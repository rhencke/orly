# Orly

A formally verified Quake 3 Arena demo level, playable in the browser.
The game logic runs in [Rocq](https://rocq-prover.org/) (formerly Coq),
interpreted live by [JsCoq](https://github.com/jscoq/jscoq) so you can
read and step through the proofs on the same page as the running game.

See [ARCHITECTURE.md](ARCHITECTURE.md) for the Rocq/JavaScript boundary and
[V1_CHECKLIST.md](V1_CHECKLIST.md) for the v1 acceptance target.

## Local development

### Prerequisites

- **Rocq + OCaml** via [opam](https://opam.ocaml.org/): `opam install rocq-prover decompress`
  (OCaml 5.3 recommended; matches the CI image)
- **Node.js + npm** for the browser runtime: `npm ci`
- Your own copy of the **Quake 3 Arena Demo v1.11** installer or `pak0.pk3`
  (see [ASSETS.md](ASSETS.md) for sources and redistribution constraints)

> **Tip:** To match CI exactly without a local opam setup, run everything
> inside Docker:
> ```sh
> docker build -t orly .
> docker run --rm -v "$PWD:/src" orly sh -c \
>   "cp -r /src /tmp/work && cd /tmp/work && opam exec -- make assets DEMO=/src/pak0.pk3"
> ```

### 1. Extract game assets

Run `make assets`, pointing `DEMO` at your installer or at a bare `pak0.pk3`:

```sh
# Linux installer (handled natively — no external tools needed)
make assets DEMO=/path/to/linuxq3ademo-1.11-6.x86.gz.sh

# Windows installer (works if the .exe is ZIP-compatible; see note below)
make assets DEMO=/path/to/Q3ADemo.exe

# Or a bare pak0.pk3 extracted by any means
make assets DEMO=/path/to/demoq3/pak0.pk3
```

This builds the `extract-assets` binary first (Rocq → OCaml → native), then
runs it.  Assets are extracted to `docs/assets/` (gitignored).  The extractor
validates every required file against the manifest in [ASSETS.md](ASSETS.md)
and fails loudly if anything is missing.

> **Windows installer note:** `Q3ADemo.exe` uses Cabinet-based compression
> that cannot always be opened natively.  If the extractor reports an error,
> extract `pak0.pk3` first with 7-Zip:
> ```sh
> 7z e Q3ADemo.exe demoq3/pak0.pk3 -o/tmp/q3
> make assets DEMO=/tmp/q3/pak0.pk3
> ```

> **macOS installer note:** `MacQuake3Demo.bin` uses a Stuffit-based format
> that requires platform-specific tools.  Run the installer on macOS, locate
> `demoq3/pak0.pk3` in the installed directory, then pass it directly.

### 2. Serve locally

```sh
make serve
```

Opens a local HTTP server at <http://localhost:8080> (requires Python 3 for the
dev server).  On each run, `make serve` refreshes `docs/vendor/jscoq/` from the
locked npm dependency tree so the browser shell uses a reproducible JsCoq
runtime without committing the generated files.  The game shell is at
`docs/index.html`.  Assets must be extracted first (step 1); if `docs/assets/`
is missing, `make serve` warns but still starts the server so you can work on
the shell without assets.

### Browser regression smoke test

To run the Playwright regression coverage for browser load and q3dm1 render
startup:

```sh
npm ci
npm run playwright:install
npm run test:q3dm1-browser
```

The smoke test runs two scenarios against the local browser build:

1. the assetless page load path, to ensure the JsCoq worker bootstrap still
   succeeds without tripping over browser security restrictions
2. a stubbed `maps/q3dm1.bsp` startup path, to ensure the Rocq-seeded render
   pipeline reaches its first frame and hides the placeholder

It writes screenshots plus JSON diagnostics under your system temp directory.

### Build and test

```sh
make test   # compiles Rocq theories, extracts OCaml, builds extract-assets binary
make clean  # removes .vo/.glob files and the dune build directory
```

`make test` runs the full pipeline:

1. **`rocq-build`** — compiles all Rocq theories under `theories/`,
   running all proofs and emitting `extract_assets/extract_assets_core.{ml,mli}`
   via Rocq's `Extraction` command.
2. **`ocaml-build`** — builds the extracted module and the I/O driver
   (`extract_assets/main.ml`) into the `extract-assets` native binary via dune.

CI runs `make test` inside Docker (see `.github/workflows/ci.yml`).  The
Dockerfile installs Rocq, OCaml 5.3, and the `decompress` library — no C
dependencies required.
