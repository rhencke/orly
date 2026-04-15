# Orly

A formally verified Quake 3 Arena demo level, playable in the browser.
The game logic runs in [Rocq](https://rocq-prover.org/) (formerly Coq),
interpreted live by [JsCoq](https://github.com/jscoq/jscoq) so you can
read and step through the proofs on the same page as the running game.

See [ARCHITECTURE.md](ARCHITECTURE.md) for the Rocq/JavaScript boundary and
[V1_CHECKLIST.md](V1_CHECKLIST.md) for the v1 acceptance target.

## Local development

### Prerequisites

- Python 3 (stdlib only — no pip install needed)
- Your own copy of the **Quake 3 Arena Demo v1.11** installer or `pak0.pk3`
  (see [ASSETS.md](ASSETS.md) for sources and redistribution constraints)

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

Assets are extracted to `docs/assets/` (gitignored).  The script validates
every required file against the manifest in [ASSETS.md](ASSETS.md) and
fails loudly if anything is missing.

> **Windows installer note:** `Q3ADemo.exe` uses Cabinet-based compression
> that cannot always be opened natively.  If the script reports an error,
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

Opens a local HTTP server at <http://localhost:8080>.  The game shell is at
`docs/index.html`.  Assets must be extracted first (step 1); if `docs/assets/`
is missing, `make serve` warns but still starts the server so you can work
on the shell without assets.

### Build and test (Rocq theories)

```sh
make test   # compiles theories/ with rocq compile
make clean  # removes generated .vo/.glob files
```

CI runs `make test` via Docker (see `.github/workflows/ci.yml`).  You do not
need a local Rocq install; use the published Docker image if you want to match
CI exactly.
