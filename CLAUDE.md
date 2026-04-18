# orly

Quake 3 BSP viewer with formally verified parsing and game logic, built
in Rocq and rendered via JsCoq in the browser.

## Build and test

```bash
make test          # compile all Rocq theories + OCaml extraction
make clean         # remove build artifacts
make serve         # local dev server on :8080
```

`make test` is the gate — nothing merges unless it passes.

### Playwright browser validation

For changes that touch browser-side code (`docs/*.js`, `docs/index.html`,
layout, UI behaviour, rendering), also run the Playwright suite:

```bash
npm run test:browser   # full local browser scenario suite
```

This spins up a headless Chromium instance and exercises: no-assets load,
desktop render startup (lower-panel chrome, section switcher, keyboard
resize), mobile portrait/landscape render startup (touch targets, safe-area
padding, lower-panel usability), BSP parse → Rocq handoff, error overlay
copy flow, and Rocq sync timeout overlay. Screenshots land in `/tmp` on
failure for inspection.

Prerequisites (one-time):
```bash
npm ci                        # install node_modules
npm run playwright:install    # download Chromium browser binary
```

Run the suite whenever you modify `docs/`, `scripts/`, or browser-facing
logic. It is not wired into `make test` (needs a browser binary) but should
pass before any PR touches the browser layer.

## Proof strategy

Proofs are first-class output, not an afterthought. Every parsed type
should carry mechanically verified properties:

- **Per-parser round-trip**: `parse ∘ serialize = id` (or at minimum
  the parse direction).
- **Structural invariants**: node child indices in bounds, leaf brush
  ranges non-overlapping, plane normals non-zero — whatever is
  mechanically provable from the parsed structure.
- **Cross-lump consistency**: brush-side plane indices reference valid
  planes, texture indices in range, etc.

Treat each proof as a **theory**. Prove what you can, then adjust when
a counterexample (real data, spec correction, new lump interaction)
invalidates the claim. The theories are the shining star — they evolve
with the codebase rather than being gold-plated upfront.

## Project layout

| Path | Purpose |
|------|---------|
| `theories/` | Rocq source files (`.v`) — BSP types, parsers, proofs |
| `extract_assets/` | OCaml extraction target for asset pipeline |
| `docs/` | GitHub Pages shell (JsCoq + WebGL) |
| `_RocqProject` | Rocq project file — lists all `.v` sources |
| `Makefile` | Build orchestration |
| `ARCHITECTURE.md` | Rocq-vs-JS boundary decisions |
| `V1_CHECKLIST.md` | v1 acceptance criteria |
