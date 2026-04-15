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
