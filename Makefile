.PHONY: build test clean serve assets stage-pages-map rocq-build ocaml-build validate-build validate browser-theories jscoq-runtime

# Path to the Q3 Arena Demo installer or pak0.pk3.
# Set on the command line: make assets DEMO=/path/to/Q3ADemo.exe
DEMO ?=

EXTRACT_BIN = _build/default/extract_assets/main.exe

THEORIES := \
  theories/ExtractAssets.v \
  theories/BspBinary.v \
  theories/BspFormat.v \
  theories/BspPlaneVertex.v \
  theories/BspNodeLeaf.v \
  theories/BspTexture.v \
  theories/BspBrush.v \
  theories/BspFace.v \
  theories/BspLightmapVisEffect.v \
  theories/BspEntity.v \
  theories/BspFile.v \
  theories/BspPatch.v \
  theories/BspProofs.v \
  theories/GameState.v \
  theories/ExtractBsp.v

# ── Browser theory bundle ──────────────────────────────────────────────
# Generates docs/theories/BspCore.v: a flat, self-contained Rocq source
# file served to the JsCoq IDE panel in the browser.  It is the
# concatenation of the three game-core theories in dependency order
# (BspBinary → BspEntity → GameState) with cross-file
# "From Bsp Require Import" lines stripped (their content is inlined),
# and "From Stdlib Require Import" rewritten to plain "Require Import"
# so the bundled theory still loads under JsCoq's older stdlib layout.
# JsCoq 0.17.1 runs Rocq 8.17.1 and cannot load pre-compiled .vo
# packages built with our system Rocq 9.x; this flat-file approach
# lets JsCoq compile the theories on the fly using only the stdlib.
#
# Proofs (Lemma/Theorem blocks) are included in the bundle so users can
# examine proof terms in the JsCoq IDE while they play.
#
# One Rocq 9.x → 8.17 compatibility fix is applied: `length_map` was
# introduced as the canonical name in Rocq 8.20; JsCoq's older stdlib
# only has `map_length` (deprecated in 9.x).  The sed pass below
# rewrites every `apply length_map` and `rewrite length_map` occurrence
# to the 8.17-compatible form so the full proof bundle compiles cleanly
# under JsCoq.
DOCS_THEORIES_DIR = docs/theories
BSP_CORE_SRCS     = theories/BspBinary.v theories/BspEntity.v theories/GameState.v
BSP_CORE_V        = $(DOCS_THEORIES_DIR)/BspCore.v
JSCOQ_VENDOR_DIR  = docs/vendor/jscoq
ASSETS_DIR        = docs/assets
PAGES_MAP_SRC     = docs/vendor/maps/openarena/am_lavaarena.bsp
PAGES_MAP_PATH    = maps/am_lavaarena.bsp
PAGES_MAP_DEST    = $(ASSETS_DIR)/$(PAGES_MAP_PATH)
PAGES_MANIFEST    = $(ASSETS_DIR)/manifest.json

$(BSP_CORE_V): $(BSP_CORE_SRCS)
	mkdir -p $(DOCS_THEORIES_DIR)
	{ cat $(BSP_CORE_SRCS); } \
	  | sed -E '/^From Bsp Require Import /d; s/^From Stdlib Require Import ([^.]+)\.$$/Require Import \1./; s/\bapply length_map\b/apply map_length/g; s/\brewrite length_map\b/rewrite map_length/g' \
	  > $@

browser-theories: $(BSP_CORE_V)

jscoq-runtime: package.json package-lock.json scripts/vendor-jscoq.mjs
	@test -d node_modules/jscoq || { \
	  printf 'error: node_modules/jscoq not found.\n'; \
	  printf 'Run: npm ci\n'; \
	  exit 1; \
	}
	npm run --silent vendor:jscoq

rocq-build:
	$(foreach v,$(THEORIES),rocq compile -Q theories Bsp $(v) &&) true

validate-build: rocq-build
	dune build validate_bsp/main.exe

validate: validate-build
	dune exec validate_bsp/main.exe

ocaml-build: rocq-build
	dune build extract_assets/main.exe

build: rocq-build validate-build browser-theories

test: build validate

clean:
	rm -f theories/*.vo theories/*.vok theories/*.vos theories/*.glob theories/.*.aux
	rm -f extract_assets/extract_assets_core.ml extract_assets/extract_assets_core.mli
	rm -f validate_bsp/bsp_core.ml validate_bsp/bsp_core.mli
	rm -f $(BSP_CORE_V)
	rm -rf $(JSCOQ_VENDOR_DIR)
	dune clean

assets: ocaml-build
	@test -n "$(DEMO)" || { \
	  printf 'error: DEMO is not set.\n'; \
	  printf 'Usage: make assets DEMO=/path/to/installer-or-pak0.pk3\n'; \
	  printf '\n'; \
	  printf 'DEMO can be:\n'; \
	  printf '  The Linux installer:   linuxq3ademo-1.11-6.x86.gz.sh\n'; \
	  printf '  The Windows installer: Q3ADemo.exe\n'; \
	  printf '  A bare pak0.pk3:       demoq3/pak0.pk3\n'; \
	  printf '\nSee README.md and ASSETS.md for details.\n'; \
	  exit 1; \
	}
	$(EXTRACT_BIN) --output $(ASSETS_DIR) "$(DEMO)"

# Stage the GPL-licensed OpenArena BSP that GitHub Pages is allowed to ship.
stage-pages-map:
	mkdir -p "$(dir $(PAGES_MAP_DEST))"
	cp "$(PAGES_MAP_SRC)" "$(PAGES_MAP_DEST)"
	printf '[\n  "%s"\n]\n' "$(PAGES_MAP_PATH)" > "$(PAGES_MANIFEST)"

serve: jscoq-runtime
	@test -d docs/assets || { \
	  printf 'warning: docs/assets/ not found — game assets will not load.\n'; \
	  printf 'Run: make assets DEMO=/path/to/installer-or-pak0.pk3\n'; \
	  printf 'See README.md for details.\n'; \
	}
	python3 -m http.server 8080 --directory docs
