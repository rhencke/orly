.PHONY: build test clean serve assets rocq-build ocaml-build validate-build validate browser-theories jscoq-runtime

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
# "From Bsp Require Import" lines stripped (their content is inlined).
# JsCoq 0.17.1 runs Rocq 8.17.1 and cannot load pre-compiled .vo
# packages built with our system Rocq 9.x; this flat-file approach
# lets JsCoq compile the theories on the fly using only the stdlib.
DOCS_THEORIES_DIR = docs/theories
BSP_CORE_SRCS     = theories/BspBinary.v theories/BspEntity.v theories/GameState.v
BSP_CORE_V        = $(DOCS_THEORIES_DIR)/BspCore.v
JSCOQ_VENDOR_DIR  = docs/vendor/jscoq

$(BSP_CORE_V): $(BSP_CORE_SRCS)
	mkdir -p $(DOCS_THEORIES_DIR)
	{ cat $(BSP_CORE_SRCS); } \
	  | grep -v '^From Bsp Require Import' > $@

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
	$(EXTRACT_BIN) --output docs/assets "$(DEMO)"

serve: jscoq-runtime
	@test -d docs/assets || { \
	  printf 'warning: docs/assets/ not found — game assets will not load.\n'; \
	  printf 'Run: make assets DEMO=/path/to/installer-or-pak0.pk3\n'; \
	  printf 'See README.md for details.\n'; \
	}
	python3 -m http.server 8080 --directory docs
