.PHONY: build test clean serve assets rocq-build ocaml-build validate-build validate

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
  theories/BspProofs.v \
  theories/GameState.v \
  theories/ExtractBsp.v

rocq-build:
	$(foreach v,$(THEORIES),rocq compile -Q theories Bsp $(v) &&) true

validate-build: rocq-build
	dune build validate_bsp/main.exe

validate: validate-build
	dune exec validate_bsp/main.exe

ocaml-build: rocq-build
	dune build extract_assets/main.exe

build: rocq-build validate-build

test: build validate

clean:
	rm -f theories/*.vo theories/*.vok theories/*.vos theories/*.glob theories/.*.aux
	rm -f extract_assets/extract_assets_core.ml extract_assets/extract_assets_core.mli
	rm -f validate_bsp/bsp_core.ml validate_bsp/bsp_core.mli
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

serve:
	@test -d docs/assets || { \
	  printf 'warning: docs/assets/ not found — game assets will not load.\n'; \
	  printf 'Run: make assets DEMO=/path/to/installer-or-pak0.pk3\n'; \
	  printf 'See README.md for details.\n'; \
	}
	python3 -m http.server 8080 --directory docs
