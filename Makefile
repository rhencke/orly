.PHONY: build test clean serve assets rocq-build ocaml-build

# Path to the Q3 Arena Demo installer or pak0.pk3.
# Set on the command line: make assets DEMO=/path/to/Q3ADemo.exe
DEMO ?=

EXTRACT_BIN = _build/default/extract_assets/main.exe

rocq-build:
	rocq compile -Q theories Hello theories/Hello.v
	rocq compile -Q theories Hello theories/ExtractAssets.v
	rocq compile -Q theories Hello theories/BspBinary.v

ocaml-build: rocq-build
	dune build extract_assets/main.exe

build: rocq-build ocaml-build

test: build

clean:
	rm -f theories/*.vo theories/*.vok theories/*.vos theories/*.glob theories/.*.aux
	rm -f extract_assets/extract_assets_core.ml extract_assets/extract_assets_core.mli
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
