# Demo asset provenance and redistribution constraints

This document records the origin of the demo assets used by Orly's v1 level
(q3dm1 — "Arena Gate"), the legal constraints that govern their use, and the
exact files that must be extracted from the demo distribution to run the level.
It exists so that future builds and GitHub Pages deploys do not accidentally
become policy violations.

## Source distribution

**Quake 3 Arena Demo v1.11**, published by id Software, Inc., December 1999.

| Platform | Canonical filename | SHA1 (installer) |
|---|---|---|
| Windows | `Q3ADemo.exe` | *(verify against archive.org copy)* |
| Linux | `linuxq3ademo-1.11-6.x86.gz.sh` | *(verify against archive.org copy)* |
| macOS | `MacQuake3Demo.bin` | *(verify against archive.org copy)* |

The Internet Archive preserves all three installers and is currently the most
reliable source:

- <https://archive.org/details/QuakeIiiArenaDemo> (Windows and macOS)
- <https://archive.org/details/Q3A-Demo> (Steam demo build, also v1.11)

Rights are retained by id Software / Bethesda Softworks (ZeniMax Media
acquired id Software in 2009).  Archive.org's distribution does not relicense
the content; the EULA below governs use regardless of where you obtain the
installer.

## Redistribution constraints

The controlling document is the **LIMITED USE SOFTWARE LICENSE AGREEMENT**
bundled with the demo installer.  The constraints that matter for this project
are:

### What is permitted

Redistribution of the **unmodified demo package in its entirety** is permitted
under Section 3 of the EULA, subject to:

- Non-commercial use only.
- Each copy must be conspicuously labeled "SHAREWARE" or "DEMO".
- The full EULA text must accompany every copy.

### What is not permitted — and why this matters for GitHub Pages

**Extracted files may not be redistributed individually.**  The EULA defines
"Software" to include "data files and screen displays" (Section 1) and
restricts copying to what Section 3 explicitly allows — copying the package as
a whole.  Extracting `.bsp`, texture, shader, or model files from `pak0.pk3`
and hosting them separately (e.g. committed to this repo and served via GitHub
Pages) does not fall within the permitted acts.

Additional relevant prohibitions:

- **Public display** — Section 2(j) prohibits publicly displaying the
  Software.  Rendering game assets in a browser session visible to the public
  is likely covered by this restriction.
- **Derivative works** — Section 2(k) prohibits derivative works.
- **Commercial use** — Section 2(f) prohibits commercial exploitation in any
  medium.

**Consequence for GitHub Pages deploys:** The demo assets must **not** be
committed to this repository or to the `docs/` build output that Pages serves.
Any build or CI step that would publish extracted asset files to Pages would
constitute redistribution of individual extracted files and/or public display,
both of which the EULA prohibits.  The public Pages deployment may still host
the HTML/CSS/JS/Rocq shell itself, but it must treat q3dm1 asset loading as a
local, user-supplied step rather than shipping a publicly playable copy of the
map.

### Approved approach for local development and CI

Users must supply their own copy of the demo distribution.  A future
`make assets` (or equivalent) target will:

1. Accept a path to the user-supplied demo installer or `pak0.pk3`.
2. Extract only the required files (see manifest below) into a
   `.gitignore`-covered local directory.
3. Serve or incorporate those files into the local build.

The extracted files must never be committed, pushed, or deployed.

In practice this means the public site can only demonstrate the shell, theory
loading, and "bring your own demo assets" flow.  Any actually playable q3dm1
session has to come from a local build fed by the user's own demo package.

## Required file manifest

All assets needed for q3dm1 live inside `demoq3/pak0.pk3` within the demo
distribution.  `.pk3` files are ZIP archives; any standard ZIP tool can
extract them.

### Map

```
maps/q3dm1.bsp         — BSP geometry, entity lump, embedded lightmaps, texture refs
maps/q3dm1.aas         — bot navigation mesh (required for entity/trigger logic)
levelshots/q3dm1.jpg   — level preview thumbnail
```

### Shader scripts

```
scripts/shaderlist.txt
scripts/base_floor.shader
scripts/base_wall.shader
scripts/base_trim.shader
scripts/base_support.shader
scripts/base_light.shader
scripts/base_object.shader
scripts/gothic_light.shader
scripts/gothic_floor.shader
scripts/gothic_wall.shader
scripts/gothic_block.shader
scripts/common.shader
scripts/liquids.shader
scripts/skies.shader
```

### Texture directories

```
textures/base_floor/
textures/base_wall/
textures/base_trim/
textures/base_support/
textures/base_light/
textures/base_object/
textures/gothic_light/
textures/gothic_floor/
textures/gothic_wall/
textures/gothic_block/
textures/skies/
textures/liquids/
textures/liquids2/     — contains q3dm1-specific liquid variants (e.g. clear_ripple1_q3dm1v)
```

### Models for map entities

```
models/mapobjects/jumppad/   — jump pad base model and textures (trigger_push entity)
models/mapobjects/           — other static map objects referenced by q3dm1 entities
```

Weapon and item pickup models (`models/weapons2/`, `models/ammo/`,
`models/powerups/`) and player models (`models/players/`) are not required for
geometry rendering or collision but are needed for a complete visual
presentation.  Include them if the build goal is a fully rendered scene.

### What the BSP embeds (does not need separate extraction)

Quake 3 BSPs embed lightmap data internally as a series of 128×128 RGB lumps
within the file itself.  There are no external lightmap files to extract.

---

*The definitive authoritative file list is the BSP's texture-reference lump.
To enumerate every texture path actually used by q3dm1, extract the .bsp and
inspect lump 1 (Textures/Shaders lump) with any Q3 BSP inspection tool.  The
manifest above is accurate for the standard demo build but should be verified
against the actual `pak0.pk3` before shipping a production extraction script.*
