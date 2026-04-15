#!/usr/bin/env python3
"""Extract q3dm1 assets from a Quake 3 Arena Demo pak0.pk3 file.

Usage:
    python3 extract_assets.py /path/to/pak0.pk3 [--output docs/assets]

pak0.pk3 is a ZIP archive found inside demoq3/ in the demo distribution.
Extracted files land in docs/assets/ (gitignored) at the paths the browser
shell expects via fetch().  See ASSETS.md for the full manifest and
redistribution constraints.
"""

import argparse
import sys
import zipfile
from pathlib import Path

# ---------------------------------------------------------------------------
# Manifest — what must be present for a complete q3dm1 local build.
# Keep this in sync with ASSETS.md.
# ---------------------------------------------------------------------------

# Individual files that must exist after extraction.
REQUIRED_FILES = [
    "maps/q3dm1.bsp",
    "maps/q3dm1.aas",
    "levelshots/q3dm1.jpg",
    "scripts/shaderlist.txt",
    "scripts/base_floor.shader",
    "scripts/base_wall.shader",
    "scripts/base_trim.shader",
    "scripts/base_support.shader",
    "scripts/base_light.shader",
    "scripts/base_object.shader",
    "scripts/gothic_light.shader",
    "scripts/gothic_floor.shader",
    "scripts/gothic_wall.shader",
    "scripts/gothic_block.shader",
    "scripts/common.shader",
    "scripts/liquids.shader",
    "scripts/skies.shader",
]

# Directory prefixes — every file under each prefix is extracted, and at
# least one file per prefix must be present or validation fails.
REQUIRED_PREFIXES = [
    "textures/base_floor/",
    "textures/base_wall/",
    "textures/base_trim/",
    "textures/base_support/",
    "textures/base_light/",
    "textures/base_object/",
    "textures/gothic_light/",
    "textures/gothic_floor/",
    "textures/gothic_wall/",
    "textures/gothic_block/",
    "textures/skies/",
    "textures/liquids/",
    "textures/liquids2/",
    "models/mapobjects/",
]


def _wanted(name: str) -> bool:
    """Return True if this zip entry should be extracted."""
    low = name.lower()
    if low in {f.lower() for f in REQUIRED_FILES}:
        return True
    return any(low.startswith(p.lower()) for p in REQUIRED_PREFIXES)


def _safe_dest(output: Path, zip_name: str) -> Path:
    """Resolve destination and reject path-traversal attempts."""
    dest = (output / zip_name).resolve()
    if not dest.is_relative_to(output.resolve()):
        sys.exit(f"error: zip entry escapes output directory: {zip_name!r}")
    return dest


def extract(pak0: Path, output: Path) -> None:
    if not pak0.is_file():
        sys.exit(f"error: file not found: {pak0}")

    try:
        zf = zipfile.ZipFile(pak0)
    except zipfile.BadZipFile as exc:
        sys.exit(f"error: {pak0} is not a valid ZIP/pk3 file: {exc}")

    with zf:
        # Sort entries for deterministic extraction order.
        all_names = sorted(zf.namelist())
        to_extract = [n for n in all_names if not n.endswith("/") and _wanted(n)]

        if not to_extract:
            sys.exit(
                "error: no matching assets found — "
                "is this the Quake 3 Arena Demo v1.11 pak0.pk3?"
            )

        print(f"Extracting {len(to_extract)} files to {output}/")
        output.mkdir(parents=True, exist_ok=True)

        for name in to_extract:
            dest = _safe_dest(output, name)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(zf.read(name))

    _validate(output, len(to_extract))


def _validate(output: Path, extracted_count: int) -> None:
    """Check the manifest; exit with a clear message on any gap."""
    missing: list[str] = []

    for req in REQUIRED_FILES:
        if not (output / req).is_file():
            missing.append(req)

    for prefix in REQUIRED_PREFIXES:
        prefix_dir = output / prefix
        if not prefix_dir.is_dir() or not any(
            f for f in prefix_dir.rglob("*") if f.is_file()
        ):
            missing.append(f"{prefix}  (no files found under this directory)")

    if missing:
        print(
            "error: the following required assets are missing from pak0.pk3:",
            file=sys.stderr,
        )
        for m in missing:
            print(f"  {m}", file=sys.stderr)
        sys.exit(
            "\nThe pak0.pk3 may be from the wrong demo version or corrupt.\n"
            "Expected: Quake 3 Arena Demo v1.11 (demoq3/pak0.pk3 inside the installer)."
        )

    print(f"Done — {extracted_count} files extracted and manifest validated.")


def main() -> None:
    repo_root = Path(__file__).parent
    parser = argparse.ArgumentParser(
        description="Extract q3dm1 assets from the Quake 3 Arena Demo pak0.pk3",
        epilog=(
            "pak0.pk3 lives inside demoq3/ in the demo installer.  "
            "See ASSETS.md for redistribution constraints."
        ),
    )
    parser.add_argument("pak0", type=Path, help="path to pak0.pk3")
    parser.add_argument(
        "--output",
        type=Path,
        default=repo_root / "docs" / "assets",
        metavar="DIR",
        help="destination directory (default: docs/assets)",
    )
    args = parser.parse_args()
    extract(args.pak0, args.output)


if __name__ == "__main__":
    main()
