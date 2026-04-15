#!/usr/bin/env python3
"""Extract q3dm1 assets from a Quake 3 Arena Demo installer or pak0.pk3.

Usage:
    python3 extract_assets.py /path/to/pak0.pk3             # pak0.pk3 directly
    python3 extract_assets.py /path/to/linuxq3ademo*.sh     # Linux installer
    python3 extract_assets.py /path/to/Q3ADemo.exe          # Windows installer
    python3 extract_assets.py [--output DIR] <source>

pak0.pk3 is a ZIP archive found inside demoq3/ in the demo distribution.
Linux .sh installers are handled natively (gzip'd tar payload).
Windows .exe installers are attempted as ZIP; if that fails, instructions
for manual extraction with 7z are printed.
macOS .bin installers require manual extraction (Stuffit/MacBinary format).

Extracted files land in docs/assets/ (gitignored) at the paths the browser
shell expects via fetch().  See ASSETS.md for the full manifest and
redistribution constraints.
"""

import argparse
import gzip
import io
import sys
import tarfile
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


# ---------------------------------------------------------------------------
# Installer-format detection and pak0.pk3 extraction
# ---------------------------------------------------------------------------


def _pak0_from_sh(installer: Path) -> zipfile.ZipFile:
    """Extract pak0.pk3 from a Linux Loki .sh installer.

    Loki installers are a shell script header followed immediately by a
    gzip-compressed tar archive.  We scan for the gzip magic bytes, decompress
    the payload, and pull demoq3/pak0.pk3 out of the resulting tar stream.
    """
    data = installer.read_bytes()
    offset = data.find(b"\x1f\x8b")
    if offset == -1:
        sys.exit(
            f"error: no gzip payload found in {installer}\n"
            "Expected the Quake 3 Arena Demo Linux installer "
            "(linuxq3ademo-1.11-6.x86.gz.sh)."
        )

    try:
        with gzip.GzipFile(fileobj=io.BytesIO(data[offset:])) as gz:
            inner = gz.read()
    except OSError as exc:
        sys.exit(
            f"error: failed to decompress payload in {installer}: {exc}\n"
            "The file may be corrupt or not the expected installer."
        )

    try:
        with tarfile.open(fileobj=io.BytesIO(inner)) as tf:
            for member in tf.getmembers():
                # Match demoq3/pak0.pk3 regardless of leading path components.
                if member.name.lower().replace("\\", "/").endswith("demoq3/pak0.pk3"):
                    fobj = tf.extractfile(member)
                    if fobj is not None:
                        print(f"Found pak0.pk3 at {member.name!r} inside {installer.name}")
                        return zipfile.ZipFile(io.BytesIO(fobj.read()))
    except tarfile.TarError as exc:
        sys.exit(
            f"error: could not read tar archive from {installer}: {exc}\n"
            "The embedded archive may be in an unexpected format."
        )

    sys.exit(
        f"error: demoq3/pak0.pk3 not found in {installer}\n"
        "Make sure this is the Quake 3 Arena Demo v1.11 Linux installer."
    )


def _pak0_from_exe(installer: Path) -> zipfile.ZipFile:
    """Try to extract pak0.pk3 from a Windows .exe installer.

    Some Windows self-extractors are ZIP-compatible.  If that works, great.
    Otherwise we bail with actionable instructions for using 7z.
    """
    if zipfile.is_zipfile(installer):
        with zipfile.ZipFile(installer) as outer:
            for name in sorted(outer.namelist()):
                if name.lower().replace("\\", "/").endswith("demoq3/pak0.pk3"):
                    print(f"Found pak0.pk3 at {name!r} inside {installer.name}")
                    return zipfile.ZipFile(io.BytesIO(outer.read(name)))

    sys.exit(
        f"error: cannot automatically unpack pak0.pk3 from {installer}\n"
        "\n"
        "The Windows installer uses a Cabinet-based format that requires\n"
        "an external tool.  Options:\n"
        "\n"
        "  On Windows — run the installer, then pass pak0.pk3 directly:\n"
        "    python3 extract_assets.py \"C:\\...\\demoq3\\pak0.pk3\"\n"
        "\n"
        "  On Linux with 7z installed:\n"
        "    7z e Q3ADemo.exe demoq3/pak0.pk3 -o/tmp/q3\n"
        "    python3 extract_assets.py /tmp/q3/pak0.pk3\n"
        "\n"
        "  Or extract pak0.pk3 by any means and pass the path directly."
    )


def _open_pak0(source: Path) -> zipfile.ZipFile:
    """Return an open ZipFile for pak0.pk3, routing through installer logic if needed."""
    suffix = source.suffix.lower()

    if suffix == ".sh":
        return _pak0_from_sh(source)

    if suffix == ".exe":
        return _pak0_from_exe(source)

    if suffix == ".bin":
        sys.exit(
            f"error: automatic extraction from macOS .bin installers is not supported.\n"
            "\n"
            "Run the installer on macOS to install the demo, then locate pak0.pk3\n"
            "(typically at <install dir>/demoq3/pak0.pk3) and pass it directly:\n"
            "    python3 extract_assets.py /path/to/demoq3/pak0.pk3"
        )

    # .pk3 or unrecognised extension — try directly as a ZIP.
    try:
        return zipfile.ZipFile(source)
    except zipfile.BadZipFile as exc:
        sys.exit(f"error: {source} is not a valid ZIP/pk3 file: {exc}")


# ---------------------------------------------------------------------------
# Core extraction and validation
# ---------------------------------------------------------------------------


def extract(source: Path, output: Path) -> None:
    if not source.is_file():
        sys.exit(f"error: file not found: {source}")

    zf = _open_pak0(source)
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
        description="Extract q3dm1 assets from a Quake 3 Arena Demo installer or pak0.pk3",
        epilog=(
            "Accepted inputs: pak0.pk3 directly, the Linux .sh installer "
            "(handled natively), or the Windows .exe installer (ZIP-compatible "
            "versions only — see error output for 7z fallback).  "
            "See ASSETS.md for redistribution constraints."
        ),
    )
    parser.add_argument(
        "source",
        type=Path,
        help="path to pak0.pk3, Q3ADemo.exe, linuxq3ademo*.sh, or MacQuake3Demo.bin",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=repo_root / "docs" / "assets",
        metavar="DIR",
        help="destination directory (default: docs/assets)",
    )
    args = parser.parse_args()
    extract(args.source, args.output)


if __name__ == "__main__":
    main()
