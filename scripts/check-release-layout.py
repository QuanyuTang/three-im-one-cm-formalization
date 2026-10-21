#!/usr/bin/env python3
"""Check the release layout alongside the official source-requirements script."""
from __future__ import annotations

from pathlib import Path
import importlib.util
import os
import re


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    errors = []
    configs = [root / name for name in ("lakefile.toml", "lakefile.lean") if (root / name).is_file()]
    if len(configs) != 1:
        errors.append("Expected exactly one root Lake configuration")
    for name in ("lean-toolchain", "lake-manifest.json", "formalization.yaml", "LICENSE",
                 "Challenge.lean", "Solution.lean", "comparator.json", "verification/Audit.lean"):
        if not (root / name).is_file():
            errors.append("Missing release file: " + name)
    licenses = [path for path in root.iterdir() if path.is_file()
                and re.fullmatch(r"(?:LICENSE|LICENCE|COPYING)(?:\.(?:txt|md))?", path.name, re.I)]
    if len(licenses) != 1 or licenses[0].name != "LICENSE":
        errors.append("Expected exactly one recognized root license file, named LICENSE")
    challenge = root / "Challenge.lean"
    if challenge.is_file():
        data = challenge.read_bytes()
        lines = data.count(b"\n") + int(bool(data) and not data.endswith(b"\n"))
        if len(data) > 100 * 1024 or lines > 1000:
            errors.append("Challenge exceeds 100 KiB or 1,000 physical lines")
    size = 0
    for directory, subdirs, files in os.walk(root, followlinks=False):
        for name in subdirs:
            if (Path(directory) / name).is_symlink():
                errors.append("Release symlink directory requires review: " +
                              str((Path(directory) / name).relative_to(root)))
        subdirs[:] = [name for name in subdirs if name not in {".git", ".lake", ".ci-output"}
                     and not (Path(directory) / name).is_symlink()]
        for name in files:
            path = Path(directory) / name
            if path.is_symlink():
                errors.append("Release symlink requires explicit review: " + str(path.relative_to(root)))
                continue
            size += path.stat().st_size
            if path.suffix.lower() == ".tex":
                errors.append("Original TeX is excluded from this release: " + str(path.relative_to(root)))
    if size > 500 * 1024 * 1024:
        errors.append("Source checkout exceeds 500 MiB")
    try:
        spec = importlib.util.spec_from_file_location("release_topology", root / "scripts/build-topological.py")
        planner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(planner)
        planner.check_registration(root, planner.discover(root))
    except (OSError, UnicodeError, ValueError) as error:
        errors.append("Local module registration: " + str(error))
    for error in errors:
        print(error)
    if not errors:
        print("Draft local release-layout checks passed; full Palomar verification is still required")
    return int(bool(errors))


if __name__ == "__main__":
    raise SystemExit(main())
