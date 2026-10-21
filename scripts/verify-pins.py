#!/usr/bin/env python3
"""Inspect pinned, clean dependencies and fingerprint their tracked contents.

The topological builder calls inspect_dependencies before and after execution.
Only Git-tracked dependency contents are fingerprinted here; cached build outputs
are checked by Lake's real trace gates. Nothing is assumed current from a mere
file's existence. This script does not execute Lean, Lake, or any proof check.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess


def release_key(value: str) -> tuple[int, int, int, int, int]:
    match = re.fullmatch(r"(?:leanprover/lean4:)?v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?", value)
    if not match:
        raise ValueError("Expected a fixed Lean release or release candidate")
    major, minor, patch = (int(match[index]) for index in (1, 2, 3))
    return major, minor, patch, int(match[4] is None), int(match[4] or 0)


def inspect_dependencies(root: Path) -> dict:
    toolchain = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    # Recheck the current Palomar policy when updating this minimum. This is
    # the minimum in the primary Palomar toolchains.json audited for this pin.
    if release_key(toolchain) < release_key("v4.35.0-rc2"):
        raise ValueError("Lean is below the audited Palomar minimum")
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = manifest["packages"]
    if sum(item["name"].lower() == "mathlib" for item in packages) != 1:
        raise ValueError("Expected exactly one resolved Mathlib package")
    packages_dir = Path(manifest.get("packagesDir", ".lake/packages"))
    if packages_dir.is_absolute() or ".." in packages_dir.parts:
        raise ValueError("Expected a repository-relative packagesDir")
    inspected = {}
    for package in packages:
        name = package["name"]
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9-]*", name):
            raise ValueError("Unsupported dependency directory name")
        revision = package.get("rev", "")
        if package.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", revision):
            raise ValueError("Every external dependency needs a full fixed Git revision: " + name)
        dependency = root / packages_dir / name
        actual = subprocess.check_output(["git", "-C", str(dependency), "rev-parse", "HEAD"], text=True).strip()
        if actual != revision:
            raise ValueError("Installed dependency does not match the manifest: " + name)
        status = subprocess.check_output(
            ["git", "-C", str(dependency), "status", "--porcelain=v1", "--untracked-files=normal"],
            text=True,
        ).strip()
        if status:
            raise ValueError("Dependency checkout is not clean: " + name)
        tracked = subprocess.check_output(["git", "-C", str(dependency), "ls-files", "-z"])
        content = {}
        for entry in tracked.split(b"\0"):
            if not entry:
                continue
            relative = Path(os.fsdecode(entry))
            path = dependency / relative
            if relative.is_absolute() or ".." in relative.parts or path.is_symlink():
                raise ValueError("Unsupported tracked dependency path: " + name)
            content[relative.as_posix()] = sha256(path.read_bytes()).hexdigest()
        inspected[name] = {"revision": actual, "clean": True,
                           "trackedFileCount": len(content),
                           "trackedContentSHA256": sha256(json.dumps(content, sort_keys=True).encode()).hexdigest()}
        if name.lower() == "mathlib":
            subdir = Path(package.get("subDir") or ".")
            if subdir.is_absolute() or ".." in subdir.parts:
                raise ValueError("Unsupported Mathlib subDir")
            dependency_toolchain = (dependency / subdir / "lean-toolchain").read_text(encoding="utf-8").strip()
            if toolchain != dependency_toolchain:
                raise ValueError("The root and actual Mathlib toolchains differ")
    return {"toolchain": toolchain,
            "manifestSHA256": sha256((root / "lake-manifest.json").read_bytes()).hexdigest(),
            "packages": dict(sorted(inspected.items()))}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    result = inspect_dependencies(args.root.resolve())
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"toolchain": result["toolchain"], "packageCount": len(result["packages"]),
                      "status": "Pinned clean dependencies fingerprinted; not a proof audit"}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
