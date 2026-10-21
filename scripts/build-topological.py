#!/usr/bin/env python3
"""Build root-layout local modules sequentially, with real Lake deps gates.

The default only writes a source/topology plan; --execute is explicit. One
upstream gate uses --rehash; each later local `lake --no-build build +M:deps`
must pass, retaining Lake's real dependency-hash checks without rehashing every
artifact for every target. Resolved dependency pins, clean tracked files, and
tracked-content fingerprints are checked before and after the build.
This checks Lake's actual import/plugin/native-library dependencies and traces;
existence of .olean files alone is never used as a freshness claim. If the gate
fails, stop. Never fall back to an unrestricted build of stale dependencies.

There is no claim that this controls all upstream or Comparator concurrency.
The root package must use the standard root-relative Lean source layout.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import tomllib

MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*\Z")
IMPORT = re.compile(r"(?:(?:public|private|meta)\s+)*import\s+(.*)\Z")
EXCLUDED = {".git", ".lake", ".ci-output", "__pycache__"}
CONFIG_NAMES = {"lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json", "comparator.json"}
TOOLCHAIN_ROOTS = {"Init", "Lean", "Std", "Lake"}


def mask_comments_strings(text: str) -> str:
    """Keep line locations; ignore nested comments and ordinary string literals."""
    out = list(text)
    index, depth = 0, 0
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                out[index:index + 2] = "  "
                depth += 1
                index += 2
            elif text.startswith("-/", index):
                out[index:index + 2] = "  "
                depth -= 1
                index += 2
            else:
                if text[index] != "\n":
                    out[index] = " "
                index += 1
        elif text.startswith("/-", index):
            out[index:index + 2] = "  "
            depth = 1
            index += 2
        elif text.startswith("--", index):
            end = text.find("\n", index)
            if end < 0:
                end = len(text)
            out[index:end] = " " * (end - index)
            index = end
        elif text[index] == '"':
            out[index] = " "
            index += 1
            while index < len(text):
                char = text[index]
                if char != "\n":
                    out[index] = " "
                index += 1
                if char == "\\" and index < len(text):
                    if text[index] != "\n":
                        out[index] = " "
                    index += 1
                elif char == '"':
                    break
            else:
                raise ValueError("Unterminated string")
        else:
            index += 1
    if depth:
        raise ValueError("Unterminated block comment")
    return "".join(out)


def imports(text: str) -> list[str]:
    found = []
    for line in mask_comments_strings(text).splitlines():
        line = line.strip()
        if not line or line in {"module", "prelude"}:
            continue
        match = IMPORT.fullmatch(line)
        if match:
            names = match[1].split()
            if names and names[0] == "all":
                names = names[1:]
            if not names or any(not MODULE_NAME.fullmatch(name) for name in names):
                raise ValueError("Unsupported import header: " + line)
            found.extend(names)
        elif re.match(r"(?:(?:public|private|meta)\s+)*import(?:\s|$)", line):
            raise ValueError("Unsupported import header: " + line)
        else:
            break  # Imports are header commands, never proof-body text.
    return list(dict.fromkeys(found))


def discover(root: Path) -> dict[str, dict]:
    modules = {}
    for directory, subdirs, files in os.walk(root, followlinks=False):
        subdirs[:] = sorted(name for name in subdirs
                           if name not in EXCLUDED and not (Path(directory) / name).is_symlink())
        for name in sorted(files):
            path = Path(directory) / name
            if not name.endswith(".lean") or path == root / "lakefile.lean":
                continue
            if path.is_symlink():
                raise ValueError(f"Lean symlink rejected: {path.relative_to(root)}")
            relative = path.relative_to(root)
            module = ".".join(relative.with_suffix("").parts)
            if not MODULE_NAME.fullmatch(module):
                raise ValueError(f"Unsupported source module path: {relative}")
            data = path.read_bytes()
            modules[module] = {
                "path": relative.as_posix(), "sha256": sha256(data).hexdigest(),
                "imports": imports(data.decode("utf-8")),
            }
    if not modules:
        raise ValueError("No local Lean modules found")
    return modules


def topological_order(modules: dict[str, dict]) -> list[str]:
    ordered, visiting, done = [], set(), set()

    def visit(name):
        if name in done:
            return
        if name in visiting:
            raise ValueError("Local import cycle at " + name)
        visiting.add(name)
        for dependency in sorted(modules[name]["imports"]):
            if dependency in modules:
                visit(dependency)
            elif any(dependency.split(".")[0] == local.split(".")[0] for local in modules):
                raise ValueError(f"Missing local import {dependency} in {name}")
        visiting.remove(name)
        done.add(name)
        ordered.append(name)

    for name in sorted(modules):
        visit(name)
    return ordered


def fingerprint(root: Path, modules: dict[str, dict]) -> dict:
    result = {info["path"]: info["sha256"] for info in modules.values()}
    for name in sorted(CONFIG_NAMES):
        path = root / name
        if path.exists():
            result[name] = sha256(path.read_bytes()).hexdigest()
    return dict(sorted(result.items()))


def check_registration(root: Path, modules: dict[str, dict]) -> dict[str, str]:
    """Check the supported root-layout TOML library semantics, without Lake."""
    config = root / "lakefile.toml"
    if not config.is_file() or (root / "lakefile.lean").exists():
        raise ValueError("This draft requires exactly one lakefile.toml; dynamic configurations need a separate reviewed planner")
    data = tomllib.loads(config.read_text(encoding="utf-8"))
    if data.get("srcDir", ".") != ".":
        raise ValueError("This draft does not infer a custom package srcDir")
    libraries = data.get("lean_lib", [])
    if not libraries:
        raise ValueError("No registered Lean libraries")

    def matches(module, glob):
        if glob.endswith(".*"):
            prefix = glob[:-2]
            return module == prefix or module.startswith(prefix + ".")
        if glob.endswith(".+"):
            return module.startswith(glob[:-2] + ".")
        return module == glob

    registered = {}
    for library in libraries:
        if library.get("srcDir", ".") != ".":
            raise ValueError("This draft does not infer a custom library srcDir")
        name = library["name"]
        roots = library.get("roots", [name])
        globs = library.get("globs", roots)
        for glob in globs:
            if not isinstance(glob, str) or not MODULE_NAME.fullmatch(glob.removesuffix(".*").removesuffix(".+")):
                raise ValueError("Unsupported library glob")
        for module in modules:
            # Lake.LeanLibConfig.isBuildableModule: a matching glob, or a
            # root prefix for which that root itself matches some glob.
            buildable = (any(matches(module, glob) for glob in globs)
                         or any((module == base or module.startswith(base + "."))
                                and any(matches(base, glob) for glob in globs) for base in roots))
            if buildable:
                if module in registered and registered[module] != name:
                    raise ValueError("Ambiguous local library ownership for " + module)
                registered[module] = name
    missing = sorted(set(modules) - set(registered))
    if missing:
        raise ValueError("Local modules not registered in a buildable Lean library: " + ", ".join(missing))
    return registered


def strong_dependency_targets(modules: dict[str, dict]) -> list[str]:
    """One combined gate for direct nonlocal workspace import roots."""
    external = {name for info in modules.values() for name in info["imports"]
                if name not in modules and name.split(".")[0] not in TOOLCHAIN_ROOTS}
    # If Mathlib itself is imported, separate Mathlib.* requests add no coverage.
    # All roots remain in ONE Lake invocation, sharing its job graph.
    minimal = [name for name in sorted(external)
               if not any(name.startswith(parent + ".") for parent in external)]
    return [f"+{name}:leanArts" for name in minimal]


def dependency_inspector():
    path = Path(__file__).with_name("verify-pins.py")
    spec = importlib.util.spec_from_file_location("ci_dependency_pins", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.inspect_dependencies


def build(plan: dict, root: Path, run=subprocess.run, records: list | None = None) -> list[dict]:
    records = [] if records is None else records

    def command(argv):
        print("+ " + " ".join(argv), flush=True)
        completed = run(argv, cwd=root, check=False)
        records.append({"argv": argv, "exitCode": completed.returncode})
        if completed.returncode:
            raise subprocess.CalledProcessError(completed.returncode, argv)

    if plan.get("strongDependencyTargets"):
        command(["lake", "--rehash", "--no-build", "build", *plan["strongDependencyTargets"]])
    for module in plan["order"]:
        # :deps is a real buildable facet in the checked 4.35 source. The
        # non-buildable :presetup facet must not be used as a CLI target.
        command(["lake", "--no-build", "build", f"+{module}:deps"])
        command(["lake", "--fail-fast", "build", f"+{module}:leanArts"])
        command(["lake", "--no-build", "build", f"+{module}:leanArts"])
    # Covers any configured default target we failed to account for. It may
    # refuse a default native target; adapt the final plan, never bulk-fallback.
    command(["lake", "--no-build", "build"])
    return records


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--report", type=Path, default=Path(".ci-output/build.json"))
    parser.add_argument("--execute", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    report_path = args.report if args.report.is_absolute() else root / args.report
    report_path.parent.mkdir(parents=True, exist_ok=True)
    result = {"recordedUTC": datetime.now(timezone.utc).isoformat(),
              "executed": args.execute, "status": "PLAN ONLY; not a build result"}
    exit_code = 0
    try:
        modules = discover(root)
        result.update({"modules": modules, "order": topological_order(modules),
                       "registeredLibraries": check_registration(root, modules),
                       "strongDependencyTargets": strong_dependency_targets(modules),
                       "freshnessPolicy": "One combined upstream --rehash/no-build gate; real ordinary no-build gate for every local target; no --old; source/config and clean pinned dependency contents checked before/after"})
        before = fingerprint(root, modules)
        result["inputsBefore"] = before
        if args.execute:
            inspect_dependencies = dependency_inspector()
            result["dependenciesBefore"] = inspect_dependencies(root)
            result["commands"] = []
            build(result, root, records=result["commands"])
            after = fingerprint(root, discover(root))
            result["inputsAfter"] = after
            if before != after:
                raise ValueError("Source or configuration changed during the build")
            result["dependenciesAfter"] = inspect_dependencies(root)
            if result["dependenciesBefore"] != result["dependenciesAfter"]:
                raise ValueError("Dependency revision, toolchain, or tracked contents changed during the build")
            result["status"] = "Actual sequential local-target build and freshness gates passed"
    except (OSError, UnicodeError, ValueError, subprocess.CalledProcessError) as error:
        result["status"] = "FAILED"
        result["error"] = str(error)
        if isinstance(error, subprocess.CalledProcessError):
            result["failedCommand"] = error.cmd
            result["failedExitCode"] = error.returncode
        exit_code = 1
    report_path.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"{result['status']}: {len(result.get('order', []))} local modules; {report_path}")
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
