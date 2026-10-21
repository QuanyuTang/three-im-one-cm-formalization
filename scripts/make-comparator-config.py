#!/usr/bin/env python3
"""Validate the submitted config and write a temporary bundled-kernel config.

Based on PalomarTemplate 2891de4c48955af824969a263d31b25e7a9a1406.
This script prepares configuration; it does not execute the Comparator.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

PERMITTED = {"propext", "Quot.sound", "Classical.choice"}
THEOREM = "ThreeIMOneCM.three_IM_one_CM"
ALLOWED_KEYS = {
    "challenge_module", "solution_module", "theorem_names",
    "definition_names", "permitted_axioms", "enable_nanoda",
}


def prepare(config: object, prefix: Path) -> dict:
    if not isinstance(config, dict):
        raise ValueError("Comparator configuration must be one JSON object")
    unknown = set(config) - ALLOWED_KEYS
    if unknown:
        raise ValueError("Unsupported submitter fields: " + ", ".join(sorted(unknown)))
    if config.get("challenge_module") != "Challenge" or config.get("solution_module") != "Solution":
        raise ValueError("Expected the separate Challenge and Solution modules")
    if config.get("theorem_names") != [THEOREM]:
        raise ValueError("The advertised full theorem must be the Comparator target")
    axioms = config.get("permitted_axioms")
    if (not isinstance(axioms, list) or len(axioms) != 3
            or not all(isinstance(axiom, str) for axiom in axioms)
            or set(axioms) != PERMITTED):
        raise ValueError("permitted_axioms must be exactly the three standard axioms")
    if config.get("definition_names", []) != []:
        # In Lake.Check.Compare this field EXEMPTS definition bodies from
        # equality; it lists holes, not additional body-equality checks.
        raise ValueError("Keep definition_names empty so ordinary definition bodies are compared")
    if not prefix.is_absolute():
        raise ValueError("The toolchain prefix must be absolute")
    result = dict(config)
    result.pop("enable_nanoda", None)  # Ignored by Palomar, not an enabling switch.
    result["external_kernels"] = {
        "nanoda": [str(prefix / "bin/nanoda_bin")],
        "con-ron": [str(prefix / "bin/con-ron")],
    }
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    parser.add_argument("prefix", type=Path)
    args = parser.parse_args()
    if args.source.resolve() == args.destination.resolve():
        parser.error("The temporary config must not overwrite the submitted config")
    try:
        config = json.loads(args.source.read_text(encoding="utf-8"))
        result = prepare(config, args.prefix)
        args.destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    except (OSError, UnicodeError, ValueError) as error:
        parser.exit(1, f"error: {error}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
