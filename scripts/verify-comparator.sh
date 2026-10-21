#!/usr/bin/env bash
# Run the bundled sandboxed Comparator and independent proof kernels.
# Adapted from the Apache-2.0 PalomarTemplate at
# 2891de4c48955af824969a263d31b25e7a9a1406.
set -euo pipefail

repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd -- "$repo"
for command in bwrap lean lake python3 git env; do
  command -v "$command" >/dev/null || { printf 'Missing command: %s\n' "$command" >&2; exit 1; }
done
if [ "$(uname -s)" != Linux ]; then
  echo 'The official sandboxed Comparator requires Linux.' >&2
  exit 1
fi
test -f lake-manifest.json
prefix=$(lean --print-prefix)
for binary in lake leanexport leanchecker nanoda_bin con-ron; do
  test -x "$prefix/bin/$binary" || { printf 'Missing bundled binary: %s\n' "$binary" >&2; exit 1; }
done

temporary_config=$(mktemp "${TMPDIR:-/tmp}/three-im-one-cm-comparator.XXXXXXXX.json")
trap 'rm -f -- "$temporary_config"' EXIT
python3 scripts/make-comparator-config.py comparator.json "$temporary_config" "$prefix"

# Same fixed-dependency cache step as the official template. No dependency update.
lake exe cache get
python3 scripts/verify-pins.py
# Refuse to let missing/stale local outputs cause an unplanned bulk build.
# Run build-topological.py first; the Comparator still makes its own normal
# sandboxed builds and exports. Do not disable the sandbox or replay exports.
lake --no-build build +Challenge:leanArts +Solution:leanArts
"$prefix/bin/lake" comparator --config "$temporary_config"
