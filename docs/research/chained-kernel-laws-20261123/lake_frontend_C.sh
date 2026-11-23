#!/usr/bin/env bash
# Official installed Lake entry point, interpreted by the exact pinned Lean.
set -euo pipefail
prefix=$(cd "$(dirname "$0")/.." && pwd)
exec "$prefix/bin/lean-real" -j1 --root="$prefix/src/lean/lake" \
  --run "$prefix/src/lean/lake/LakeMain.lean" "$@"
