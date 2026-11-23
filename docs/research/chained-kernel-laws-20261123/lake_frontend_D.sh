#!/usr/bin/env bash
# Official source and native Lake implementation, both unchanged and pinned.
set -euo pipefail
prefix=$(cd "$(dirname "$0")/.." && pwd)
exec "$prefix/bin/lean-real" -j1 \
  --load-dynlib="$prefix/lib/lean/libLake_shared.so" \
  --root="$prefix/src/lean/lake" \
  --run "$prefix/src/lean/lake/LakeMain.lean" "$@"
