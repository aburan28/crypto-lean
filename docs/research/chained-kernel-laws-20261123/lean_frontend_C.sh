#!/usr/bin/env bash
# Same pinned kernel binary; enforce the recorded single elaborator worker.
set -euo pipefail
prefix=$(cd "$(dirname "$0")/.." && pwd)
for arg in "$@"; do
  case "$arg" in
    -j1) ;;
    -j*|--threads*) echo 'C refuses a worker override' >&2; exit 66 ;;
  esac
done
exec "$prefix/bin/lean-real" -j1 "$@"
