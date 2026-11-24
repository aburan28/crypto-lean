#!/usr/bin/env bash
# Direct pinned compiler and unchanged canonical auditor; no Lake/cache build.
set -euo pipefail
source_commit=${1:?public source commit}
out=${2:?fresh absolute RAM output directory}
compiler_temp=${3:?fresh absolute RAM compiler directory}
study_dir=$(cd "$(dirname "$0")" && pwd)
repo_dir=$(git -C "$study_dir" rev-parse --show-toplevel)
toolchain=/home/agent/.elan/toolchains/leanprover--lean4---v4.35.0
export PATH="$toolchain/bin:/home/agent/.cargo/bin:$PATH"
export LEAN_NUM_THREADS=1 LEAN_STACK_SIZE_KB=16384 LEAN_MAIN_USE_THREAD=0 MIMALLOC_ARENA_RESERVE=65536
export RAYON_NUM_THREADS=1 CARGO_BUILD_JOBS=1
export CHECKPOINT_SKIP="Fixed genuine additive pair-incidence mathematical proof, not an experiment; full public source/input/lock checkpoint and whole-byte readback."
unset LEAN_SYSROOT LEAN_PATH LEAN_OPTS
umask 077
mkdir "$out" "$compiler_temp"
mkdir -p "$out/olean/CryptoLean/Group"
export TMPDIR="$compiler_temp"
export LEAN_PATH="$out/olean"
while IFS= read -r package_dir; do LEAN_PATH="$LEAN_PATH:$repo_dir/.lake/packages/$package_dir/.lake/build/lib/lean"; done < <(python3 -c 'import json,sys;print("\n".join(p["name"] for p in json.load(open(sys.argv[1]))["packages"]))' "$repo_dir/lake-manifest.json")
export LEAN_PATH
metadata="$study_dir/custody_metadata_B.py"
finish() {
 local status=$? guard_status=0
 trap - EXIT
 python3 "$metadata" finish "$out" "$status" > "$out/final-guards.stdout" 2> "$out/final-guards.stderr" || guard_status=$?
 if [[ "$status" -ne 0 ]]; then exit "$status"; fi
 exit "$guard_status"
}
trap finish EXIT
python3 "$metadata" init "$source_commit" "$out" "$compiler_temp" > "$out/init.stdout" 2> "$out/init.stderr"
cd "$out/source"
phase() {
 local name=$1 status=0
 shift
 printf '%q ' "$@" > "$out/$name.argv"
 printf '\n' >> "$out/$name.argv"
 ( ulimit -c 0; ulimit -v 2097152; timeout --signal=TERM --kill-after=5s 120s "$@" ) > "$out/$name.stdout" 2> "$out/$name.stderr" || status=$?
 python3 "$metadata" phase "$out" "$name" "$status"
 if [[ "$status" -ne 0 ]]; then return "$status"; fi
}
phase lean-version lean --version
phase law lean -j1 -DwarningAsError=true -o "$out/olean/CryptoLean/Group/PairIncidenceModule.olean" CryptoLean/Group/PairIncidenceModule.lean
chmod 0444 "$out/olean/CryptoLean/Group/PairIncidenceModule.olean"
python3 "$metadata" pre_audit "$out" > "$out/pre-audit.stdout" 2> "$out/pre-audit.stderr"
phase audit lean -j1 -DwarningAsError=true --run tools/AuditAxioms.lean CryptoLean.Group.PairIncidenceModule
