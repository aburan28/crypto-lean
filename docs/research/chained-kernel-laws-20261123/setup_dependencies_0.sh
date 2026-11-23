#!/usr/bin/env bash
# Software/Git/cache installation only; no study proof or native calls.
set -euo pipefail
source_commit=${1:?public source commit}
out=${2:?fresh absolute RAM output directory}
compiler_temp=${3:?fresh absolute RAM temporary directory}
repo_dir=$(git rev-parse --show-toplevel)
study_rel=docs/research/chained-kernel-laws-20261123
export PATH="/home/agent/.elan/toolchains/leanprover--lean4---v4.35.0/bin:/home/agent/.cargo/bin:$PATH"
export LEAN_STACK_SIZE_KB=16384 LEAN_MAIN_USE_THREAD=0 MIMALLOC_ARENA_RESERVE=65536
export LEAN_NUM_THREADS=1 CARGO_BUILD_JOBS=1 RAYON_NUM_THREADS=1 GIT_TERMINAL_PROMPT=0
unset LEAN_PATH LEAN_OPTS
umask 077
mkdir "$out" "$compiler_temp"
export TMPDIR="$compiler_temp" MATHLIB_CACHE_DIR="$out/prebuilt-cache"
cd "$repo_dir"
snapshot() {
  python3 - "$source_commit" "$out" "$1" <<'PY'
from pathlib import Path
import sys,json,hashlib,subprocess,os,datetime
source,out,phase=sys.argv[1],Path(sys.argv[2]),sys.argv[3]
root=Path('.').resolve(); lock_path=root/'docs/research/chained-kernel-laws-20261123/SOURCE_LOCK_0.json'
lock=json.loads(lock_path.read_text()); rows=[]
for p,e in lock['files'].items():
 b=(root/p).read_bytes(); public=subprocess.check_output(['git','cat-file','blob',source+':'+p])
 assert b==public and len(b)==e['bytes'] and hashlib.sha256(b).hexdigest()==e['sha256'],p
 rows.append({'path':p,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
assert subprocess.check_output(['git','cat-file','blob',source+':'+str(lock_path.relative_to(root))])==lock_path.read_bytes()
tools={}
for name in ('lean','lake'):
 p=Path('/home/agent/.elan/toolchains/leanprover--lean4---v4.35.0/bin')/name
 tools[name]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
dest=out/(phase+'_MANIFEST.json');assert not dest.exists()
dest.write_text(json.dumps({'recorded':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_commit':source,'source':rows,'lock_sha256':hashlib.sha256(lock_path.read_bytes()).hexdigest(),'tools':tools,'environment':{k:os.environ[k] for k in ('TMPDIR','MATHLIB_CACHE_DIR','LEAN_STACK_SIZE_KB','LEAN_MAIN_USE_THREAD','MIMALLOC_ARENA_RESERVE')},'software_setup_only':True},indent=2)+'\n')
PY
}
finish() {
  local status=$? guard_status=0
  trap - EXIT
  snapshot POST > "$out/final-guards.stdout" 2> "$out/final-guards.stderr" || guard_status=$?
  printf '%s\n' "$status" > "$out/setup.exit"
  if [[ "$status" -ne 0 ]]; then exit "$status"; fi
  exit "$guard_status"
}
trap finish EXIT
snapshot BUILD > "$out/init.stdout" 2> "$out/init.stderr"
python3 - <<'PY' > "$out/manifest-packages.tsv"
import json
for p in json.load(open('lake-manifest.json'))['packages']:
 print(p['name'],p['url'],p['rev'],sep='\t')
PY
phase() {
  local name=$1 status=0
  shift
  printf '%q ' "$@" > "$out/$name.argv"
  printf '\n' >> "$out/$name.argv"
  ( ulimit -c 0; ulimit -v 2097152; timeout --signal=TERM --kill-after=5s 600s "$@" ) \
    > "$out/$name.stdout" 2> "$out/$name.stderr" || status=$?
  printf '%s\n' "$status" > "$out/$name.exit"
  if [[ "$status" -ne 0 ]]; then return "$status"; fi
}
mkdir -p .lake/packages
while IFS=$'\t' read -r package_name package_url package_revision; do
  package_dir="$repo_dir/.lake/packages/$package_name"
  if [[ -e "$package_dir" ]]; then
    echo "Refuse existing dependency directory: $package_dir" >&2
    exit 65
  fi
  phase "$package_name-init" git init "$package_dir"
  phase "$package_name-remote" git -C "$package_dir" remote add origin "$package_url"
  phase "$package_name-fetch" git -C "$package_dir" fetch --depth=1 --no-tags origin "$package_revision"
  phase "$package_name-checkout" git -C "$package_dir" checkout --detach "$package_revision"
done < "$out/manifest-packages.tsv"
phase official-cache lake exe cache get Mathlib.Algebra.Group.Hom.Instances Mathlib.Algebra.Field.ZMod Mathlib.LinearAlgebra.BilinearForm.Orthogonal
