#!/usr/bin/env bash
# Only the first unfinished official-cache stage; no study proof/native calls.
set -euo pipefail
source_commit=${1:?public source commit}
out=${2:?fresh absolute RAM output directory}
compiler_temp=${3:?fresh absolute RAM temporary directory}
repo_dir=$(git rev-parse --show-toplevel)
real_toolchain=/home/agent/.elan/toolchains/leanprover--lean4---v4.35.0
export PATH="/home/agent/.elan/toolchains/leanprover--lean4---v4.35.0/bin:/home/agent/.cargo/bin:$PATH"
export LEAN_STACK_SIZE_KB=16384 LEAN_MAIN_USE_THREAD=0 MIMALLOC_ARENA_RESERVE=65536
export LEAN_NUM_THREADS=1 CARGO_BUILD_JOBS=1 RAYON_NUM_THREADS=1 GIT_TERMINAL_PROMPT=0
unset LEAN_PATH LEAN_OPTS MATHLIB_CACHE_GET_URL MATHLIB_CACHE_PUT_URL
umask 077
mkdir "$out" "$compiler_temp"
export TMPDIR="$compiler_temp" MATHLIB_CACHE_DIR="$out/prebuilt-cache" LAKE_CACHE_DIR="$out/lake-cache"
cd "$repo_dir"
prefix="$out/toolchain-exact"
mkdir -p "$prefix/bin"
cp "$real_toolchain/bin/lean" "$prefix/bin/lean-real"
chmod 0555 "$prefix/bin/lean-real"
for component in lib include src share; do
  if [[ -e "$real_toolchain/$component" ]]; then ln -s "$real_toolchain/$component" "$prefix/$component"; fi
done
for binary in "$real_toolchain"/bin/*; do
  name=${binary##*/}
  case "$name" in lean|lake) continue ;; esac
  ln -s "$binary" "$prefix/bin/$name"
done
cp docs/research/chained-kernel-laws-20261123/lean_frontend_C.sh "$prefix/bin/lean"
cp docs/research/chained-kernel-laws-20261123/lake_frontend_D.sh "$prefix/bin/lake"
chmod 0555 "$prefix/bin/lean" "$prefix/bin/lake"
export PATH="$prefix/bin:$PATH" LEAN_SYSROOT="$prefix"
snapshot() {
  python3 - "$source_commit" "$out" "$1" <<'PY_METADATA_B'
from pathlib import Path
import sys,json,hashlib,subprocess,os,datetime
source,out,phase=sys.argv[1],Path(sys.argv[2]),sys.argv[3]
root=Path('.').resolve(); lock_path=root/'docs/research/chained-kernel-laws-20261123/SOURCE_LOCK_D.json'
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
runtime={}
for name,expected in lock['runtime_library_sha256'].items():
 p=Path('/home/agent/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean')/name
 digest=hashlib.sha256(p.read_bytes()).hexdigest();assert digest==expected,name
 runtime[name]=digest
tools['runtime_libraries']=runtime
front=out/'toolchain-exact'
assert hashlib.sha256((front/'bin/lean-real').read_bytes()).hexdigest()==tools['lean']['sha256']
for name in ('lean','lake'):
 p=front/'bin'/name
 expected=root/'docs/research/chained-kernel-laws-20261123'/({'lean':'lean_frontend_C.sh','lake':'lake_frontend_D.sh'}[name])
 assert p.read_bytes()==expected.read_bytes(),name
for p,e in lock['external_source_inputs'].items():
 b=Path(p).read_bytes();assert len(b)==e['bytes'] and hashlib.sha256(b).hexdigest()==e['sha256'],p
tools['prefix_frontends']={name:hashlib.sha256((front/'bin'/name).read_bytes()).hexdigest() for name in ('lean-real','lean','lake')}
dest=out/(phase+'_MANIFEST.json');assert not dest.exists()
dest.write_text(json.dumps({'recorded':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_commit':source,'source':rows,'lock_sha256':hashlib.sha256(lock_path.read_bytes()).hexdigest(),'tools':tools,'environment':{k:os.environ[k] for k in ('TMPDIR','MATHLIB_CACHE_DIR','LEAN_STACK_SIZE_KB','LEAN_MAIN_USE_THREAD','MIMALLOC_ARENA_RESERVE','LEAN_NUM_THREADS')},'software_setup_only':True},indent=2)+'\n')
PY_METADATA_B
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
python3 - <<'PY_DEPENDENCIES_B' > "$out/dependency-verification.stdout" 2> "$out/dependency-verification.stderr"
import json,subprocess
for p in json.load(open('lake-manifest.json'))['packages']:
 path='.lake/packages/'+p['name']
 rev=subprocess.check_output(['git','-C',path,'rev-parse','HEAD'],text=True).strip()
 assert rev==p['rev'],p['name']
 assert not subprocess.check_output(['git','-C',path,'status','--porcelain','--untracked-files=no']),p['name']
 print(p['name'],rev)
PY_DEPENDENCIES_B
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
phase official-cache strace -f -e trace=clone,clone3,mmap,munmap,execve -o "$out/cache-startup.trace" lake exe cache get Mathlib.Algebra.Group.Hom.Instances Mathlib.Algebra.Field.ZMod Mathlib.LinearAlgebra.BilinearForm.Orthogonal
