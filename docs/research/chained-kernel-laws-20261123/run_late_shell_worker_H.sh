#!/usr/bin/env bash
# Focused generic law, actual inherited product assembly, canonical axiom audit.
set -euo pipefail
source_commit=${1:?public source commit}
out=${2:?fresh absolute output directory}
compiler_temp=${3:?fresh absolute temporary directory}
repo_dir=$(git rev-parse --show-toplevel)
toolchain=/home/agent/.elan/toolchains/leanprover--lean4---v4.35.0
export PATH="$toolchain/bin:/home/agent/.cargo/bin:$PATH"
export LEAN_STACK_SIZE_KB=16384 LEAN_MAIN_USE_THREAD=0 MIMALLOC_ARENA_RESERVE=65536
export LEAN_NUM_THREADS=0 CARGO_BUILD_JOBS=1 RAYON_NUM_THREADS=1
unset LEAN_SYSROOT LEAN_PATH LEAN_OPTS
umask 077
mkdir "$out" "$compiler_temp"
export TMPDIR="$compiler_temp"
cd "$repo_dir"
mkdir -p "$out/olean/CryptoLean/Group"
export LEAN_PATH="$out/olean"
while IFS= read -r package_dir; do LEAN_PATH="$LEAN_PATH:$repo_dir/$package_dir/.lake/build/lib/lean"; done < <(python3 -c 'import json;print("\n".join(".lake/packages/"+p["name"] for p in json.load(open("lake-manifest.json"))["packages"]))')
export LEAN_PATH
snapshot() {
 python3 - "$source_commit" "$out" "$1" <<'PY_H_METADATA'
from pathlib import Path
import json,hashlib,sys,subprocess,os,datetime
source,out,phase=sys.argv[1],Path(sys.argv[2]),sys.argv[3]
root=Path('.').resolve();lp=root/'docs/research/chained-kernel-laws-20261123/SOURCE_LOCK_H.json';lock=json.loads(lp.read_text());rows=[]
for p,e in lock['files'].items():
 b=(root/p).read_bytes();assert b==subprocess.check_output(['git','cat-file','blob',source+':'+p]),p
 assert len(b)==e['bytes'] and hashlib.sha256(b).hexdigest()==e['sha256'],p
 rows.append({'path':p,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
assert lp.read_bytes()==subprocess.check_output(['git','cat-file','blob',source+':'+str(lp.relative_to(root))])
for p,h in lock['tool_and_runtime_sha256'].items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h,p
packages=[]
for p in json.loads((root/'lake-manifest.json').read_text())['packages']:
 d=root/'.lake/packages'/p['name'];rev=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip();assert rev==p['rev'],p['name'];packages.append({'name':p['name'],'rev':rev})
for p in ('Mathlib/Algebra/Group/Hom/Instances.olean','Mathlib/Algebra/Field/ZMod.olean','Mathlib/Algebra/Group/Prod.olean'):
 assert (root/'.lake/packages/mathlib/.lake/build/lib/lean'/p).is_file(),'missing official prebuilt '+p
(out/(phase+'_MANIFEST.json')).write_text(json.dumps({'recorded':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_commit':source,'source':rows,'lock_sha256':hashlib.sha256(lp.read_bytes()).hexdigest(),'tool_and_runtime_sha256':lock['tool_and_runtime_sha256'],'packages':packages,'environment':{k:os.environ[k] for k in ('TMPDIR','LEAN_PATH','LEAN_STACK_SIZE_KB','LEAN_MAIN_USE_THREAD','MIMALLOC_ARENA_RESERVE','LEAN_NUM_THREADS')},'per_phase_virtual_KiB':2097152,'per_phase_seconds':120,'default_logical_limits':True,'focused_audit_not_whole_project_gate':True},indent=2)+'\n')
PY_H_METADATA
}
finish() {
 local status=$? guard_status=0
 trap - EXIT
 snapshot POST > "$out/final-guards.stdout" 2> "$out/final-guards.stderr" || guard_status=$?
 printf '%s\n' "$status" > "$out/overall.exit"
 if [[ "$status" -ne 0 ]]; then exit "$status"; fi
 exit "$guard_status"
}
trap finish EXIT
snapshot BUILD > "$out/init.stdout" 2> "$out/init.stderr"
phase() {
 local name=$1 status=0
 shift
 printf '%q ' "$@" > "$out/$name.argv"
 printf '\n' >> "$out/$name.argv"
 ( ulimit -c 0; ulimit -v 2097152; timeout --signal=TERM --kill-after=5s 120s strace -f -e trace=mmap,munmap,openat,clone,clone3 -o "$out/$name.trace" "$@" ) > "$out/$name.stdout" 2> "$out/$name.stderr" || status=$?
 printf '%s\n' "$status" > "$out/$name.exit"
 if [[ "$status" -ne 0 ]]; then return "$status"; fi
}
phase generic lean -j1 -DwarningAsError=true -o "$out/olean/CryptoLean/Group/UniqueDouble.olean" CryptoLean/Group/UniqueDouble.lean
phase instance lean -j1 -DwarningAsError=true -o "$out/olean/CryptoLean/Group/UniqueDoubleExamples.olean" CryptoLean/Group/UniqueDoubleExamples.lean
phase audit lean -j1 -DwarningAsError=true --run tools/AuditAxioms.lean CryptoLean.Group.UniqueDouble CryptoLean.Group.UniqueDoubleExamples
