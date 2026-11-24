"""File/Git/hash/JSON custody only; never launches Lean or mathematical code."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys
from datetime import datetime, timezone

STUDY = Path(__file__).resolve().parent
ROOT = STUDY.parents[2]
LOCK = STUDY / 'SOURCE_LOCK_B.json'

def now():
    return datetime.now(timezone.utc).isoformat()

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return {'bytes':path.stat().st_size, 'sha256':h.hexdigest(), 'mode':path.stat().st_mode & 0o777}

def write(path, value):
    assert not path.exists(), str(path)
    path.write_text(json.dumps(value, indent=2)+'\n')

def runtime():
    result = []
    manifest = json.loads((ROOT/'lake-manifest.json').read_text())
    packages = ROOT/'.lake/packages'
    for spec in manifest['packages']:
        directory = packages/spec['name']
        revision = subprocess.check_output(['git','-C',str(directory),'rev-parse','HEAD'],text=True).strip()
        assert revision == spec['rev'], spec['name']
        library = directory/'.lake/build/lib/lean'
        aggregate = hashlib.sha256()
        count = total = 0
        if library.exists():
            for path in sorted(library.rglob('*')):
                if not path.is_file():
                    continue
                info = digest(path)
                name = str(path.relative_to(library))
                aggregate.update((name+'\0'+str(info['bytes'])+'\0'+info['sha256']+'\0'+str(info['mode'])+'\n').encode())
                count += 1
                total += info['bytes']
        result.append({'package':spec['name'],'revision':revision,'prebuilt_files':count,
                       'prebuilt_bytes':total,'whole_cache_filename_size_hash_mode_sha256':aggregate.hexdigest()})
    return result

def snapshot(out, lock):
    paths = list(lock['files'])+[str(LOCK.relative_to(ROOT))]
    return {'recorded':now(),'original':{p:digest(ROOT/p) for p in paths},
            'copied':{p:digest(out/'source'/p) for p in paths if (out/'source'/p).is_file()},
            'tools':{p:digest(Path(p)) for p in lock['tool_and_runtime_sha256']},
            'packages':runtime(),
            'compiled_olean':digest(out/'olean/CryptoLean/Group/PairIncidenceModule.olean') if (out/'olean/CryptoLean/Group/PairIncidenceModule.olean').is_file() else None}

def main():
    action = sys.argv[1]
    if action == 'fingerprint':
        print(json.dumps(runtime(),indent=2))
        return
    lock = json.loads(LOCK.read_text())
    if action == 'init':
        source,out,temp = sys.argv[2],Path(sys.argv[3]),Path(sys.argv[4])
        for name,expected in lock['files'].items():
            path = ROOT/name
            assert digest(path)['sha256'] == expected['sha256'] and path.stat().st_size == expected['bytes'],name
            public = subprocess.check_output(['git','-C',str(ROOT),'cat-file','blob',source+':'+name])
            assert public == path.read_bytes(),name
            dest = out/'source'/name
            dest.parent.mkdir(parents=True,exist_ok=True)
            shutil.copy2(path,dest)
        assert LOCK.read_bytes() == subprocess.check_output(['git','-C',str(ROOT),'cat-file','blob',source+':'+str(LOCK.relative_to(ROOT))])
        shutil.copy2(LOCK,out/'source'/LOCK.relative_to(ROOT))
        for p,h in lock['tool_and_runtime_sha256'].items():
            assert digest(Path(p))['sha256'] == h,p
        assert runtime() == lock['installed_pinned_package_runtime'], 'prebuilt cache changed'
        ram = os.statvfs('/dev/shm')
        assert ram.f_bavail*ram.f_frsize >= 268435456
        write(out/'CONTEXT.json',{'recorded':now(),'source_commit':source,'root':str(ROOT),'out':str(out),'temp':str(temp),
                                'environment':{k:os.environ.get(k) for k in ['LEAN_PATH','LEAN_NUM_THREADS','LEAN_MAIN_USE_THREAD','LEAN_STACK_SIZE_KB','MIMALLOC_ARENA_RESERVE','CHECKPOINT_SKIP']},
                                'ambient_boundary':'Installed transitive toolchain libraries and OS disclosed; exact package cache hash/revisions guarded, no hermetic or independent execution proof.'})
        write(out/'BUILD_MANIFEST.json',snapshot(out,lock))
    elif action == 'phase':
        out,name,status = Path(sys.argv[2]),sys.argv[3],int(sys.argv[4])
        write(out/(name+'.phase.json'),{'recorded':now(),'name':name,'expected_exit':0,'exit':status,
                                      'complete_stdout':digest(out/(name+'.stdout')),'complete_stderr':digest(out/(name+'.stderr'))})
    elif action == 'pre_audit':
        out = Path(sys.argv[2])
        write(out/'PRE_AUDIT_MANIFEST.json',snapshot(out,lock))
    elif action == 'finish':
        out,status = Path(sys.argv[2]),int(sys.argv[3])
        post = snapshot(out,lock)
        post['outer_exit'] = status
        failures = []
        if (out/'BUILD_MANIFEST.json').exists():
            before = json.loads((out/'BUILD_MANIFEST.json').read_text())
            for name in ['original','copied','tools','packages']:
                if post[name] != before[name]:
                    failures.append(name)
        else:
            failures.append('init incomplete')
        if (out/'PRE_AUDIT_MANIFEST.json').exists():
            before = json.loads((out/'PRE_AUDIT_MANIFEST.json').read_text())
            if post['compiled_olean'] != before['compiled_olean']:
                failures.append('compiled olean')
        elif status == 0:
            failures.append('missing pre-audit manifest')
        post['guard_failures'] = failures
        write(out/'POST_CALL_MANIFEST.json',post)
        if status == 0 and failures:
            raise RuntimeError(str(failures))
    else:
        raise RuntimeError(action)

if __name__ == '__main__':
    main()
