from pathlib import Path
import hashlib,json,os,subprocess,sys,time
root=Path('/Users/masa/git/Qleisli')
base=root/'tests/fixtures/frontend_v030/checked-operation/implementation-01'
name=sys.argv[1]
argv=sys.argv[2:]
assert argv and not (base/(name+'.json')).exists(), 'Refusing to overwrite command record'
env=dict(os.environ,CARGO_TARGET_DIR=os.environ.get('QLEISLI_VALIDATION_TARGET','/private/tmp/qleisli-bounded-validation-target'),CARGO_INCREMENTAL='0',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_TEST_DEBUG='0',QLEISLI_KERNEL=str(root/'lean-kernel/.lake/build/bin/qleisli-kernel'))
start=time.monotonic()
with (base/(name+'.stdout.txt')).open('wb') as out,(base/(name+'.stderr.txt')).open('wb') as err:
    completed=subprocess.run(argv,cwd=root,env=env,stdout=out,stderr=err)
record={'argv':argv,'exit_code':completed.returncode,'seconds':time.monotonic()-start,'cwd':str(root),'environment':{k:env[k] for k in ('CARGO_TARGET_DIR','CARGO_INCREMENTAL','CARGO_PROFILE_DEV_DEBUG','CARGO_PROFILE_TEST_DEBUG','QLEISLI_KERNEL')},'streams':{kind:{'path':(base/(name+'.'+kind+'.txt')).relative_to(root).as_posix(),'sha256':hashlib.sha256((base/(name+'.'+kind+'.txt')).read_bytes()).hexdigest()} for kind in ('stdout','stderr')}}
(base/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ('argv','exit_code','seconds')}),flush=True)
for kind in ('stdout','stderr'):
    stream=(base/(name+'.'+kind+'.txt')).read_text()
    print(kind+':\n'+stream[-3000:],flush=True)
sys.exit(completed.returncode)
