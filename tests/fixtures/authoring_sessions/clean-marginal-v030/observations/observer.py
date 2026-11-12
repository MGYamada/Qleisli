from pathlib import Path
import datetime, hashlib, json, os, signal, subprocess, time
BASE=Path(__file__).parent
FIRST=BASE.parent/'stage7-clean-157-marginal-first'
WORK=Path('/private/tmp/qleisli-516-provider-followup')
CLI=Path('/private/tmp/qleisli-beta-qmatch-bounded-v5.wxZviN/target/debug/qleisli')
KERNEL=WORK/'lean-kernel/.lake/build/bin/qleisli-kernel'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def inputs(): return {str(p.relative_to(FIRST)):sha(p) for p in sorted(FIRST.rglob('*')) if p.is_file()}
def identities(): return {'cli':{'path':str(CLI),'sha256':sha(CLI)},'kernel':{'path':str(KERNEL),'sha256':sha(KERNEL)}}
original=inputs(); binaries=identities()
context={'kind':'newly-authored-first-observer','recorded_before_invocations_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'worktree_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=WORK,text=True).strip(),'worktree_status':subprocess.check_output(['git','status','--porcelain'],cwd=WORK,text=True),'source_hashes':original,'binaries':binaries,'build_attestation':'Existing executables identified by bytes; repository HEAD is not an attestation of their build source.','command_provenance':'Commands authored from current CLI --help; no commands are executed from historical records.','native_invocation_note':'Explicit native path supplied; no native-process counter or child-start attestation is installed.'}
(BASE/'context.json').write_text(json.dumps(context,indent=2)+'\n')
records=[]
for name in ['coherent-uncompute','explicit-reset','false-unitary-reset']:
 for mode in ['check','run']:
  n=f'{len(records)+1:02d}-{name}-{mode}'; d=BASE/n;d.mkdir()
  argv=[str(CLI),mode,str(FIRST/'attempt-01'/name),'--format=json','--lean-kernel='+str(KERNEL)]
  before={'source_hashes':inputs(),'binaries':identities()}
  assert before['source_hashes']==original and before['binaries']==binaries
  started=datetime.datetime.now(datetime.timezone.utc).isoformat(); t=time.monotonic()
  record={'argv':argv,'cwd':str(WORK),'started_at_utc':started,'before':before}
  (d/'command.json').write_text(json.dumps(record,indent=2)+'\n')
  child=subprocess.Popen(argv,cwd=WORK,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
  try:
   out,err=child.communicate(timeout=90);code=child.returncode;timed_out=False
  except subprocess.TimeoutExpired:
   os.killpg(child.pid,signal.SIGTERM)
   try: out,err=child.communicate(timeout=5)
   except subprocess.TimeoutExpired:
    os.killpg(child.pid,signal.SIGKILL);out,err=child.communicate()
   code=child.returncode;timed_out=True
  (d/'stdout.txt').write_bytes(out);(d/'stderr.txt').write_bytes(err)
  after={'source_hashes':inputs(),'binaries':identities()}
  record.update(exit_code=code,timed_out=timed_out,elapsed_seconds=time.monotonic()-t,ended_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),after=after,stdout_sha256=sha(d/'stdout.txt'),stderr_sha256=sha(d/'stderr.txt'))
  (d/'result.json').write_text(json.dumps(record,indent=2)+'\n')
  records.append({'name':n,'result':n+'/result.json','exit_code':code,'timed_out':timed_out})
  (BASE/'observations.json').write_text(json.dumps(records,indent=2)+'\n')
  print(n, 'exit',code,flush=True)
  assert after==before,'source or executable changed during observation'
  assert not timed_out,'timeout retained; investigate before continuing'
print('All six first observations saved; original packet and executable identities unchanged.',flush=True)
