from pathlib import Path
import datetime,hashlib,json,os,subprocess,time
root=Path('/private/tmp/qleisli-355-public-effects-first-auwlqr53')
manifest_path=root/'first-sources.json'
manifest_bytes=manifest_path.read_bytes()
assert hashlib.sha256(manifest_bytes).hexdigest()=='2234034c87c8fd81fe3ea6b02ac0437b9adf1c38eb148a497a716d3dabc75d9d'
study=json.loads(manifest_bytes)
cli,kernel=[row['path'] for row in study['binaries']]
def identities():
 return [dict(path=row['path'],sha256=hashlib.sha256(Path(row['path']).read_bytes()).hexdigest(),bytes=Path(row['path']).stat().st_size) for row in study['binaries']]
def original_sources():
 return [dict(path=row['path'],sha256=hashlib.sha256((root/row['path']).read_bytes()).hexdigest(),bytes=(root/row['path']).stat().st_size) for row in study['files']]
assert original_sources()==study['files']
assert identities()==study['binaries']
out=root/'observations-first';out.mkdir()
records=[]
for case in study['cases']:
 project=Path(case['source_root'])
 for profile in ['finite-project','selected-raw']:
  if profile=='finite-project':
   argv=[cli,'check',str(project),'--format=json','--lean-kernel='+kernel]
  else:
   argv=[cli,'check','--entry=main::main','--format=json','--ir-profile=raw','--lean-kernel='+kernel]
   argv += ['--module='+Path(name).stem+'='+str(project/name) for name in sorted(case['files'])]
  before=identities();assert before==study['binaries'],before
  start=datetime.datetime.now(datetime.timezone.utc).isoformat();tick=time.monotonic()
  env=dict(os.environ,QLEISLI_KERNEL=kernel)
  timed_out=False
  try:
   proc=subprocess.run(argv,cwd='/Users/masa/git/Qleisli',env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
   code=proc.returncode;stdout=proc.stdout;stderr=proc.stderr
  except subprocess.TimeoutExpired as error:
   timed_out=True;code=None;stdout=error.stdout or b'';stderr=error.stderr or b''
  after=identities()
  prefix=out/(case['id']+'.'+profile)
  prefix.with_suffix(prefix.suffix+'.stdout.txt').write_bytes(stdout)
  prefix.with_suffix(prefix.suffix+'.stderr.txt').write_bytes(stderr)
  record=dict(case=case['id'],profile=profile,argv=argv,cwd='/Users/masa/git/Qleisli',started_at_utc=start,elapsed_seconds=time.monotonic()-tick,exit_code=code,timed_out=timed_out,stdout=dict(path=str(prefix.with_suffix(prefix.suffix+'.stdout.txt').relative_to(root)),sha256=hashlib.sha256(stdout).hexdigest(),bytes=len(stdout)),stderr=dict(path=str(prefix.with_suffix(prefix.suffix+'.stderr.txt').relative_to(root)),sha256=hashlib.sha256(stderr).hexdigest(),bytes=len(stderr)),binaries_before=before,binaries_after=after,binaries_unchanged=before==after==study['binaries'],predicted_current=case['predicted_current'],required_policy=case['required_policy'])
  try:
   payload=json.loads(stdout)
   record['json']=payload
  except (UnicodeDecodeError,json.JSONDecodeError):
   record['json']=None
  prefix.with_suffix(prefix.suffix+'.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
  records.append(record)
  print(json.dumps(dict(case=case['id'],profile=profile,exit_code=code,timed_out=timed_out,identities_unchanged=record['binaries_unchanged'])),flush=True)
  if not record['binaries_unchanged']:raise RuntimeError('Binary changed; all first diagnostics retained; no subsequent check issued')
assert original_sources()==study['files']
summary=dict(format='qleisli.public-effect-first-observations',version=1,first_sources_sha256=hashlib.sha256(manifest_bytes).hexdigest(),observer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),record_count=len(records),sources_unchanged=True,binaries_before=study['binaries'],binaries_after=identities(),records=records,source_revisions=0,limitations='Informed bounded source-contract diagnostics only; no post-implementation capture, provider/foreign/API complete coverage, native semantic oracle, source/runtime proof, physical/resource claim or issue completion.')
(root/'observations-first.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(summary=str(root/'observations-first.json'),sha256=hashlib.sha256((root/'observations-first.json').read_bytes()).hexdigest(),records=len(records))),flush=True)
