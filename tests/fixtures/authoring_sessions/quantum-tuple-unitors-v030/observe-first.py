from pathlib import Path
import hashlib,json,subprocess,datetime,os,time
root=Path('/Users/masa/git/Qleisli');p=root/'tests/fixtures/authoring_sessions/quantum-tuple-unitors-v030'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def save(name,v):
 f=p/name;f.parent.mkdir(parents=True,exist_ok=True);assert not f.exists(),f
 f.write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
identity=json.loads((p/'identity-before.json').read_text());first=json.loads((p/'first-files.json').read_text())['files']
for f,h in first.items():assert sha(p/f)==h,f
cli=Path(identity['binary']['path']);kernel=Path(identity['kernel']['path'])
assert sha(cli)==identity['binary']['sha256'];assert sha(kernel)==identity['kernel']['sha256']
env={'QLEISLI_KERNEL':str(kernel),'QLEISLI_HIERARCHY_KERNEL':str(kernel)};actual_env=dict(os.environ,**env)
rows=[]
for case in json.loads((p/'expectations.json').read_text())['cases']:
 name=case['name'];d=p/'attempt-01'/name
 for route in ['selected','finite']:
  args=[str(cli),'--format=json','check']
  if route=='selected':args += ['--entry=main::f','--module=main='+str(d/'main.qli'),'--ir-profile=hierarchy','--lean-kernel='+str(kernel)]
  else:args += [str(d)]
  date=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic()
  run=subprocess.run(args,cwd=root,env=actual_env,capture_output=True,timeout=60)
  out=run.stdout.decode('utf-8');err=run.stderr.decode('utf-8')
  record={'command':args,'working_directory':str(root),'environment':env,'exit_code':run.returncode,'recorded_utc':date,'timestamp_note':'Clock observation immediately before this command, not an authoring timestamp.','elapsed_seconds':time.monotonic()-t,'stdout_text':out,'stderr':err,'source_sha256':sha(d/'main.qli'),'manifest_sha256':sha(d/'Qargo.toml'),'binary_sha256':sha(cli),'kernel_sha256':sha(kernel)}
  try:record['stdout']=json.loads(out)
  except json.JSONDecodeError:pass
  save(f'observations/{name}-{route}.json',record)
  diagnostics=record.get('stdout',{}).get('diagnostics',[])
  rows.append({'case':name,'route':route,'exit_code':run.returncode,'diagnostics':[{'code':x.get('code'),'message':x.get('message')} for x in diagnostics]})
  print(name,route,run.returncode,[x.get('message') for x in diagnostics],flush=True)
for f,h in first.items():assert sha(p/f)==h,f
current={f:sha(root/f) for f in identity['current_source_sha256']}
assert current==identity['current_source_sha256'];assert sha(cli)==identity['binary']['sha256'];assert sha(kernel)==identity['kernel']['sha256']
save('identity-after.json',{'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'binary_sha256':sha(cli),'kernel_sha256':sha(kernel),'current_source_sha256':current,'first_files_unchanged':True,'production_sources_unchanged':True,'scope':'Exact original source files, existing binaries and selected101 production sources unchanged through44 observations; no build/replay.'})
save('baseline-summary.json',{'observations':rows,'count':len(rows),'scope':'Actual compile/check outcomes only; open functions not executed. Unsupported/import errors may mask intended negative rules. No source repairs.'})
