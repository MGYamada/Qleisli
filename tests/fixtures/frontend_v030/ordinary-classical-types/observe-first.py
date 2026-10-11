from pathlib import Path
import hashlib,json,os,subprocess,time
root=Path('/Users/masa/git/Qleisli'); fix=root/'tests/fixtures/frontend_v030/ordinary-classical-types/initial-study'; observer=Path('/private/tmp/qleisli-ordinary-classical-type-study/observer'); kernel=root/'lean-kernel/.lake/build/bin/qleisli-kernel'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
session=json.loads((fix/'session.json').read_text()); records=[]
for case in session['cases']:
 for p,h in case['sources'].items():assert sha(fix/p)==h
for p,h in session['source_identity'].items():assert sha(root/p)==h,p
identities={str(p):sha(p) for p in (observer,root/'target/debug/libqleisli.rlib',kernel)}
for case in session['cases']:
 d=fix/case['name']; argv=[str(observer),str(d)]; start=time.monotonic();p=subprocess.run(argv,cwd=root,env=dict(os.environ,QLEISLI_KERNEL=str(kernel)),capture_output=True,timeout=45)
 (d/'observed.stdout.txt').write_bytes(p.stdout);(d/'observed.stderr.txt').write_bytes(p.stderr)
 records.append(dict(case=case['name'],argv=argv,cwd=str(root),QLEISLI_KERNEL=str(kernel),exit_code=p.returncode,seconds=time.monotonic()-start,stdout=str((d/'observed.stdout.txt').relative_to(fix)),stderr=str((d/'observed.stderr.txt').relative_to(fix))))
 (fix/'observations.json').write_text(json.dumps(records,indent=2)+'\n')
 assert p.returncode==0,case['name']
for case in session['cases']:
 for p,h in case['sources'].items():assert sha(fix/p)==h
for p,h in session['source_identity'].items():assert sha(root/p)==h,p
assert identities=={p:sha(Path(p)) for p in identities}
(fix/'validation.json').write_text(json.dumps(dict(format='qleisli.ordinary-classical-type-observations',version=1,processes=len(records),session_sha256=sha(fix/'session.json'),observations_sha256=sha(fix/'observations.json'),executables_and_linked_library=identities,all_exit_zero=True,sources_and_executables_unchanged_during_observation=True,scope='Observer exit zero includes diagnostic rejection. Native kernel results were not requested for hierarchy proposals; source check, elaboration and lowering are distinct observations.'),indent=2)+'\n')
for r in records:
 lines=(fix/r['stdout']).read_text().splitlines()
 print(r['case'], ' | '.join(x for x in lines if not x.startswith(('sized.inputs:','sized.output:'))))
