import hashlib,json,os,subprocess,time
from pathlib import Path
root=Path('/Users/masa/git/Qleisli'); fix=root/'tests/fixtures/frontend_v030/predicate-domain'; out=fix/'validation'; out.mkdir(exist_ok=False)
scratch=Path('/private/tmp/qleisli-predicate-domain-after'); scratch.mkdir(exist_ok=False)
kernel=root/'lean-kernel/.lake/build/bin/qleisli-kernel'; env=dict(os.environ,QLEISLI_KERNEL=str(kernel))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,v): p.write_text(json.dumps(v,indent=2)+'\n')
paths=sorted(list((root/'src').rglob('*.rs'))+list((root/'stdlib').rglob('*.qli'))+[root/'Cargo.toml',root/'Cargo.lock'])
identity={str(p.relative_to(root)):sha(p) for p in paths}; write(out/'production-before.json',identity)
records=[]
def run(label,argv,expected=0):
    start=time.monotonic(); p=subprocess.run(list(map(str,argv)),cwd=root,env=env,capture_output=True,timeout=300)
    (out/f'{label}.stdout.txt').write_bytes(p.stdout); (out/f'{label}.stderr.txt').write_bytes(p.stderr)
    records.append(dict(label=label,argv=list(map(str,argv)),cwd=str(root),QLEISLI_KERNEL=str(kernel),exit_code=p.returncode,seconds=time.monotonic()-start,stdout=f'{label}.stdout.txt',stderr=f'{label}.stderr.txt'))
    write(out/'commands.json',records)
    if p.returncode!=expected: raise RuntimeError((label,p.returncode,p.stderr[-1000:]))
    return p
run('remaining-focused-tests',['cargo','test','--offline','--test','source_judgments','--test','with_computed_diagnostics','--test','function_contracts','--test','operation_parameters','--test','cli_json','--test','cli_sampling'])
run('build',['cargo','build','--offline','--lib','--bin','qleisli'])
observer=scratch/'observer'; observer_source=root/'tests/fixtures/frontend_v030/lexical-resolution/initial-study/observer.rs'
run('observer-build',['rustc','--edition=2024',observer_source,'--extern',f'qleisli={root}/target/debug/libqleisli.rlib','-L',f'dependency={root}/target/debug/deps','-o',observer])
oldstudy=Path('/private/tmp/qleisli-basis-arity-study-0d93a18')
cases=[]
old=json.loads((fix/'initial-study/comparison.json').read_text())['cases']
for item in old:
    case=item['case']; source=oldstudy/case
    assert (source/'main.qli').read_bytes()==(fix/'initial-study'/case/'main.qli').read_bytes()
    p=run('study-'+case,[observer,source,'check']); diagnostic=next(s for s in p.stdout.decode().splitlines() if s.startswith('finite.check:'))
    accepted=diagnostic=='finite.check: ok'; legacy=case.startswith(('restricted-legacy-','certified-legacy-')) or case in ('restricted-zero','certified-zero')
    assert accepted==(False if legacy else item['accepted'])
    if legacy: assert 'code: "arity"' in diagnostic
    cases.append(dict(case=case,before_accepted=item['accepted'],after_accepted=accepted,diagnostic=diagnostic,intentional_arity_rejection=legacy))
write(out/'study-comparison.json',dict(cases=cases,after_accepted=sum(c['after_accepted'] for c in cases),expected_outcomes_match=True))
oldcli=Path('/private/tmp/qleisli-lexical-baseline-fae0/target/debug/qleisli'); newcli=root/'target/debug/qleisli'
translations=json.loads((fix/'current-translations.json').read_text())['translations']
inputs=[]
for label,historical,current in [
 ('pair-contract',root/translations[0]['historical'],root/translations[0]['current']),
 ('basis-tuple-pattern',root/translations[1]['historical'],root/translations[1]['current']),
 ('phase-mismatch',root/translations[2]['historical'],root/translations[2]['current']),
 ('grover',root/'tests/fixtures/authoring_sessions/grover-trial-v020/attempt-02',fix/'current/grover-trial-v020')]:
    pair=[]
    for kind,original in [('historical',historical),('current',current)]:
        dest=scratch/(label+'-'+kind); dest.mkdir(); (dest/'Qargo.toml').write_bytes((root/'tests/Qargo.toml').read_bytes())
        sources=sorted(original.glob('*.qli')) if original.is_dir() else [original]
        for s in sources: (dest/(s.name if original.is_dir() else 'main.qli')).write_bytes(s.read_bytes())
        inputs.append(dict(label=label,kind=kind,original=str(original.relative_to(root)),files={str(p):sha(p) for p in sorted(dest.iterdir())}))
        pair.append(dest)
    hist,cur=pair
    # These exact sources are first saved and hashed above before any command.
    write(out/'historical-current-inputs.json',inputs)
    rejection=run(label+'-historical-new-check',[newcli,'check',hist,'--format=json'],1)
    assert b'arity' in rejection.stdout+rejection.stderr
    if label=='phase-mismatch':
        a=run(label+'-before',[oldcli,'check',hist,'--format=json'],1); b=run(label+'-after',[newcli,'check',cur,'--format=json'],1)
        assert b'contract' in a.stdout+a.stderr and b'contract' in b.stdout+b.stderr
    else:
        a=run(label+'-before-run',[oldcli,'run',hist,'--format=json']); b=run(label+'-after-run',[newcli,'run',cur,'--format=json'])
        assert a.stdout==b.stdout,(label,a.stdout,b.stdout)
        outputs=[]
        for kind,cli,path in [('before',oldcli,hist),('after',newcli,cur)]:
            output=out/f'{label}-{kind}.proposal.json'
            run(label+'-'+kind+'-proposal',[cli,'emit-ir',path,'--output='+str(output)])
            outputs.append(output)
        assert outputs[0].read_bytes()==outputs[1].read_bytes(),label
for r in translations:
    assert sha(root/r['historical'])==r['historical_sha256']; assert sha(root/r['current'])==r['current_sha256']
assert identity=={str(p.relative_to(root)):sha(p) for p in paths}
write(out/'summary.json',dict(status='passed',study_cases=26,positive_derivatives_with_identical_proposal_bytes_and_runs=3,negative_derivative_preserves_contract_failure=True,historical_sources_unchanged=True,production_unchanged=True,executables={str(p):sha(p) for p in [oldcli,newcli,observer,kernel]},scope='Bounded observations and exact serialized proposed IR identity, plus actual native checking/execution of three closed examples. Not a universal source-preservation proof.'))
print('Recorded focused tests, 26 source observations, and 4 historical/current derivatives.')
