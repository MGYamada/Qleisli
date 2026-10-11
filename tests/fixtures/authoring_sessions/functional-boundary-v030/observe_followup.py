"""Append bounded command/source repairs without rewriting #80 first outcomes.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
Explicit command construction only; recorded command arrays are not executed.
"""
from pathlib import Path
import datetime,hashlib,json,os,subprocess,time

REPOSITORY=Path('/Users/masa/git/Qleisli')
ROOT=REPOSITORY/'tests/fixtures/authoring_sessions/functional-boundary-v030'
CLI=Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
KERNEL=REPOSITORY/'lean-kernel/.lake/build/bin/qleisli-kernel'
EXPECTED_CLI='bd9219f7847f1a7a52a3bd1346d39e8455edf0988e04582595471ae439b5feef'
EXPECTED_KERNEL='39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85'
CASES=['complete-call','partial-call','ordinary-local-callee','quantum-unit-tuple-callee','quantum-unit-tuple-provider','static-description-reuse','owner-duplication','classical-condition','quantum-condition','explicit-observation']
FIRST=json.loads((ROOT/'first-files.json').read_text())
FOLLOWUP=json.loads((ROOT/'followup-before.json').read_text())
OUTPUT=ROOT/'observations-followup'
OUTPUT.mkdir()
EVENTS=[]


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def write_new(path,data):
    with path.open('x',encoding='utf-8') as f:f.write(json.dumps(data,indent=2)+'\n')
def identity():
    result={'cli':{'path':str(CLI),'sha256':sha(CLI)},'kernel':{'path':str(KERNEL),'sha256':sha(KERNEL)}}
    if result['cli']['sha256']!=EXPECTED_CLI or result['kernel']['sha256']!=EXPECTED_KERNEL:raise RuntimeError('fixed executable changed')
    for name,value in {**FIRST['files'],**FOLLOWUP['new_attempt_files']}.items():
        if sha(ROOT/name)!=value:raise RuntimeError('immutable source/prediction changed: '+name)
    return result

def observe(attempt,case,mode='sized-adapter',text=False,verb='check'):
    before=identity();project=ROOT/attempt/case
    command=[str(CLI)]
    if mode=='sized-adapter':command+=['sized',verb,'--entry=main::main','--module=main='+str(project/'main.qli')]
    else:command += [verb,str(project)]
    if not text:command += ['--format=json']
    ident=attempt+'-'+case+'-'+mode+'-'+verb+('-text' if text else '-json')
    started=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic()
    env=os.environ.copy();env['QLEISLI_KERNEL']=str(KERNEL)
    result=subprocess.run(command,cwd=REPOSITORY,env=env,capture_output=True,timeout=30)
    elapsed=time.monotonic()-t
    after={'cli':{'path':str(CLI),'sha256':sha(CLI)},'kernel':{'path':str(KERNEL),'sha256':sha(KERNEL)}}
    streams={}
    for name,content in [('stdout',result.stdout),('stderr',result.stderr)]:
        path=OUTPUT/(ident+'.'+name+'.txt')
        with path.open('xb') as f:f.write(content)
        streams[name]={'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(content).hexdigest(),'bytes':len(content)}
    event={'command':command,'cwd':str(REPOSITORY),'environment_overrides':{'QLEISLI_KERNEL':str(KERNEL)},'attempt':attempt,'case':case,'mode':mode,'exit_code':result.returncode,'started_utc':started,'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'seconds':elapsed,'binary_before':before,'binary_after':after,'binary_identity_stable':before==after,'source_sha256':sha(project/'main.qli'),'manifest_sha256':sha(project/'Qargo.toml'),'raw_streams':streams,'scope':'Actual bounded observation; shared selected-source adapter, not independent implementation or preservation proof.'}
    try:parsed=json.loads(result.stdout)
    except (ValueError,UnicodeDecodeError):parsed=None
    if isinstance(parsed,dict) and parsed.get('format')=='qleisli.result':event['stdout']=parsed
    else:event['transcript']='stdout:\n'+result.stdout.decode(errors='replace')+'\nstderr:\n'+result.stderr.decode(errors='replace')
    path=OUTPUT/(ident+'.json');write_new(path,event);EVENTS.append(str(path.relative_to(ROOT)))
    if before!=after:raise RuntimeError('executable changed; actual result retained')
    identity()
    details=[(d.get('code'),d.get('message')) for d in parsed.get('diagnostics',[])] if isinstance(parsed,dict) else event['transcript']
    print(json.dumps({'attempt':attempt,'case':case,'mode':mode,'verb':verb,'text':text,'exit':result.returncode,'diagnostics':details}),flush=True)
    return result.returncode

for case in CASES:observe('attempt-01',case)
for case in ['partial-call','ordinary-local-callee']:observe('attempt-01',case,text=True)
for case in ['static-description-reuse','owner-duplication']:
    code=observe('attempt-02',case,'finite')
    observe('attempt-02',case)
    if case=='static-description-reuse' and code==0:observe('attempt-02',case,'finite',verb='run')
write_new(OUTPUT/'capture.json',{'format':'qleisli.informed-public-source-followup-capture','version':1,'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'actual_observations':EVENTS,'followup_before_sha256':sha(ROOT/'followup-before.json'),'first_inventory_sha256':sha(ROOT/'first-files.json'),'observer_sha256':sha(Path(__file__)),'scope':'Append-only real follow-up; first sources/results unchanged.'})
print(json.dumps({'observations':len(EVENTS),'final_identity':identity()}),flush=True)
