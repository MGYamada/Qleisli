"""Bounded session recorder; no source translation or production acceptance logic.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,subprocess,time

parser=argparse.ArgumentParser()
parser.add_argument('stage',choices=['before','after'])
parser.add_argument('checkout',type=Path)
parser.add_argument('kernel',type=Path)
parser.add_argument('--session',default='first-sources.json')
parser.add_argument('--output-label')
args=parser.parse_args()
fixture=Path(__file__).resolve().parent
out=fixture/(args.output_label or args.stage)
out.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
session=json.loads((fixture/args.session).read_text())
identities={str(p.relative_to(fixture)):sha(p) for p in sorted((fixture/'sources').rglob('*')) if p.is_file()}
identities['Observe.rs']=sha(fixture/'Observe.rs')
commands=[]
def run(label,argv,cwd,env=None):
 start=time.monotonic(); at=datetime.datetime.now(datetime.timezone.utc).isoformat()
 result=subprocess.run([str(v) for v in argv],cwd=cwd,env=env,capture_output=True,timeout=120)
 (out/f'{label}.stdout.txt').write_bytes(result.stdout);(out/f'{label}.stderr.txt').write_bytes(result.stderr)
 commands.append(dict(label=label,argv=[str(v) for v in argv],cwd=str(cwd),started_at=at,seconds=time.monotonic()-start,exit_code=result.returncode,stdout=f'{label}.stdout.txt',stderr=f'{label}.stderr.txt'))
 (out/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
 if result.returncode: raise RuntimeError(f'{label}: {result.returncode}; see saved streams')
 return result
run('version',['rustc','--version'],args.checkout)
run('build',['cargo','build','--offline','--lib','--bin','qleisli'],args.checkout)
observer=args.checkout/f'ordinary-types-observer-{args.stage}'
run('observer-build',['rustc','--edition=2024',fixture/'Observe.rs','--extern',f'qleisli={args.checkout}/target/debug/libqleisli.rlib','-L',f'dependency={args.checkout}/target/debug/deps','-o',observer],args.checkout)
executables={str(p):sha(p) for p in [observer,args.checkout/'target/debug/libqleisli.rlib',args.checkout/'target/debug/qleisli',args.kernel]}
for case in session['cases']:
 caseout=out/case['name'];caseout.mkdir()
 arg=[observer,fixture/'sources'/case['name'],caseout,case['entry']]
 if case['naturals']:arg.append('n=0')
 result=run(case['name'],arg,args.checkout,dict(os.environ,QLEISLI_KERNEL=str(args.kernel)))
 print(case['name'],' | '.join(x for x in result.stdout.decode().splitlines() if not x.startswith(('sized.inputs:','sized.output:'))),flush=True)
assert all(sha(fixture/n)==h for n,h in identities.items())
assert all(sha(Path(n))==h for n,h in executables.items())
(out/'validation.json').write_text(json.dumps(dict(stage=args.stage,observations=len(session['cases']),sources=identities,executables=executables,commands_sha256=sha(out/'commands.json'),scope='Stage-specific parse/check/lower outcomes. Observer exit 0 includes explicit rejection. Actual native success is reported only when requested and observed; no general source-preservation theorem.'),indent=2)+'\n')
