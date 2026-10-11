#!/usr/bin/env python3
"""Disk-safe selected caller replay; no builds and no historical input rewrites."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
BINARY = Path('/private/tmp/qleisli-ordinary-types-after-20261005/target/debug/qleisli')
KERNEL = ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel'
ENV = os.environ | {'QLEISLI_BIN':str(BINARY), 'QLEISLI_KERNEL':str(KERNEL),
                    'PYTHONDONTWRITEBYTECODE':'1','PYTHONPATH':str(ROOT/'python')}
SCRIPTS = ['current_source_fixtures.py','test_interop_external.py','test_interop_native.py',
 'test_connections.py','test_source_kernel.py','test_lean_phase_layout.py',
 'test_lean_interference.py','test_lean_qft.py','test_lean_qpe.py','test_lean_controlled_power.py']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source_map=json.loads((HERE/'source-map.json').read_text())
paths=[ROOT/'scripts'/p for p in SCRIPTS]+[HERE/'source-map.json',Path(__file__).resolve(),BINARY,KERNEL]
paths += list((ROOT/'src').rglob('*.rs'))+list((ROOT/'stdlib').rglob('*.qli'))
for entry in source_map['projects']:
 for key in ('historical_path','current_path'):
  paths += [ROOT/entry[key]/file['path'] for file in entry['files']]
identity=lambda:{str(p):sha(p) for p in paths}
before=identity();commands=[]
(HERE/'results').mkdir(exist_ok=True)
def run(name,argv,expected=0):
 start=time.monotonic()
 result=subprocess.run(list(map(str,argv)),cwd=ROOT,env=ENV,capture_output=True,timeout=180)
 out=HERE/'results'/f'{name}.stdout.txt';err=HERE/'results'/f'{name}.stderr.txt'
 out.write_bytes(result.stdout);err.write_bytes(result.stderr)
 commands.append(dict(name=name,argv=list(map(str,argv)),cwd=str(ROOT),exit_code=result.returncode,
  expected_exit=expected,seconds=time.monotonic()-start,stdout=str(out.relative_to(HERE)),
  stderr=str(err.relative_to(HERE)),stdout_sha256=sha(out),stderr_sha256=sha(err)))
 (HERE/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
 print(name,result.returncode,flush=True)
 if result.returncode!=expected: raise RuntimeError(f'{name}: unexpected result; retained exact streams')
 return result
for mode in ('emit-qasm','emit-qir'):
 run('historical-terminal-'+mode,[BINARY,'interop',mode,ROOT/'tests/fixtures/interop/terminal','--input=qli'],1)
for name in ('phase_layout','interference','qft','qpe','controlled_power'):
 run('source-'+name,[sys.executable,ROOT/f'scripts/test_lean_{name}.py','--source-only',BINARY])
run('source-kernel',[sys.executable,ROOT/'scripts/test_source_kernel.py'])
terminal=ROOT/'tests/fixtures/frontend_v030/ordinary-type-cutover/current/interop/terminal'
for mode in ('check','emit-qasm','emit-qir'):
 result=run('current-terminal-'+mode,[BINARY,'interop',mode,terminal,'--input=qli'])
 if mode!='check':
  doc=json.loads(result.stdout)
  (HERE/'results'/('terminal.'+('qasm' if mode=='emit-qasm' else 'll'))).write_text(doc['result']['text'])
run('external-terminal-oracles',['/private/tmp/qleisli-review-interop-venv/bin/python','-c',
 "import pathlib,sys,types;sys.path.insert(0,'scripts');import test_interop_external as t;"+
 "t.OPTIONS=types.SimpleNamespace(llvm_as='/opt/homebrew/opt/llvm/bin/llvm-as',opt='/opt/homebrew/opt/llvm/bin/opt');"+
 "c=t.ExternalFormats();p=pathlib.Path('tests/fixtures/frontend_v030/ordinary-type-client-integration/results');"+
 "c.check_qasm((p/'terminal.qasm').read_text(),['h','cx'],[1,0]);c.check_qir((p/'terminal.ll').read_text(),2,2);"+
 "print('Existing terminal QASM and LLVM/QIR oracles passed on selected main-CLI exports.')"])
run('python-project-reverification',['/private/tmp/qleisli-v028-release-python/bin/python',
 ROOT/'scripts/test_connections.py','Connections.test_project_and_raw_ir_reverification','-v'])
run('selected-native-clients',[sys.executable,'-c',
 "import os,pathlib,sys,unittest;sys.path.insert(0,'scripts');import test_interop_native as t;"+
 "t.BINARY=pathlib.Path(os.environ['QLEISLI_BIN']);t.KERNEL=pathlib.Path(os.environ['QLEISLI_KERNEL']);"+
 "s=unittest.TestSuite(t.PublicNative(n) for n in ['test_all_actions_formats_use_real_native_checker','test_python_imports_and_every_program_method_use_selected_kernel']);"+
 "r=unittest.TextTestRunner(verbosity=2).run(s);sys.exit(not r.wasSuccessful())"])
after=identity()
(HERE/'validation.json').write_text(json.dumps(dict(status='passed' if before==after else 'source-changed',
 scope='Selected existing source-only callers and terminal exporters/Python native clients. No Cargo/Lean builds. Not the full interop example or external target-coefficient suite.',
 binary_build_snapshot='tests/fixtures/frontend_v030/ordinary-types-independent/after-source.json',
 snapshot_limit='Reuses the independently built canonical-cutover CLI. Current source identities below are recorded, not a claim that this binary was freshly built from them; subsequent source deltas were separately recorded as formatting/documentation.',
 commands='commands.json',source_map_sha256=sha(HERE/'source-map.json'),before=before,after=after,
 unchanged_during_validation=before==after),indent=2)+'\n')
assert before==after
print('Selected replay passed; all bound source and executable inputs unchanged.')
