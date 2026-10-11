#!/usr/bin/env python3
"""Observe the frozen desired source; do not execute commands from records."""
import datetime
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
CLI = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
NATIVE = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
parser = argparse.ArgumentParser()
parser.add_argument('--snapshot', default='attempt-02')
parser.add_argument('--record', default='after-yield')
args = parser.parse_args()
OUT = HERE / args.record
OUT.mkdir(exist_ok=False)
OBS = HERE / 'observations'
OBS.mkdir(exist_ok=True)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest = HERE / ('first-files.json' if args.snapshot == 'attempt-01' else 'second-files.json')
first = json.loads(manifest.read_text())['files']
assert all(digest(HERE / p) == sha for p, sha in first.items())
wrapper = HERE / 'native-log.py'
wrapper.chmod(0o755)
identities = {'cli_sha256': digest(CLI), 'native_sha256': digest(NATIVE),
              'wrapper_sha256': digest(wrapper), 'source_files_sha256': digest(manifest)}
(OUT / 'inputs.json').write_text(json.dumps(identities, indent=2) + '\n')
(OUT / 'driver.py.txt').write_bytes(Path(__file__).read_bytes())
rows = []
observations = []
for project in sorted((HERE / args.snapshot).iterdir()):
    name = project.name
    entry = 'repeat' if name == 'opaque-repeat' else 'outer' if name == 'opaque-forward' else 'f'
    argv = [str(CLI), 'check', f'--entry=main::{entry}',
            f'--module=main={project / "main.qli"}', '--format=json']
    if name in ('opaque-repeat', 'concrete-control'):
        argv += ['--nat=k=2', '--operation=U=main::identity_bit']
    log = OUT / f'{name}.native.jsonl'
    log.write_bytes(b'')
    env = dict(os.environ, QLEISLI_KERNEL=str(wrapper), QLEISLI_HIERARCHY_KERNEL=str(wrapper),
               QLEISLI_STUDY_NATIVE_LOG=str(log), QLEISLI_STUDY_NATIVE=str(NATIVE))
    start = time.monotonic()
    result = subprocess.run(argv, cwd=ROOT, env=env, capture_output=True, timeout=30)
    (OUT / f'{name}.stdout.txt').write_bytes(result.stdout)
    (OUT / f'{name}.stderr.txt').write_bytes(result.stderr)
    data = json.loads(result.stdout)
    count = len(log.read_text().splitlines())
    event = {'command': argv, 'exit_code': result.returncode,
             'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'timestamp_note': 'Clock observation after command completion, not authenticated provenance.',
             'stdout': data, 'native_invocations': count, 'seconds': time.monotonic() - start}
    observation = f'observations/{args.record}-{name}.json'
    (HERE / observation).write_text(json.dumps(event, indent=2, ensure_ascii=False) + '\n')
    observations.append(observation)
    rows.append({'project': name, 'exit_code': result.returncode,
                 'native_invocations': count, 'codes': [d['code'] for d in data['diagnostics']]})
    print(rows[-1], flush=True)
assert all(digest(HERE / p) == sha for p, sha in first.items())
assert digest(CLI) == identities['cli_sha256'] and digest(NATIVE) == identities['native_sha256']
assert all(r['exit_code'] == 1 and r['native_invocations'] == 0 and r['codes'] == ['parse']
           for r in rows if r['project'] != 'concrete-control')
assert next(r for r in rows if r['project'] == 'concrete-control')['exit_code'] == 0
(OUT / 'result.json').write_text(json.dumps({'identities': identities, 'sources_stable': True,
    'results': rows, 'scope': 'Eight desired abstract forms reach parser rejection only; one concrete control reaches native checking. No generic proof or later diagnostic claim.'}, indent=2) + '\n')
sources = {str(p.relative_to(HERE / args.snapshot)): digest(p)
           for p in sorted((HERE / args.snapshot).rglob('*.qli'))}
session = json.loads((HERE / 'session.json').read_text())
assert args.snapshot == 'attempt-02' and len(session['attempts']) == 1
session['attempts'].append({'id': args.snapshot, 'reason': 'Add mandatory yield to the opaque-repeat draft and concrete control; other sources unchanged. Eight abstract forms still reject at parsing; the concrete control reaches native checking.',
         'sha256': sources, 'observations': observations})
(HERE / 'session.json').write_text(json.dumps(session, indent=2) + '\n')
