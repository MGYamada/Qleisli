#!/usr/bin/env python3
"""Append actual observations of unchanged desired sources, never replay records.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import datetime
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
OUT = HERE / 'implementation'
OUT.mkdir(exist_ok=False)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


original = json.loads((HERE / 'second-files.json').read_text())['files']
assert all(digest(HERE / p) == sha for p, sha in original.items())
wrapper = HERE / 'native-log.py'
identities = {
    'cli_sha256': digest(CLI), 'native_sha256': digest(NATIVE),
    'wrapper_sha256': digest(wrapper),
    'original_snapshot_manifest_sha256': digest(HERE / 'second-files.json'),
    'provider_files': {
        str(p.relative_to(HERE)): digest(p)
        for p in sorted((HERE / 'providers').iterdir())
    },
    'checked_sources': {
        str(p.relative_to(ROOT)): digest(p)
        for p in sorted((ROOT / 'src').rglob('*.rs'))
    },
}
(OUT / 'inputs.json').write_text(json.dumps(identities, indent=2) + '\n')
(OUT / 'driver.py.txt').write_bytes(Path(__file__).read_bytes())
rows, observations = [], []
cases = [(p.name, p.name, None) for p in sorted((HERE / 'attempt-02').iterdir())]
cases += [('opaque-repeat-register', 'opaque-repeat', 'Bits<1>')]
for label, name, extra_type in cases:
    entry = 'repeat' if name == 'opaque-repeat' else 'outer' if name == 'opaque-forward' else 'f'
    argv = [str(CLI), 'check', f'--entry=main::{entry}',
            f'--module=main={HERE / "attempt-02" / name / "main.qli"}', '--format=json']
    if name in ('opaque-repeat', 'concrete-control'):
        provider = 'identity_register' if extra_type else 'identity_bit'
        argv += ['--nat=k=2', f'--operation=U=main::{provider}']
    if name == 'opaque-repeat':
        argv += [f'--type=A={extra_type or "Bit"}']
    if name == 'opaque-forward':
        argv += [f'--module=provider={HERE / "providers" / "main.qli"}',
                 '--type=A=Bit', '--operation=U=provider::identity',
                 '--operation-type=U.B=Bit']
    log = OUT / f'{label}.native.jsonl'
    log.write_bytes(b'')
    env = dict(os.environ, QLEISLI_KERNEL=str(wrapper), QLEISLI_HIERARCHY_KERNEL=str(wrapper),
               QLEISLI_STUDY_NATIVE_LOG=str(log), QLEISLI_STUDY_NATIVE=str(NATIVE))
    start = time.monotonic()
    result = subprocess.run(argv, cwd=ROOT, env=env, capture_output=True, timeout=30)
    (OUT / f'{label}.stdout.txt').write_bytes(result.stdout)
    (OUT / f'{label}.stderr.txt').write_bytes(result.stderr)
    data = json.loads(result.stdout)
    count = len(log.read_text().splitlines())
    event = {
        'command': argv, 'exit_code': result.returncode,
        'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'timestamp_note': 'Clock observation after command completion, not authenticated provenance.',
        'stdout': data, 'native_invocations': count, 'seconds': time.monotonic() - start,
    }
    observation = f'observations/implementation-{label}.json'
    assert not (HERE / observation).exists()
    (HERE / observation).write_text(json.dumps(event, indent=2, ensure_ascii=False) + '\n')
    observations.append(observation)
    rows.append({'project': name, 'label': label, 'exit_code': result.returncode,
                 'native_invocations': count, 'codes': [d['code'] for d in data['diagnostics']]})
    print(rows[-1], flush=True)
stable = all(digest(HERE / p) == sha for p, sha in original.items())
stable &= digest(CLI) == identities['cli_sha256'] and digest(NATIVE) == identities['native_sha256']
stable &= all(digest(HERE / p) == sha for p, sha in identities['provider_files'].items())
result_record = {
    'identities': identities, 'sources_stable': stable, 'results': rows,
    'scope': 'Unchanged attempt-02 source; explicit type/provider bindings are new command inputs. '
             'Six abstract negatives reach generic type/access/ownership rules with no native call; '
             'forwarding, two exact repeat bases and the concrete control reach fresh native checking. '
             'No generic/source preservation theorem, guarantee admission or Issue closure.',
}
(OUT / 'result.json').write_text(json.dumps(result_record, indent=2) + '\n')
session = json.loads((HERE / 'session.json').read_text())
assert len(session['attempts']) == 2
session['attempts'][1]['observations'].extend(observations)
session['source_records'] = [{
    'id': 'separate-opaque-provider',
    'reason': 'Additional ordinary source for the unchanged opaque-forward client; explicit own B binding.',
    'sha256': {str(HERE.relative_to(ROOT) / p): sha for p, sha in identities['provider_files'].items()},
    'reports': ['implementation/result.json'],
}]
(HERE / 'session.json').write_text(json.dumps(session, indent=2) + '\n')
assert stable
for row in rows:
    positive = row['project'] in ('opaque-repeat', 'opaque-forward', 'concrete-control')
    assert row['exit_code'] == (0 if positive else 1), row
    assert row['native_invocations'] == (1 if positive else 0), row
