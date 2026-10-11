#!/usr/bin/env python3
"""Read retained bounded observations; never execute recorded commands.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""

import hashlib
import json
from pathlib import Path


root = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


first = json.loads((root / 'first-files.json').read_text())['files']
for path, expected in first.items():
    assert digest(root / path) == expected, path
session = json.loads((root / 'session.json').read_text())
phases = ['before', 'after-visibility-repair', 'after-import-repair']
identities = [json.loads((root / phase / 'identity.json').read_text())
              for phase in phases]
assert all(identity == identities[0] for identity in identities), 'identity drift'
cases = json.loads((root / 'cases.json').read_text())
rows = []
for attempt, phase in zip(session['attempts'], phases, strict=True):
    assert len(attempt['observations']) == 24
    for name in sorted(cases):
        observations = []
        for format_name in ['text', 'json']:
            stem = f'{name}-{format_name}'
            raw_path = root / phase / f'{stem}.json'
            event = json.loads(raw_path.read_text())
            recorded_path = root / phase / (
                f'{stem}.record.json' if phase == 'before' else f'{stem}.json')
            assert str(recorded_path.relative_to(root)) in attempt['observations']
            recorded = json.loads(recorded_path.read_text())
            if phase == 'before':
                assert recorded['raw_event']['path'] == str(raw_path.relative_to(root))
                assert recorded['raw_event']['sha256'] == digest(raw_path)
                assert recorded['exit_code'] == event['exit_code']
            out = (root / phase / f'{stem}.stdout.txt').read_text()
            err = (root / phase / f'{stem}.stderr.txt').read_text()
            assert err == event['stderr']
            native_count = len((root / phase / f'{stem}.native.jsonl')
                               .read_text().splitlines())
            assert native_count == event['native_invocations']
            if format_name == 'json':
                assert json.loads(out) == event['stdout']
                assert not err
                result = event['stdout']
                assert (result['outcome'] == 'ok') == (event['exit_code'] == 0)
                code = None if event['exit_code'] == 0 else result['diagnostics'][0]['code']
                message = None if event['exit_code'] == 0 else result['diagnostics'][0]['message']
            else:
                assert out + err == event['transcript']
            observations.append({'format': format_name,
                'exit_code': event['exit_code'], 'native_invocations': native_count,
                'record': str(recorded_path.relative_to(root)),
                'raw_event_sha256': digest(raw_path)})
        assert observations[0]['exit_code'] == observations[1]['exit_code']
        assert observations[0]['native_invocations'] == observations[1]['native_invocations']
        rows.append({'attempt': attempt['id'], 'project': name,
            'diagnostic_code': code, 'message': message, 'observations': observations})

summary = {'format': 'qleisli.operator-arrow-first-study', 'version': 1,
    'baseline_commit': session['baseline_commit'], 'project_version': '0.3.0-alpha',
    'edition': '2026', 'first_files_sha256': digest(root / 'first-files.json'),
    'source_count_per_attempt': 12, 'observation_count': 72,
    'final_native_successes': sum(row['observations'][0]['exit_code'] == 0
                                 for row in rows if row['attempt'] == 'attempt-03'),
    'identity': identities[0], 'rows': rows,
    'limits': 'Checks only. Parser rejection does not validate later semantics; native check success does not prove general source preservation, exact scalar action or the full instrument. No operator-arrow syntax, external effect justification, new primitive, guarantee or constitutional interpretation is adopted.'}
target = root / 'summary.json'
assert not target.exists(), 'preserve the preceding summary'
target.write_text(json.dumps(summary, indent=2) + '\n')
print('Verified 24 original source/manifest hashes and 72 raw observations; final 5 native successes and 7 rejections per output format.')
