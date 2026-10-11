"""Bounded actual observation of independently authored #80 first projects.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
Commands are constructed here; no recorded argv or unreviewed text is executed.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import time

REPOSITORY = Path('/Users/masa/git/Qleisli')
ROOT = REPOSITORY / 'tests/fixtures/authoring_sessions/functional-boundary-v030'
CLI = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
KERNEL = REPOSITORY / 'lean-kernel/.lake/build/bin/qleisli-kernel'
EXPECTED_CLI = 'bd9219f7847f1a7a52a3bd1346d39e8455edf0988e04582595471ae439b5feef'
EXPECTED_KERNEL = '39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85'
CASES = [
    'complete-call', 'partial-call', 'ordinary-local-callee',
    'quantum-unit-tuple-callee', 'quantum-unit-tuple-provider',
    'static-description-reuse', 'owner-duplication', 'classical-condition',
    'quantum-condition', 'explicit-observation',
]
POSITIVE_CASES = ['complete-call', 'static-description-reuse', 'classical-condition', 'explicit-observation']
FIRST = json.loads((ROOT / 'first-files.json').read_text())
OUTPUT = ROOT / 'observations-first'
OUTPUT.mkdir()
EVENTS = []


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json_new(path, value):
    with path.open('x', encoding='utf-8') as out:
        out.write(json.dumps(value, indent=2) + '\n')


def identity():
    observed = {'cli': {'path': str(CLI), 'sha256': sha(CLI)},
                'kernel': {'path': str(KERNEL), 'sha256': sha(KERNEL)}}
    if observed['cli']['sha256'] != EXPECTED_CLI or observed['kernel']['sha256'] != EXPECTED_KERNEL:
        raise RuntimeError('fixed executable identity changed')
    for name, expected in FIRST['files'].items():
        if sha(ROOT / name) != expected:
            raise RuntimeError('first source/context/prediction changed: ' + name)
    return observed


def observe(case, mode, verb='check', text=False):
    before = identity()
    project = ROOT / 'attempt-01' / case
    command = [str(CLI), verb]
    if mode == 'sized':
        command.append('--sized')
    command.append(str(project))
    if not text:
        command.append('--format=json')
    ident = case + '-' + mode + '-' + verb + ('-text' if text else '-json')
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    began = time.monotonic()
    env = os.environ.copy()
    env['QLEISLI_KERNEL'] = str(KERNEL)
    result = subprocess.run(command, cwd=REPOSITORY, env=env, capture_output=True, timeout=30)
    elapsed = time.monotonic() - began
    end = datetime.datetime.now(datetime.timezone.utc).isoformat()
    for stream, data in [('stdout', result.stdout), ('stderr', result.stderr)]:
        with (OUTPUT / (ident + '.' + stream + '.txt')).open('xb') as out:
            out.write(data)
    # Preserve real outputs/exit even if the post-command executable check fails.
    after = {'cli': {'path': str(CLI), 'sha256': sha(CLI)},
             'kernel': {'path': str(KERNEL), 'sha256': sha(KERNEL)}}
    stable = before == after
    event = {
        'command': command, 'cwd': str(REPOSITORY),
        'environment_overrides': {'QLEISLI_KERNEL': str(KERNEL)},
        'case': case, 'mode': mode, 'exit_code': result.returncode,
        'started_utc': start, 'recorded_utc': end, 'seconds': elapsed,
        'binary_before': before, 'binary_after': after, 'binary_identity_stable': stable,
        'source_sha256': sha(project / 'main.qli'), 'manifest_sha256': sha(project / 'Qargo.toml'),
        'raw_streams': {
            stream: {'path': str((OUTPUT / (ident + '.' + stream + '.txt')).relative_to(ROOT)),
                     'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}
            for stream, data in [('stdout', result.stdout), ('stderr', result.stderr)]
        },
        'scope': 'Actual bounded public CLI observation. Native selected bytes recorded, not child-start/completion attestation or source/runtime theorem.',
    }
    try:
        parsed = json.loads(result.stdout)
    except (ValueError, UnicodeDecodeError):
        parsed = None
    if isinstance(parsed, dict) and parsed.get('format') == 'qleisli.result':
        event['stdout'] = parsed
    else:
        event['transcript'] = 'stdout:\n' + result.stdout.decode('utf-8', errors='replace') + '\nstderr:\n' + result.stderr.decode('utf-8', errors='replace')
    path = OUTPUT / (ident + '.json')
    write_json_new(path, event)
    EVENTS.append(str(path.relative_to(ROOT)))
    if not stable:
        raise RuntimeError('post-command executable identity changed; original result retained')
    identity()
    detail = parsed.get('diagnostics', []) if isinstance(parsed, dict) else event['transcript']
    print(json.dumps({'case': case, 'mode': mode, 'verb': verb, 'text': text,
                      'exit': result.returncode, 'outcome': parsed.get('outcome') if isinstance(parsed, dict) else None,
                      'diagnostics': detail}, ensure_ascii=False), flush=True)
    return result.returncode


for case in CASES:
    observe(case, 'finite')
    observe(case, 'sized')
for case in ['partial-call', 'ordinary-local-callee']:
    observe(case, 'finite', text=True)
    observe(case, 'sized', text=True)
for case in POSITIVE_CASES:
    check = json.loads((OUTPUT / (case + '-finite-check-json.json')).read_text())
    if check['exit_code'] == 0:
        observe(case, 'finite', verb='run')
    else:
        print('Skipping execution after actual rejected positive: ' + case, flush=True)
write_json_new(OUTPUT / 'capture.json', {
    'format': 'qleisli.informed-public-source-capture', 'version': 1,
    'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'actual_observations': EVENTS,
    'first_inventory_sha256': sha(ROOT / 'first-files.json'),
    'prediction_sha256': sha(ROOT / 'predictions-before.json'),
    'pending_session_sha256': sha(ROOT / 'session.pending.json'),
    'observer_sha256': sha(Path(__file__)),
    'scope': 'Original first outcomes retained; no commands taken from captured records, no source changes or builds.',
})
print(json.dumps({'observations': len(EVENTS), 'binary_final': identity()}), flush=True)
