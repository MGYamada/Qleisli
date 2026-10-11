"""Capture the fixed pre-code executable on frozen informed #81 sources.

This is an authored observation driver, never a replay of recorded commands.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
BASE = Path(__file__).resolve().parent
CLI = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
NATIVE = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
EXPECTED_CLI = 'a7c2b2d387dc0c3ae360b047ff433abb7e341cc21c8a9aefbfe8b5056c791ae8'
EXPECTED_NATIVE = '39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')


def stamp():
    return datetime.now(timezone.utc).isoformat()


def identity(first):
    assert digest(CLI) == EXPECTED_CLI, 'CLI identity changed'
    assert digest(NATIVE) == EXPECTED_NATIVE, 'native identity changed'
    for name, sha in first['files'].items():
        assert digest(BASE / 'attempt-01' / name) == sha, 'source identity changed: ' + name


def main():
    output = BASE / 'observations-before'
    assert not output.exists(), 'Refusing to overwrite first observations'
    first = json.loads((BASE / 'first-files.json').read_text())
    identity(first)
    output.mkdir()
    artifacts = output / 'artifacts'
    artifacts.mkdir()
    started = stamp()
    environment = os.environ.copy()
    environment['QLEISLI_KERNEL'] = str(NATIVE)
    observations = []
    for case in first['cases']:
        case_id = case['id']
        project = BASE / 'attempt-01' / case_id
        commands = [
            ('finite-check', [str(CLI), 'check', str(project), '--format=json', '--lean-kernel=' + str(NATIVE)]),
            ('selected-check', [str(CLI), 'check', '--entry=main::main', '--module=main=' + str(project / 'main.qli'), '--format=json', '--lean-kernel=' + str(NATIVE)]),
        ]
        if case['spelling'] == 'legacy' and case['oracle'] is not None:
            commands += [
                ('finite-run', [str(CLI), 'run', str(project), '--format=json', '--lean-kernel=' + str(NATIVE)]),
                ('finite-emit-ir', [str(CLI), 'emit-ir', str(project), '--output=' + str(artifacts / (case_id + '.qirf')), '--format=json', '--lean-kernel=' + str(NATIVE)]),
            ]
        for action, command in commands:
            identity(first)
            began = time.monotonic()
            completed = subprocess.run(command, cwd=ROOT, env=environment, capture_output=True, timeout=60)
            elapsed = time.monotonic() - began
            identity(first)
            name = case_id + '-' + action
            stdout_file = output / (name + '.stdout.txt')
            stderr_file = output / (name + '.stderr.txt')
            stdout_file.write_bytes(completed.stdout)
            stderr_file.write_bytes(completed.stderr)
            event = {
                'command': command,
                'exit_code': completed.returncode,
                'recorded_utc': stamp(),
                'elapsed_seconds': elapsed,
                'case': case_id,
                'action': action,
                'cwd': str(ROOT),
                'cli': {'path': str(CLI), 'sha256': EXPECTED_CLI},
                'native_selection': {'path': str(NATIVE), 'sha256': EXPECTED_NATIVE},
                'source_sha256': digest(project / 'main.qli'),
                'raw_stdout': {'path': str(stdout_file.relative_to(BASE)), 'sha256': digest(stdout_file)},
                'raw_stderr': {'path': str(stderr_file.relative_to(BASE)), 'sha256': digest(stderr_file)},
                'identity_checked_before_and_after': True,
                'native_attestation_limit': 'Explicit selected bytes are checked; native child start/exit counts and compiled-HEAD correspondence are not independently attested.'
            }
            decoded = completed.stdout.decode('utf-8')
            parsed = json.loads(decoded)
            assert parsed['format'] == 'qleisli.result' and parsed['version'] == 1
            event['stdout'] = parsed
            write(output / (name + '.json'), event)
            observations.append(str((output / (name + '.json')).relative_to(BASE)))
    identity(first)
    captured_artifacts = {str(p.relative_to(BASE)): {'sha256': digest(p), 'bytes': p.stat().st_size} for p in sorted(artifacts.iterdir())}
    assert all(info['bytes'] < 1048576 for info in captured_artifacts.values()), 'unexpectedly large emitted artifact'
    summary = {'format': 'qleisli.coherent-basis-first-capture', 'version': 1,
               'baseline_checkout': first['baseline_commit'], 'started_utc': started, 'ended_utc': stamp(),
               'cli_sha256': EXPECTED_CLI, 'native_sha256': EXPECTED_NATIVE,
               'pending_record_sha256': digest(BASE / 'session.pending.json'),
               'first_sources_sha256': digest(BASE / 'first-files.json'),
               'source_and_executable_identities_unchanged': True,
               'observations': observations, 'artifacts': captured_artifacts,
               'scope': 'Actual fixed pre-code commands. No source repair, rebuilt CLI, numerical oracle invocation, Lean replay, guarantee admission or completion claim.'}
    write(output / 'capture.json', summary)
    session = json.loads((BASE / 'session.pending.json').read_text())
    session['record_status'] = 'actual-before-observations-registered'
    session['attempts'][0]['observations'] = observations
    session['reports'] += ['observations-before/capture.json']
    session['registration'] = {'recorded_utc': stamp(), 'pending_file': 'session.pending.json', 'pending_sha256': summary['pending_record_sha256'], 'actual_capture': 'observations-before/capture.json', 'capture_sha256': digest(output / 'capture.json')}
    write(BASE / 'session.json', session)
    results = []
    for relative in observations:
        event = json.loads((BASE / relative).read_text())
        results.append({'case': event['case'], 'action': event['action'], 'exit': event['exit_code'], 'outcome': event['stdout']['outcome']})
    print(json.dumps({'observations': len(observations), 'results': results, 'artifacts': captured_artifacts, 'session_sha256': digest(BASE / 'session.json'), 'capture_sha256': digest(output / 'capture.json')}, indent=2))


if __name__ == '__main__':
    main()
