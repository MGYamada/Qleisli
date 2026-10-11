"""Record the fixed pre-code CLI on untouched informed #82 first sources.

The command list is authored here; observation records are never replayed.
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
EXPECTED_CLI = '4c58a0b51360b99433ea75259967875c40d0caf872e2dc2981616c08d9c7db50'
EXPECTED_NATIVE = '39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def stamp():
    return datetime.now(timezone.utc).isoformat()


def identity(first, frozen):
    assert sha(CLI) == EXPECTED_CLI, 'CLI identity changed'
    assert sha(NATIVE) == EXPECTED_NATIVE, 'native identity changed'
    for name, expected in frozen.items():
        assert sha(BASE / name) == expected, 'frozen record changed: ' + name
    for name, expected in first['files'].items():
        assert sha(BASE / 'attempt-01' / name) == expected, 'first source changed: ' + name


def main():
    output = BASE / 'observations-before'
    assert not output.exists(), 'Refusing to overwrite first observations'
    assert not (BASE / 'session.json').exists(), 'Refusing to overwrite session'
    first = json.loads((BASE / 'first-files.json').read_text())
    frozen = {name: sha(BASE / name) for name in ('first-files.json', 'session.pending.json', 'context.md')}
    identity(first, frozen)
    output.mkdir()
    artifacts = output / 'artifacts'
    artifacts.mkdir()
    environment = os.environ.copy()
    environment['QLEISLI_KERNEL'] = str(NATIVE)
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    observations = []
    started = stamp()
    for case in first['cases']:
        name = case['id']
        project = BASE / 'attempt-01' / name
        commands = [('finite-check-json', [str(CLI), 'check', str(project), '--format=json', '--lean-kernel=' + str(NATIVE)], 'json')]
        if case['pair'] in ('providers-reference-control', 'wrong-phase'):
            commands.append(('finite-check-text', [str(CLI), 'check', str(project), '--format=text', '--lean-kernel=' + str(NATIVE)], 'text'))
        if case['pair'] == 'providers-reference-control':
            commands.append(('public-selected-check-json', [str(CLI), 'check', '--entry=main::probe', '--module=main=' + str(project / 'main.qli'), '--format=json', '--lean-kernel=' + str(NATIVE)], 'json'))
        if case['spelling'] == 'legacy' and case['oracle'] is not None:
            commands.extend([
                ('finite-run-json', [str(CLI), 'run', str(project), '--format=json', '--lean-kernel=' + str(NATIVE)], 'json'),
                ('finite-emit-ir-json', [str(CLI), 'emit-ir', str(project), '--output=' + str(artifacts / (name + '.qirf')), '--format=json', '--lean-kernel=' + str(NATIVE)], 'json'),
            ])
        for action, argv, format_name in commands:
            identity(first, frozen)
            began = time.monotonic()
            timed_out = False
            try:
                completed = subprocess.run(argv, cwd=ROOT, env=environment, capture_output=True, timeout=45)
                stdout, stderr, exit_code = completed.stdout, completed.stderr, completed.returncode
            except subprocess.TimeoutExpired as error:
                stdout, stderr, exit_code = error.stdout or b'', error.stderr or b'', None
                timed_out = True
            seconds = time.monotonic() - began
            identity(first, frozen)
            stem = name + '-' + action
            stdout_path = output / (stem + '.stdout.txt')
            stderr_path = output / (stem + '.stderr.txt')
            stdout_path.write_bytes(stdout)
            stderr_path.write_bytes(stderr)
            event = {
                'command': argv, 'exit_code': exit_code, 'timed_out': timed_out,
                'recorded_utc': stamp(), 'elapsed_seconds': seconds, 'cwd': str(ROOT),
                'case': name, 'action': action, 'output_format': format_name,
                'cli': {'path': str(CLI), 'sha256': EXPECTED_CLI},
                'native_selection': {'path': str(NATIVE), 'sha256': EXPECTED_NATIVE},
                'source_sha256': sha(project / 'main.qli'),
                'manifest_sha256': sha(project / 'Qargo.toml'),
                'raw_stdout': {'path': stdout_path.relative_to(BASE).as_posix(), 'sha256': sha(stdout_path)},
                'raw_stderr': {'path': stderr_path.relative_to(BASE).as_posix(), 'sha256': sha(stderr_path)},
                'identity_checked_before_and_after': True,
                'attestation_limit': 'Explicit selected executable bytes; no compiled-HEAD claim, independent native child-start/exit count, source preservation or Lean replay.'
            }
            if format_name == 'json' and not timed_out:
                parsed = json.loads(stdout.decode('utf-8'))
                assert parsed['format'] == 'qleisli.result' and parsed['version'] == 1
                event['stdout'] = parsed
            elif format_name == 'text':
                event['stdout_text'] = stdout.decode('utf-8')
                event['stderr_text'] = stderr.decode('utf-8')
            event_path = output / (stem + '.json')
            write(event_path, event)
            observations.append(event_path.relative_to(BASE).as_posix())
            print(json.dumps({'case': name, 'action': action, 'exit': exit_code, 'timed_out': timed_out, 'seconds': round(seconds, 3)}), flush=True)
            assert len(stdout) + len(stderr) < 1048576, 'Unexpectedly large streams; already preserved'
            assert not timed_out, 'First timeout preserved; do not invent later results'
    identity(first, frozen)
    emitted = {p.relative_to(BASE).as_posix(): {'sha256': sha(p), 'bytes': p.stat().st_size} for p in sorted(artifacts.iterdir())}
    assert all(info['bytes'] < 1048576 for info in emitted.values()), 'Unexpectedly large artifact'
    capture = {
        'format': 'qleisli.checked-operation-first-capture', 'version': 1,
        'baseline_checkout': first['baseline_commit'], 'started_utc': started, 'ended_utc': stamp(),
        'cli_sha256': EXPECTED_CLI, 'native_sha256': EXPECTED_NATIVE,
        'driver_sha256': sha(Path(__file__)), 'frozen_record_sha256': frozen,
        'source_and_executable_identities_unchanged': True,
        'observations': observations, 'artifacts': emitted,
        'scope': 'Actual fixed pre-code commands on unchanged first sources. Desired spelling parse refusals validate no downstream rule. No source repair, compiler rebuild, independent numerical oracle execution, Lean replay, guarantee/Issue/release completion.'
    }
    write(output / 'capture.json', capture)
    session = json.loads((BASE / 'session.pending.json').read_text())
    session['record_status'] = 'actual-before-observations-registered'
    session['attempts'][0]['observations'] = observations
    session['reports'] += ['observations-before/capture.json']
    session['registration'] = {'recorded_utc': stamp(), 'pending_file': 'session.pending.json',
                               'pending_sha256': frozen['session.pending.json'],
                               'actual_capture': 'observations-before/capture.json',
                               'capture_sha256': sha(output / 'capture.json')}
    write(BASE / 'session.json', session)
    print(json.dumps({'completed': len(observations), 'artifacts': emitted,
                      'capture_sha256': sha(output / 'capture.json'),
                      'session_sha256': sha(BASE / 'session.json')}), flush=True)


if __name__ == '__main__':
    main()
