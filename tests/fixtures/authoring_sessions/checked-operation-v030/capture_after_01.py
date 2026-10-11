"""Capture authored bounded #82 commands on unchanged first sources.

No observation command is replayed. A parent-supplied after CLI digest is required.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
BASE = Path(__file__).resolve().parent
NATIVE = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
EXPECTED_NATIVE = '39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    assert not path.exists(), 'Refusing to overwrite actual record: ' + str(path)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def stamp():
    return datetime.now(timezone.utc).isoformat()


def ports(artifact):
    keys = ('quantum_inputs', 'quantum_outputs', 'classical_inputs',
            'classical_outputs', 'declared_effect')
    return {'root_interface': artifact['root_interface'], 'root': artifact['root'],
            'program_ports': [{key: program[key] for key in keys}
                              for program in artifact['programs']],
            'evidence_signatures': [item['signature'] for item in artifact['evidence']]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cli', required=True, type=Path)
    parser.add_argument('--cli-sha256', required=True)
    args = parser.parse_args()
    assert re.fullmatch('[0-9a-f]{64}', args.cli_sha256), 'Expected exact SHA-256'
    cli = args.cli.resolve(strict=True)
    output = BASE / 'observations-after-01'
    assert not output.exists(), 'Refusing to overwrite first AFTER observations'
    first = json.loads((BASE / 'first-files.json').read_text())
    pending = json.loads((BASE / 'after.pending-01.json').read_text())
    frozen = json.loads((BASE / 'after-baseline-files-01.json').read_text())['files']
    prepared = {name: sha(BASE / name) for name in
                ('after.pending-01.json', 'after-contract-01.md',
                 'after-baseline-files-01.json', 'capture_after_01.py')}

    def identity():
        assert sha(cli) == args.cli_sha256, 'After CLI identity changed'
        assert sha(NATIVE) == EXPECTED_NATIVE, 'Native identity changed'
        for name, digest in frozen.items():
            assert sha(BASE / name) == digest, 'Immutable baseline changed: ' + name
        for name, digest in prepared.items():
            assert sha(BASE / name) == digest, 'Prepared expectation changed: ' + name

    identity()
    output.mkdir()
    artifacts = output / 'artifacts'
    artifacts.mkdir()
    environment = os.environ.copy()
    environment['QLEISLI_KERNEL'] = str(NATIVE)
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    events = []
    assertions = []
    started = stamp()
    for case in first['cases']:
        name = case['id']
        project = BASE / 'attempt-01' / name
        commands = [('finite-check-json', [str(cli), 'check', str(project),
                     '--format=json', '--lean-kernel=' + str(NATIVE)], 'json')]
        if case['pair'] in ('providers-reference-control', 'wrong-phase'):
            commands.append(('default-text-check', [str(cli), 'check', str(project),
                             '--lean-kernel=' + str(NATIVE)], 'text'))
        if case['public_selected_entry']:
            commands.append(('public-selected-check-json', [str(cli), 'check',
                             '--entry=main::probe', '--module=main=' + str(project / 'main.qli'),
                             '--format=json', '--lean-kernel=' + str(NATIVE)], 'json'))
        if case['spelling'] == 'desired' and case['oracle'] is not None:
            commands.extend([
                ('finite-run-json', [str(cli), 'run', str(project), '--format=json',
                                     '--lean-kernel=' + str(NATIVE)], 'json'),
                ('finite-emit-ir-json', [str(cli), 'emit-ir', str(project),
                     '--output=' + str(artifacts / (name + '.qirf')), '--format=json',
                     '--lean-kernel=' + str(NATIVE)], 'json')])
        for action, argv, format_name in commands:
            identity()
            began = time.monotonic()
            timed_out = False
            try:
                completed = subprocess.run(argv, cwd=ROOT, env=environment,
                                           capture_output=True, timeout=45)
                stdout, stderr, exit_code = completed.stdout, completed.stderr, completed.returncode
            except subprocess.TimeoutExpired as error:
                stdout, stderr, exit_code = error.stdout or b'', error.stderr or b'', None
                timed_out = True
            seconds = time.monotonic() - began
            stem = name + '-' + action
            stdout_path = output / (stem + '.stdout.txt')
            stderr_path = output / (stem + '.stderr.txt')
            stdout_path.write_bytes(stdout)
            stderr_path.write_bytes(stderr)
            event = {'command': argv, 'exit_code': exit_code, 'timed_out': timed_out,
                     'recorded_utc': stamp(), 'elapsed_seconds': seconds, 'cwd': str(ROOT),
                     'case': name, 'action': action, 'output_format': format_name,
                     'cli': {'path': str(cli), 'sha256': args.cli_sha256},
                     'native_selection': {'path': str(NATIVE), 'sha256': EXPECTED_NATIVE},
                     'source_sha256': sha(project / 'main.qli'),
                     'manifest_sha256': sha(project / 'Qargo.toml'),
                     'raw_stdout': {'path': stdout_path.relative_to(BASE).as_posix(),
                                    'sha256': sha(stdout_path)},
                     'raw_stderr': {'path': stderr_path.relative_to(BASE).as_posix(),
                                    'sha256': sha(stderr_path)},
                     'transcript': 'stdout:\n' + stdout.decode('utf-8', errors='replace')
                                   + '\nstderr:\n' + stderr.decode('utf-8', errors='replace'),
                     'attestation_limit': 'Selected bytes, not compiled-HEAD or native-child attestation.'}
            try:
                identity()
                event['identity_checked_before_and_after'] = True
            except (AssertionError, OSError) as error:
                event['identity_checked_before_and_after'] = False
                event['identity_error'] = str(error)
            if format_name == 'json' and not timed_out:
                try:
                    parsed = json.loads(stdout.decode('utf-8'))
                    assert parsed['format'] == 'qleisli.result' and parsed['version'] == 1
                    event['stdout'] = parsed
                except (ValueError, KeyError, AssertionError) as error:
                    event['json_output_error'] = str(error)
            event_path = output / (stem + '.json')
            write(event_path, event)
            events.append(event_path.relative_to(BASE).as_posix())
            expected = pending['cases'][name]
            parsed = event.get('stdout', {})
            diagnostics = parsed.get('diagnostics', [])
            text = event['transcript']
            if case['spelling'] == 'legacy':
                matched = exit_code == 1 and 'bind_op' in text and 'checked_op' in text
                if format_name == 'json':
                    matched = matched and bool(diagnostics) and diagnostics[0]['code'] == 'parse'
                    primary = diagnostics[0].get('primary') or {}
                    matched = matched and primary.get('start') == expected['first_legacy_token_start']
                    matched = matched and primary.get('end') == expected['first_legacy_token_end']
            elif action == 'public-selected-check-json':
                matched = exit_code == 1 and bool(diagnostics) and diagnostics[0]['code'] == 'unsupported'
                matched = matched and 'unsupported static operation constructor' in text
            elif action == 'finite-run-json':
                distribution = {''.join('1' if bit else '0' for bit in item['bits']): item['probability']
                                for item in (parsed.get('result') or {}).get('distribution', [])}
                matched = exit_code == 0 and distribution == expected['distribution']
            elif action == 'finite-emit-ir-json':
                matched = exit_code == 0 and (artifacts / (name + '.qirf')).is_file()
            elif expected['finite_exit'] == 0:
                matched = exit_code == 0
            else:
                matched = exit_code == 1
                if format_name == 'json':
                    matched = matched and bool(diagnostics) and diagnostics[0]['code'] == expected['code']
                matched = matched and all(part in text for part in expected['message_fragments'])
            assertions.append({'case': name, 'action': action, 'prediction_matched': bool(matched),
                               'observation': event_path.relative_to(BASE).as_posix()})
            print(json.dumps({'case': name, 'action': action, 'exit': exit_code,
                              'prediction_matched': bool(matched), 'seconds': round(seconds, 3)}), flush=True)
            assert not timed_out, 'First timeout preserved; no invented completion'
            assert event['identity_checked_before_and_after'], 'Identity failure preserved'
            assert len(stdout) + len(stderr) < 1048576, 'Unexpected stream size, already preserved'
    identity()
    emitted = {}
    for path in sorted(artifacts.iterdir()):
        case_name = path.stem
        legacy_name = case_name.removesuffix('-desired') + '-legacy.qirf'
        before_path = BASE / 'observations-before/artifacts' / legacy_name
        before = json.loads(before_path.read_text())
        after = json.loads(path.read_text())
        comparison = {'before_sha256': sha(before_path), 'after_sha256': sha(path),
                      'ordered_ports_equal': ports(before) == ports(after),
                      'before_ports': ports(before), 'after_ports': ports(after),
                      'source_identity_note': 'Whole QIRF equality not required; no identities stripped or rewritten.'}
        emitted[path.relative_to(BASE).as_posix()] = comparison
        assertions.append({'case': case_name, 'action': 'ordered-ports-comparison',
                           'prediction_matched': comparison['ordered_ports_equal']})
        assert path.stat().st_size < 1048576, 'Unexpected artifact size, already preserved'
    capture = {'format': 'qleisli.checked-operation-after-capture', 'version': 1,
               'started_utc': started, 'ended_utc': stamp(), 'cli_sha256': args.cli_sha256,
               'native_sha256': EXPECTED_NATIVE, 'prepared_record_sha256': prepared,
               'immutable_before_inventory': 'after-baseline-files-01.json',
               'observations': events, 'artifacts': emitted, 'assertions': assertions,
               'scope': 'Actual bounded first-source checks/run/emission and literal predictions. '
                        'No source repairs, independent numerical oracle, native-child attestation, '
                        'fresh Lean replay, general theorem, guarantee/Issue/release completion.'}
    write(output / 'capture.json', capture)
    session = json.loads((BASE / 'session.json').read_text())
    session['record_status'] = 'actual-before-and-after-observations-registered'
    session['attempts'][0]['observations'].extend(events)
    session['reports'].extend(['after.pending-01.json', 'after-baseline-files-01.json',
                               'observations-after-01/capture.json'])
    session['after_registration'] = {'recorded_utc': stamp(),
                                    'before_session': 'session-before-after-01.json',
                                    'before_session_sha256': sha(BASE / 'session-before-after-01.json'),
                                    'capture_sha256': sha(output / 'capture.json')}
    (BASE / 'session.json').write_text(json.dumps(session, indent=2, ensure_ascii=False) + '\n')
    spec = importlib.util.spec_from_file_location('authoring_integrity', ROOT / 'scripts/check_authoring_sessions.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    registration = {'format': 'qleisli.authoring-metadata-integrity-observation', 'version': 1,
                    'recorded_utc': stamp(), 'session_sha256': sha(BASE / 'session.json'),
                    'method': 'Pure check_session for this session; no recorded command execution'}
    try:
        snapshots, observations = module.check_session(BASE / 'session.json')
        registration.update(exit_code=0, result={'snapshots': snapshots, 'observations': observations})
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        registration.update(exit_code=1, error=str(error))
    write(BASE / 'metadata-check-after-capture-01.json', registration)
    print(json.dumps({'completed': len(events), 'assertions': len(assertions),
                      'failed_predictions': sum(not item['prediction_matched'] for item in assertions),
                      'registration': registration, 'capture_sha256': sha(output / 'capture.json')}), flush=True)


if __name__ == '__main__':
    main()
