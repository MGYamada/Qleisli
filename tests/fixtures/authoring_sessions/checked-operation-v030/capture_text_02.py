"""Append real default-text observations after a preserved observer flag error.

Do not rewrite sources, the original capture, driver or registered session.
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


def main():
    output = BASE / 'observations-before'
    summary_path = output / 'default-text-capture-02.json'
    assert not summary_path.exists(), 'Refusing to overwrite text supplement'
    first = json.loads((BASE / 'first-files.json').read_text())
    frozen_names = ['first-files.json', 'session.pending.json', 'session.json',
                    'context.md', 'capture_before.py', 'observations-before/capture.json']
    frozen = {name: sha(BASE / name) for name in frozen_names}

    def identity():
        assert sha(CLI) == EXPECTED_CLI and sha(NATIVE) == EXPECTED_NATIVE
        for name, expected in frozen.items():
            assert sha(BASE / name) == expected, 'frozen capture changed: ' + name
        for name, expected in first['files'].items():
            assert sha(BASE / 'attempt-01' / name) == expected, 'first source changed: ' + name

    identity()
    prediction_path = output / 'default-text-predictions-02.json'
    assert not prediction_path.exists(), 'Refusing to overwrite predictions'
    cases = [('providers-reference-control-desired', 1, 'new name parse refusal'),
             ('providers-reference-control-legacy', 0, 'existing exact providers accepted'),
             ('wrong-phase-desired', 1, 'new name parse refusal, no downstream check'),
             ('wrong-phase-legacy', 1, 'exact Meaning equality refusal')]
    write(prediction_path, {'recorded_utc': stamp(), 'cases': cases,
                            'reason': 'The first authored --format=text calls were invalid usage. The CLI help permits --format=json; omission uses its existing text output. Original calls/failures stay unchanged.',
                            'frozen_record_sha256': frozen})
    environment = os.environ.copy()
    environment['QLEISLI_KERNEL'] = str(NATIVE)
    observations = []
    for case, expected_exit, prediction in cases:
        project = BASE / 'attempt-01' / case
        argv = [str(CLI), 'check', str(project), '--lean-kernel=' + str(NATIVE)]
        identity()
        began = time.monotonic()
        completed = subprocess.run(argv, cwd=ROOT, env=environment, capture_output=True, timeout=45)
        identity()
        stem = case + '-default-text-02'
        stdout_path = output / (stem + '.stdout.txt')
        stderr_path = output / (stem + '.stderr.txt')
        stdout_path.write_bytes(completed.stdout)
        stderr_path.write_bytes(completed.stderr)
        event = {'command': argv, 'exit_code': completed.returncode, 'recorded_utc': stamp(),
                 'elapsed_seconds': time.monotonic() - began, 'cwd': str(ROOT),
                 'case': case, 'action': 'default-text-check-02', 'output_format': 'default-text',
                 'cli': {'path': str(CLI), 'sha256': EXPECTED_CLI},
                 'native_selection': {'path': str(NATIVE), 'sha256': EXPECTED_NATIVE},
                 'source_sha256': sha(project / 'main.qli'), 'manifest_sha256': sha(project / 'Qargo.toml'),
                 'raw_stdout': {'path': stdout_path.relative_to(BASE).as_posix(), 'sha256': sha(stdout_path)},
                 'raw_stderr': {'path': stderr_path.relative_to(BASE).as_posix(), 'sha256': sha(stderr_path)},
                 'stdout_text': completed.stdout.decode('utf-8'), 'stderr_text': completed.stderr.decode('utf-8'),
                 'identity_checked_before_and_after': True, 'prediction': prediction,
                 'prediction_matched': completed.returncode == expected_exit,
                 'scope': 'Separate authored default-text command, not source repair or replay of an observation.'}
        event_path = output / (stem + '.json')
        write(event_path, event)
        observations.append(event_path.relative_to(BASE).as_posix())
        print(json.dumps({'case': case, 'exit': completed.returncode, 'prediction_matched': event['prediction_matched']}), flush=True)
    identity()
    write(summary_path, {'format': 'qleisli.checked-operation-default-text-supplement', 'version': 1,
                         'recorded_utc': stamp(), 'driver_sha256': sha(Path(__file__)),
                         'first_capture_sha256': frozen['observations-before/capture.json'],
                         'predictions': {'path': prediction_path.relative_to(BASE).as_posix(), 'sha256': sha(prediction_path)},
                         'frozen_record_sha256': frozen, 'observations': observations,
                         'source_and_executable_identities_unchanged': True,
                         'scope': 'Four additional real text commands. Four original invalid-flag usage failures remain. No source repair, compiler change/build, oracle execution, Lean replay, guarantee/Issue/release completion.'})
    print(json.dumps({'supplement_sha256': sha(summary_path), 'observations': len(observations)}))


if __name__ == '__main__':
    main()
