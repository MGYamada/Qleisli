"""Validate two prepared finite snapshots with a specified fixed AFTER binary.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
No command is read from a capture, no source is repaired, and no build is run.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
CLI = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
NATIVE = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
AFTER_CLI = '4c58a0b51360b99433ea75259967875c40d0caf872e2dc2981616c08d9c7db50'
EXPECTED_NATIVE = '39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def stamp():
    return datetime.now(timezone.utc).isoformat()


def write(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def identity(first, migration):
    assert digest(CLI) == AFTER_CLI, 'AFTER CLI changed'
    assert digest(NATIVE) == EXPECTED_NATIVE, 'native changed'
    for project in first['projects']:
        original = ROOT / 'corpus' / project['project']
        for file, sha in project['original_files'].items():
            assert digest(original / file) == sha, 'original root changed'
        for file, sha in project['selected_files'].items():
            if file.endswith('.qli'):
                assert digest(BASE / 'before-sources' / project['project'] / file) == sha
    for name, record in migration['files'].items():
        assert digest(BASE / 'sources' / name) == record['after'], 'prepared source changed'
    assert digest(ROOT / 'corpus/Qargo.toml') == first['shared_qargo_sha256']


def main():
    output = BASE / 'observations-after'
    assert not output.exists(), 'refuse overwrite'
    first = json.loads((BASE / 'first-sources.json').read_text())
    migration = json.loads((BASE / 'migration.pending.json').read_text())
    before = json.loads((BASE / 'observations-before/capture.json').read_text())
    identity(first, migration)
    output.mkdir()
    artifacts = output / 'artifacts'
    artifacts.mkdir()
    started = stamp()
    environment = os.environ.copy()
    environment['QLEISLI_KERNEL'] = str(NATIVE)
    results = []
    for name in migration['projects']:
        project = str(BASE / 'sources' / name)
        label = name.replace('/', '-')
        commands = [
            ('check', [str(CLI), 'check', project, '--format=json', '--lean-kernel=' + str(NATIVE)]),
            ('run', [str(CLI), 'run', project, '--format=json', '--lean-kernel=' + str(NATIVE)]),
            ('emit-ir', [str(CLI), 'emit-ir', project, '--output=' + str(artifacts / (label + '.qirf')), '--format=json', '--lean-kernel=' + str(NATIVE)]),
        ]
        for action, argv in commands:
            identity(first, migration)
            began = time.monotonic()
            completed = subprocess.run(argv, cwd=ROOT, env=environment, capture_output=True, timeout=60)
            elapsed = time.monotonic() - began
            identity(first, migration)
            stdout = output / (label + '-' + action + '.stdout.txt')
            stderr = output / (label + '-' + action + '.stderr.txt')
            stdout.write_bytes(completed.stdout)
            stderr.write_bytes(completed.stderr)
            parsed = json.loads(completed.stdout)
            assert parsed['format'] == 'qleisli.result' and parsed['version'] == 1
            result = {'project': name, 'action': action, 'argv': argv, 'cwd': str(ROOT),
                      'exit_code': completed.returncode, 'seconds': elapsed,
                      'recorded_utc': stamp(), 'stdout': completed.stdout.decode(),
                      'stderr': completed.stderr.decode(), 'parsed_stdout': parsed,
                      'raw_stdout': {'path': stdout.relative_to(BASE).as_posix(), 'sha256': digest(stdout)},
                      'raw_stderr': {'path': stderr.relative_to(BASE).as_posix(), 'sha256': digest(stderr)},
                      'identity_checked_before_and_after': True}
            write(output / (label + '-' + action + '.json'), result)
            results.append(result)
    comparisons = []
    for name in migration['projects']:
        label = name.replace('/', '-')
        old_run = next(r for r in before['results'] if r['project'] == name and r['action'] == 'run')
        new_run = next(r for r in results if r['project'] == name and r['action'] == 'run')
        old_ir = BASE / 'observations-before/artifacts' / (label + '.qirf')
        new_ir = artifacts / (label + '.qirf')
        comparisons.append({'project': name,
                            'parsed_default_distribution_equal': old_run['parsed_stdout'].get('result') == new_run['parsed_stdout'].get('result'),
                            'qirf_bytes_equal': new_ir.exists() and old_ir.read_bytes() == new_ir.read_bytes(),
                            'old_qirf_sha256': digest(old_ir),
                            'after_qirf_sha256': digest(new_ir) if new_ir.exists() else None,
                            'default_input_only': True})
    summary = {'format': 'qleisli.coherent-basis-corpus-after-observations', 'version': 1,
               'started_utc': started, 'ended_utc': stamp(),
               'binary': {'path': str(CLI), 'sha256': AFTER_CLI},
               'native': {'path': str(NATIVE), 'sha256': EXPECTED_NATIVE},
               'first_sources_sha256': digest(BASE / 'first-sources.json'),
               'before_capture_sha256': digest(BASE / 'observations-before/capture.json'),
               'sources': {name: record['after'] for name, record in migration['files'].items()},
               'results': results, 'comparisons': comparisons,
               'scope': 'Six actual AFTER commands, exact emitted IR bytes and parsed default distributions compared to fixed OLD. This is a bounded migration check; no universal source-preservation theorem, independent upstream oracle, Lean replay, build, maximum case or release validation.'}
    write(output / 'capture.json', summary)
    assert all(r['exit_code'] == 0 for r in results), 'AFTER commands failed; no selection'
    assert all(c['parsed_default_distribution_equal'] and c['qirf_bytes_equal'] for c in comparisons), 'comparison failed; no selection'
    checks = {'format': 'qleisli.coherent-basis-migration-checks', 'version': 1,
              'binary': summary['binary'], 'native': summary['native'], 'created_utc': stamp(),
              'sources': summary['sources'], 'results': [r for r in results if r['action'] == 'check'],
              'after_capture_sha256': digest(output / 'capture.json'),
              'comparisons': comparisons, 'scope': summary['scope']}
    write(BASE / 'checks.json', checks)
    print(json.dumps({'observations': len(results), 'all_commands_succeeded': True,
                      'comparisons': comparisons, 'capture_sha256': digest(output / 'capture.json'),
                      'checks_sha256': digest(BASE / 'checks.json')}, indent=2))


if __name__ == '__main__':
    main()
