"""Record fixed OLD commands on two frozen finite corpus projects.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
No recorded command is replayed, no source is repaired, and no build is run.
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
OLD_CLI = 'a7c2b2d387dc0c3ae360b047ff433abb7e341cc21c8a9aefbfe8b5056c791ae8'
OLD_NATIVE = '39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def stamp():
    return datetime.now(timezone.utc).isoformat()


def write(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def identity(first):
    assert digest(CLI) == OLD_CLI, 'OLD CLI changed'
    assert digest(NATIVE) == OLD_NATIVE, 'native changed'
    for project in first['projects']:
        for name, sha in project['selected_files'].items():
            assert digest(Path(project['selected_predecessor']) / name) == sha
            assert digest(BASE / 'before-sources' / project['project'] / name) == sha
        for name, sha in project['original_files'].items():
            assert digest(ROOT / 'corpus' / project['project'] / name) == sha
    assert digest(ROOT / 'corpus/Qargo.toml') == first['shared_qargo_sha256']


def main():
    output = BASE / 'observations-before'
    assert not output.exists(), 'refuse overwrite'
    first = json.loads((BASE / 'first-sources.json').read_text())
    identity(first)
    output.mkdir()
    artifacts = output / 'artifacts'
    artifacts.mkdir()
    started = stamp()
    environment = os.environ.copy()
    environment['QLEISLI_KERNEL'] = str(NATIVE)
    results = []
    for project in first['projects']:
        name = project['project']
        selected = project['selected_predecessor']
        label = name.replace('/', '-')
        commands = [
            ('check', [str(CLI), 'check', selected, '--format=json', '--lean-kernel=' + str(NATIVE)]),
            ('run', [str(CLI), 'run', selected, '--format=json', '--lean-kernel=' + str(NATIVE)]),
            ('emit-ir', [str(CLI), 'emit-ir', selected, '--output=' + str(artifacts / (label + '.qirf')), '--format=json', '--lean-kernel=' + str(NATIVE)]),
        ]
        for action, argv in commands:
            identity(first)
            began = time.monotonic()
            completed = subprocess.run(argv, cwd=ROOT, env=environment, capture_output=True, timeout=60)
            elapsed = time.monotonic() - began
            identity(first)
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
    identity(first)
    captured = {p.relative_to(BASE).as_posix(): {'sha256': digest(p), 'bytes': p.stat().st_size}
                for p in sorted(artifacts.iterdir())}
    assert all(p['bytes'] < 1024 * 1024 for p in captured.values())
    summary = {'format': 'qleisli.coherent-basis-corpus-before-observations', 'version': 1,
               'started_utc': started, 'ended_utc': stamp(),
               'binary': {'path': str(CLI), 'sha256': OLD_CLI},
               'native': {'path': str(NATIVE), 'sha256': OLD_NATIVE},
               'first_sources_sha256': digest(BASE / 'first-sources.json'),
               'sources': {p['project'] + '/' + n: s for p in first['projects']
                           for n, s in p['selected_files'].items() if n.endswith('.qli')},
               'results': results, 'artifacts': captured,
               'scope': 'Six bounded actual OLD commands on existing 5/4-qubit finite corpus projects. No independent upstream oracle, theorem replay, build, new maximum case, guarantee admission or release validation.'}
    write(output / 'capture.json', summary)
    print(json.dumps({'observations': len(results), 'results': [{'project': r['project'], 'action': r['action'], 'exit': r['exit_code'], 'outcome': r['parsed_stdout']['outcome']} for r in results], 'artifacts': captured, 'capture_sha256': digest(output / 'capture.json')}, indent=2))


if __name__ == '__main__':
    main()
