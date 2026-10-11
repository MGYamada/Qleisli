#!/usr/bin/env python3
"""Check the preserved first inputs and compare three unchanged small proposals.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
STUDY = ROOT / 'tests/fixtures/authoring_sessions/finite-unit-pattern-v030'
CURRENT = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
KERNEL = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    output = HERE / 'cli-after.json'
    progress = HERE / 'cli-after-calls.json'
    if output.exists() or progress.exists():
        raise SystemExit('Preserve the existing observation')
    identity = json.loads((STUDY / 'identity-before.json').read_text())
    old = Path(identity['binary']['path'])
    assert sha(old) == identity['binary']['sha256']
    current_sha, kernel_sha = sha(CURRENT), sha(KERNEL)
    assert kernel_sha == identity['kernel']['sha256']
    calls = []

    def call(binary, command, project):
        args = [str(binary), command, str(project)]
        if command == 'check':
            args += ['--format=json']
        artifact = None
        if command == 'emit-ir':
            artifact = HERE / 'cli-artifacts' / f'{len(calls):02}.qirf.json'
            artifact.parent.mkdir(exist_ok=True)
            assert not artifact.exists()
            args += [f'--output={artifact}']
        result = subprocess.run(args, cwd=ROOT, capture_output=True, timeout=45,
                                env=os.environ | {'QLEISLI_KERNEL': str(KERNEL)})
        calls.append({'command': args, 'exit': result.returncode,
                      'stdout': result.stdout.decode(), 'stderr': result.stderr.decode()})
        if artifact is not None and artifact.exists():
            calls[-1]['artifact'] = str(artifact.relative_to(HERE))
            calls[-1]['artifact_sha256'] = sha(artifact)
        progress.write_text(json.dumps(calls, indent=2) + '\n')
        return result

    observations = []
    for row in json.loads((STUDY / 'projects.json').read_text()):
        project = (STUDY / row['path']).resolve()
        assert project.is_relative_to(STUDY)
        assert sha(project / 'main.qli') == row['source_sha256']
        assert sha(project / 'Qargo.toml') == row['manifest_sha256']
        result = call(CURRENT, 'check', project)
        expected = row['category'] in {'attempt-01', 'controls'}
        assert (result.returncode == 0) == expected, (row['name'], result.stdout)
        data = json.loads(result.stdout)
        observations.append({'path': row['path'], 'source_sha256': row['source_sha256'],
                             'exit': result.returncode,
                             'codes': [d['code'] for d in data.get('diagnostics', [])]})
    unchanged = []
    for project in [ROOT / 'examples/bell', ROOT / 'examples/grover',
                    STUDY / 'controls/named-effectful-unit']:
        before, after = call(old, 'emit-ir', project), call(CURRENT, 'emit-ir', project)
        assert before.returncode == after.returncode == 0
        before_bytes = (HERE / calls[-2]['artifact']).read_bytes()
        after_bytes = (HERE / calls[-1]['artifact']).read_bytes()
        assert before_bytes == after_bytes, str(project)
        unchanged.append({'project': str(project.relative_to(ROOT)),
                          'artifact_sha256': hashlib.sha256(after_bytes).hexdigest()})
    assert sha(old) == identity['binary']['sha256']
    assert sha(CURRENT) == current_sha and sha(KERNEL) == kernel_sha
    output.write_text(json.dumps({
        'status': 'passed', 'driver_sha256': sha(Path(__file__)),
        'current_binary_sha256': current_sha, 'old_binary': identity['binary'],
        'current_build_sources': 'msrv/sources-before.json',
        'kernel_sha256': kernel_sha, 'observations': observations,
        'unchanged_proposals': unchanged, 'calls': calls,
        'scope': '19 small source checks and three byte-identical IR comparisons; no full preservation claim',
    }, indent=2) + '\n')
    print(f'{len(observations)} source checks; {len(unchanged)} unchanged proposals; {len(calls)} CLI calls')


if __name__ == '__main__':
    main()
