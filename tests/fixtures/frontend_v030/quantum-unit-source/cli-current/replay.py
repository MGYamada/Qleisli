#!/usr/bin/env python3
"""Repeat the frozen 28 small commands, without rebuilding or changing inputs.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[5]
BASE = ROOT / 'tests/fixtures/authoring_sessions/quantum-unit-v030'
BUILD = ROOT / 'tests/fixtures/frontend_v030/quantum-unit-source/latest-final'
CLI = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
KERNEL = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def mismatches(base, manifest):
    return {name: {'expected': value, 'actual': digest(base / name)}
            for name, value in manifest.items() if digest(base / name) != value}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    observations = output / 'observations'
    observations.mkdir()  # Refuse to overwrite an earlier observation set.
    sources = read(BUILD / 'sources.json')
    build = read(BUILD / 'result.json')
    baseline = read(BASE / 'files.json')['files']
    original = read(BASE / 'baseline-summary.json')['results']
    assert len(original) == 28
    assert digest(BUILD / 'sources.json') == build['source_manifest_sha256']
    assert not mismatches(ROOT, sources), 'current inputs differ from final build'
    assert not mismatches(BASE, baseline), 'original study changed'
    assert all(command['exit'] == 0 for command in build['commands'])
    before = {
        'recorded_utc': datetime.now(timezone.utc).isoformat(),
        'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'binary': {'path': str(CLI), 'sha256': digest(CLI)},
        'kernel': {'path': str(KERNEL), 'sha256': digest(KERNEL)},
        'build_result': {'path': str((BUILD / 'result.json').relative_to(ROOT)),
                         'sha256': digest(BUILD / 'result.json')},
        'build_sources': {'path': str((BUILD / 'sources.json').relative_to(ROOT)),
                          'sha256': digest(BUILD / 'sources.json'), 'count': len(sources)},
        'baseline_manifest_sha256': digest(BASE / 'files.json'),
        'driver_sha256': digest(Path(__file__)),
        'binding_scope': 'Existing final-build target; no build is performed by this driver. All final-build source hashes match before and after execution.',
    }
    assert before['kernel']['sha256'] == build['kernel_sha256']
    write(output / 'identity-before.json', before)
    selected_negative = {
        'bits0-as-unit': 'type', 'unit-as-bits0': 'type',
        'duplicate-owner': 'ownership', 'lost-owner': 'ownership',
        'wildcard-owner': 'ownership', 'zero-fold-invalid': 'ownership',
    }
    results = []
    for item in original:
        name = item['case'] + '-' + item['profile']
        old_path = BASE / 'observations' / (name + '.json')
        old = read(old_path)
        command = old['command']
        assert command[0] == str(CLI)
        environment = os.environ.copy()
        environment.update(old['environment'])
        start = time.monotonic()
        run = subprocess.run(command, cwd=old['working_directory'], env=environment,
                             capture_output=True, timeout=60)
        stdout = run.stdout.decode('utf-8')
        stderr = run.stderr.decode('utf-8')
        document = json.loads(stdout)
        codes = [row['code'] for row in document['diagnostics']]
        unchanged = (run.returncode == old['exit_code']
                     and stdout == old['stdout_text'] and stderr == old['stderr'])
        if item['profile'] == 'finite':
            expected = unchanged
            classification = 'unchanged finite result' if expected else 'unexpected finite change'
        elif item['case'] in selected_negative:
            expected = run.returncode == 1 and codes == [selected_negative[item['case']]]
            classification = 'intended exact-type/ownership rejection'
        else:
            expected = run.returncode == 0 and not codes
            classification = 'selected hierarchy acceptance'
        record = {
            'command': command, 'working_directory': old['working_directory'],
            'environment': old['environment'], 'exit_code': run.returncode,
            'recorded_utc': datetime.now(timezone.utc).isoformat(),
            'elapsed_seconds': time.monotonic() - start,
            'stdout_text': stdout, 'stderr': stderr, 'stdout': document,
            'baseline_observation': str(old_path.relative_to(ROOT)),
            'baseline_observation_sha256': digest(old_path),
            'source_sha256': old['source_sha256'], 'manifest_sha256': old['manifest_sha256'],
            'binary_sha256': before['binary']['sha256'],
            'kernel_sha256': before['kernel']['sha256'],
            'same_argv_and_explicit_environment': True,
            'baseline_exit_stdout_stderr_unchanged': unchanged,
            'classification': classification, 'expected_current_result': expected,
        }
        write(observations / (name + '.json'), record)
        results.append({'case': item['case'], 'profile': item['profile'],
                        'exit_code': run.returncode, 'diagnostic_codes': codes,
                        'unchanged': unchanged, 'classification': classification,
                        'expected_current_result': expected})
    after = {
        'binary_sha256': digest(CLI), 'kernel_sha256': digest(KERNEL),
        'source_deltas': mismatches(ROOT, sources),
        'baseline_deltas': mismatches(BASE, baseline),
        'build_sources_sha256': digest(BUILD / 'sources.json'),
        'build_result_sha256': digest(BUILD / 'result.json'),
        'baseline_manifest_sha256': digest(BASE / 'files.json'),
    }
    stable = (after['binary_sha256'] == before['binary']['sha256']
              and after['kernel_sha256'] == before['kernel']['sha256']
              and not after['source_deltas'] and not after['baseline_deltas']
              and after['build_sources_sha256'] == before['build_sources']['sha256']
              and after['build_result_sha256'] == before['build_result']['sha256']
              and after['baseline_manifest_sha256'] == before['baseline_manifest_sha256'])
    write(output / 'identity-after.json', after)
    summary = {'commands': len(results), 'stable': stable,
               'expected_results': all(row['expected_current_result'] for row in results),
               'profiles': {profile: {
                   'accepted': sum(row['profile'] == profile and row['exit_code'] == 0 for row in results),
                   'rejected': sum(row['profile'] == profile and row['exit_code'] != 0 for row in results),
                   'unchanged': sum(row['profile'] == profile and row['unchanged'] for row in results),
               } for profile in ['selected', 'finite']}, 'results': results}
    write(output / 'summary.json', summary)
    print(json.dumps({key: summary[key] for key in ['commands', 'stable', 'expected_results', 'profiles']}, indent=2))
    return 0 if stable and summary['expected_results'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
