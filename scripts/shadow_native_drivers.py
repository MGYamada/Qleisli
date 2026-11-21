"""Execute both native regression harnesses and compare their independent reports.

This is a measured subset of native CI, never a substitute for a required suite.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import time

import native_driver_bundle as bundle
import native_harness
from ci_runtime import execution_environment, run_task
from run_native_ci import MANIFEST, ROOT, execute, load_tasks, source_binding, verify_coverage


SIDECARS = {
    'lean-finite': {'native-inputs.json'},
    'lean-raw': {'native-inputs.json'} | {f'source-ir/{i}.qirf.json' for i in range(6)},
    'lean-observation': {'native-inputs.json', 'native-observed.json'} |
                        {f'source-ir/{i}.qirf.json' for i in range(5)},
    'lean-raw-completion': {'completion-inputs.json'},
    'lean-branch-function': {'branch-inputs.json', 'branch-observed.json'},
}
ORACLE_COUNTS = {
    'lean-exact': 'independent_matrix_comparisons', 'lean-finite': 'independent_rational_matrix_checks',
    'lean-raw': 'independent_matrices', 'lean-observation': 'independent_operators',
    'lean-raw-completion': 'independent_matrices', 'lean-branch-function': 'exact_original_operators',
    'lean-interference': 'joint_amplitude_comparisons', 'lean-qft': 'direct_path_comparisons',
    'lean-qft-semantic': 'direct_path_comparisons', 'lean-qft-graph': 'graph_path_comparisons',
    'lean-qpe': 'controlled_path_comparisons',
}


def shadow_tasks(tasks):
    names = bundle.task_ids(tasks)
    if set(names) != set(bundle.MODULES) or set(names) != set(ORACLE_COUNTS):
        raise ValueError('incomplete native driver inventory')
    selected = []
    for task in tasks:
        if task['id'] in names:
            command, = task['commands']
            if '{record}' not in command:
                command = [*command, '--record', '{record}']
            selected.append(task | {'commands': [command]})
    return selected


def observation(directory, selector, shared_identity=None):
    report = json.loads((directory / 'record.json').read_bytes())
    commands = report.pop('commands')
    builds = [row for row in commands if 'driver_source_sha256' in row]
    if len(builds) != 1 or builds[0].get('native_driver') != (selector if shared_identity else None):
        raise ValueError(f'{selector}: missing or different driver selection')
    build = builds[0]
    if shared_identity and (build.get('record_sha256'), build.get('executable_sha256')) != shared_identity:
        raise ValueError(f'{selector}: different prepared executable')
    if not report.get('source_sha256') or not build.get('driver_source_sha256') or not build.get('executable_sha256'):
        raise ValueError(f'{selector}: missing source identity')
    comparisons = report.get(ORACLE_COUNTS[selector])
    if type(comparisons) is not int or comparisons <= 0:
        raise ValueError(f'{selector}: missing independent comparisons')
    # Each arm builds different executables. Retain their identities in the
    # original reports; compare the inputs, outcomes and oracle fields.
    bindings = report.get('native_bindings', {})
    for field in ('lean_binary_sha256', 'native_binary_sha256'):
        if field in bindings and bindings[field] != build['executable_sha256']:
            raise ValueError(f'{selector}: native report names a different executable')
    files = {p.relative_to(directory).as_posix(): p for p in directory.rglob('*.json')
             if p != directory / 'record.json'}
    if set(files) != SIDECARS.get(selector, set()):
        raise ValueError(f'{selector}: missing or unexpected companion reports')
    sidecars = {}
    if selector == 'lean-observation':
        observed = json.loads(files.pop('native-observed.json').read_bytes())
        if (set(observed) != {'bindings', 'lean', 'rust'} or 'lean_binary_sha256' not in bindings
                or observed.pop('bindings') != bindings or not observed['lean'] or not observed['rust']):
            raise ValueError(f'{selector}: inconsistent companion observations or bindings')
        sidecars['native-observed.json'] = observed
    sidecars.update({name: native_harness.digest(path) for name, path in files.items()})
    for field in ('lean_binary_sha256', 'native_binary_sha256', 'rust_binary_sha256'):
        bindings.pop(field, None)
    return dict(source=build['driver_source_sha256'], oracle=report, sidecars=sidecars)


def compare(output, first, report):
    environment = execution_environment() | {
        'QLEISLI_KERNEL': str((ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel').resolve())}
    expected_head = os.environ.get('GITHUB_SHA')
    binding = source_binding(ROOT, expected_head, environment)
    tasks = shadow_tasks(load_tasks(MANIFEST))
    manifest = native_harness.digest(MANIFEST)
    report.update(binding=binding, manifest_sha256=manifest, expected_ids=[t['id'] for t in tasks])
    build_path = output / 'native-build.json'
    report['library_commands'] = []
    native_harness.prepare(build_path, report['library_commands'])
    host = dict(id='host-build', commands=[['cargo', 'build', '--locked', '--bin', 'qleisli']])
    report['host_build'] = run_task(host, ROOT, output / 'host-build', 900, environment)
    if report['host_build']['status'] != 'passed':
        raise ValueError('host build failed; see host-build/command.log')
    bound_environment = environment | {native_harness.BUILD_ENV: str(build_path)}
    observations = {}
    for mode in (first, 'standalone' if first == 'shared' else 'shared'):
        directory = output / mode
        directory.mkdir()
        started = time.monotonic()
        arm = report['arms'][mode] = dict(status='running', preparation_seconds=0)
        drivers = None
        shared_identity = None
        if mode == 'shared':
            arm['preparation_commands'] = []
            drivers = bundle.prepare(directory / 'drivers', report['expected_ids'],
                                     arm['preparation_commands'], build_path)
            binary_hash = json.loads(drivers[0].read_bytes())['binary']['sha256']
            shared_identity = (drivers[1], binary_hash)
            arm['preparation_seconds'] = time.monotonic() - started
        arm['tasks'] = execute(tasks, ROOT, directory, 1, 900, bound_environment, drivers)
        arm['elapsed_seconds'] = time.monotonic() - started
        verify_coverage(dict(binding=binding, manifest_sha256=manifest, tasks=arm['tasks']),
                        tasks, binding, manifest)
        observations[mode] = {name: observation(directory / name, name, shared_identity)
                              for name in report['expected_ids']}
        arm['status'] = 'executed'
    native_harness.validate(build_path)
    if (source_binding(ROOT, expected_head, environment)
            != binding or native_harness.digest(MANIFEST) != manifest):
        raise ValueError('comparison source, tools or task manifest changed')
    report['mismatches'] = [name for name in report['expected_ids']
                            if observations['standalone'][name] != observations['shared'][name]]
    if report['mismatches']:
        raise ValueError('unequal driver inputs or oracle reports: ' + ', '.join(report['mismatches']))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--first', choices=('standalone', 'shared'), default='standalone')
    args = parser.parse_args()
    output = args.output.resolve()
    if output.is_relative_to(ROOT) or output.exists():
        parser.error('select a fresh output directory outside the checkout')
    output.mkdir(parents=True)
    report = dict(status='failed', first=args.first, arms={}, run_id=os.environ.get('GITHUB_RUN_ID'))
    try:
        compare(output, args.first, report)
        report['status'] = 'matched'
    except (KeyError, OSError, ValueError, TypeError, RuntimeError, subprocess.SubprocessError) as exc:
        report['error'] = str(exc)
        print(exc, file=sys.stderr)
    (output / 'comparison.json').write_text(json.dumps(report, indent=2) + '\n')
    return int(report['status'] != 'matched')


if __name__ == '__main__':
    sys.exit(main())
