#!/usr/bin/env python3
"""Record bounded packaged quantum tuple and unitor checks in the existing reusable target.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
TESTS = ['quantum_tuple_unitors', 'quantum_unit_maps', 'quantum_unit_source', 'predicate_domain', 'frontend_types', 'sized_source', 'sized_cli',
         'sized_review_diagnostics', 'unit_patterns', 'runtime_parameter_patterns',
         'ordinary_types', 'selected_source_cli', 'mixed_booleans']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    paths = list((ROOT / 'src').rglob('*.rs'))
    paths += list((ROOT / 'stdlib/src').rglob('*.qli'))
    paths += [ROOT / name for name in ['Cargo.toml', 'Cargo.lock', 'tests/common/mod.rs']]
    paths += [ROOT / f'tests/{name}.rs' for name in TESTS]
    paths += list((HERE / 'independent-sources').rglob('*.qli'))
    paths += list((HERE / 'independent-sources').rglob('Qargo.toml'))
    paths += [HERE / 'independent-expectations.json']
    paths += list((ROOT / 'tests/fixtures/frontend_v030/quantum-unit-maps/current').rglob('*.qli'))
    paths += list((ROOT / 'tests/fixtures/frontend_v030/quantum-unit-source/current').rglob('*.qli'))
    predicate = ROOT / 'tests/fixtures/frontend_v030/ordinary-type-cutover/current/frontend_v030/predicate-domain-independent'
    paths += list(predicate.rglob('*.qli')) + list(predicate.rglob('Qargo.toml'))
    paths += list((ROOT / 'tests/fixtures/frontend_v030/ordinary-types-independent/sources').rglob('*.qli'))
    for name in ['quantum-tuple-unitors-v030', 'quantum-unit-maps-v030', 'quantum-unit-v030', 'finite-unit-pattern-v030',
                 'mixed-boolean-v030', 'ordinary-boolean-v030',
                 'runtime-parameter-pattern-v030', 'selected-source-cli-v030']:
        directory = ROOT / 'tests/fixtures/authoring_sessions' / name
        paths += list(directory.rglob('*.qli')) + list(directory.rglob('Qargo.toml'))
    return {str(path.relative_to(ROOT)): sha(path) for path in sorted(set(paths))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--msrv', action='store_true')
    parser.add_argument('--resume-after-integration', action='store_true', help='Run the remaining library/native CLI/lint/docs checks after a preserved integration pass')
    parser.add_argument('--record', required=True)
    args = parser.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9_-]+', args.record):
        raise SystemExit('Use a single record directory name')
    destination = HERE / args.record
    destination.mkdir(exist_ok=False)
    free = shutil.disk_usage(ROOT).free
    if free < 8 * 1024**3:
        raise SystemExit('Insufficient free space for bounded validation')
    env = os.environ.copy()
    for name in ['QLEISLI_QPE_PROPOSALS', 'QLEISLI_QPE_PERF_PROPOSALS']:
        env.pop(name, None)
    if args.msrv:
        env['PATH'] = '/Users/masa/.rustup/toolchains/1.85.0-aarch64-apple-darwin/bin' + os.pathsep + env['PATH']
    kernel_path = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
    env.update(CARGO_TARGET_DIR='/private/tmp/qleisli-bounded-validation-target',
               CARGO_INCREMENTAL='0', CARGO_PROFILE_DEV_DEBUG='0',
               CARGO_PROFILE_TEST_DEBUG='0', CARGO_BUILD_JOBS='2',
               QLEISLI_KERNEL=str(kernel_path), QLEISLI_HIERARCHY_KERNEL=str(kernel_path))
    commands = [['rustc', '--version'], ['cargo', '--version'], ['cargo', 'clippy', '--version'],
                ['cargo', 'test', '--locked', '--offline',
                 *[argument for name in TESTS for argument in ['--test', name]]],
                ['cargo', 'test', '--locked', '--offline', '--lib', 'frontend::sized'],
                ['cargo', 'test', '--locked', '--offline', '--test', 'sized_cli', '--', '--ignored'],
                ['cargo', 'clippy', '--locked', '--offline', '--all-targets', '--', '-D', 'warnings'],
                ['cargo', 'rustdoc', '--offline', '--locked', '--lib', '--', '-D', 'warnings'],
                ['cargo', 'fmt', '--check']]
    if args.resume_after_integration:
        commands = commands[:3] + commands[4:]
    before = sources()
    kernel = sha(kernel_path)
    (destination / 'sources.json').write_text(json.dumps(before, indent=2) + '\n')
    rows = []
    for index, command in enumerate(commands):
        started = time.monotonic()
        with (destination / f'{index}.stdout.txt').open('wb') as out, (destination / f'{index}.stderr.txt').open('wb') as err:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=out, stderr=err,
                                    timeout=900, check=False)
        rows.append(dict(command=command, exit=result.returncode,
                         elapsed_seconds=time.monotonic() - started,
                         stdout=f'{index}.stdout.txt', stderr=f'{index}.stderr.txt'))
        print(f'{args.record}: {command} => {result.returncode}', flush=True)
        if result.returncode:
            break
    record = dict(base_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                  driver_sha256=sha(Path(__file__)), commands=rows,
                  source_manifest_sha256=sha(destination / 'sources.json'), source_count=len(before),
                  integration_targets_executed=not args.resume_after_integration,
                  sources_stable=before == sources(), kernel_sha256=kernel,
                  kernel_stable=kernel == sha(kernel_path),
                  kernel_status='Reused existing checker; no new Lean build/audit/replay',
                  target=env['CARGO_TARGET_DIR'], incremental=False, debug_information=False,
                  build_jobs=2, free_bytes_before=free, free_bytes_after=shutil.disk_usage(ROOT).free,
                  scope=('Continuation after a separately recorded integration pass: sized library tests, existing ignored native CLI tests, all-target Clippy, library rustdoc and formatting; does not rerun integration targets' if args.resume_after_integration else 'Thirteen focused integration targets, sized library tests, existing ignored native CLI tests, all-target Clippy, library rustdoc and formatting; not all-target runtime or release validation'))
    (destination / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
    if len(rows) != len(commands) or any(row['exit'] for row in rows) or not record['sources_stable'] or not record['kernel_stable']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
