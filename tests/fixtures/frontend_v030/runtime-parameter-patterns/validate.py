#!/usr/bin/env python3
"""Retain bounded parameter-pattern validation without source/build-tree copies.

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
TARGET = Path('/private/tmp/qleisli-bounded-validation-target')
TESTS = ['runtime_parameter_patterns', 'unit_patterns', 'frontend_types',
         'tuple_shapes', 'parser', 'sized_declarations', 'shared_resolution',
         'source_scope', 'source_judgments', 'authoring_ergonomics']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    paths = list((ROOT / 'src').rglob('*.rs'))
    paths += list((ROOT / 'stdlib/src').rglob('*.qli'))
    paths += [ROOT / name for name in ['Cargo.toml', 'Cargo.lock', 'tests/common/mod.rs']]
    paths += [ROOT / f'tests/{name}.rs' for name in TESTS]
    for name in ['runtime-parameter-pattern-v030', 'finite-unit-pattern-v030']:
        base = ROOT / 'tests/fixtures/authoring_sessions' / name
        paths += list(base.rglob('*.qli')) + list(base.rglob('Qargo.toml'))
    paths += list((HERE / 'current').rglob('*.qli'))
    paths += list((HERE / 'current').rglob('Qargo.toml'))
    return {str(p.relative_to(ROOT)): sha(p) for p in sorted(set(paths))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--msrv', action='store_true')
    parser.add_argument('--record', required=True)
    args = parser.parse_args()
    if re.fullmatch(r'[A-Za-z0-9_-]+', args.record) is None:
        raise SystemExit('Use a single record directory name')
    destination = HERE / args.record
    destination.mkdir(exist_ok=False)
    free_before = shutil.disk_usage(ROOT).free
    if free_before < 8 * 1024**3:
        raise SystemExit('Insufficient free space for bounded validation')
    env = os.environ.copy()
    if args.msrv:
        env['PATH'] = '/Users/masa/.rustup/toolchains/1.85.0-aarch64-apple-darwin/bin' + os.pathsep + env['PATH']
    env.update({'CARGO_TARGET_DIR': str(TARGET), 'CARGO_INCREMENTAL': '0',
                'CARGO_PROFILE_DEV_DEBUG': '0', 'CARGO_PROFILE_TEST_DEBUG': '0',
                'CARGO_BUILD_JOBS': '2',
                'QLEISLI_KERNEL': str(ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel')})
    test_args = [item for name in TESTS for item in ['--test', name]]
    commands = [
        ['cargo', '--version'], ['rustc', '--version'], ['cargo', 'clippy', '--version'],
        ['cargo', 'test', '--locked', '--offline', *test_args],
        ['cargo', 'test', '--locked', '--offline', '--lib', 'parameter_patterns'],
        ['cargo', 'clippy', '--locked', '--offline', '--lib', '--test',
         'runtime_parameter_patterns', '--test', 'unit_patterns', '--', '-D', 'warnings'],
        ['cargo', 'build', '--locked', '--offline', '--bin', 'qleisli'],
    ]
    before = sources()
    kernel_before = sha(Path(env['QLEISLI_KERNEL']))
    (destination / 'sources.json').write_text(json.dumps(before, indent=2) + '\n')
    rows = []
    for index, command in enumerate(commands):
        started = time.monotonic()
        with (destination / f'{index}.stdout.txt').open('wb') as out, (destination / f'{index}.stderr.txt').open('wb') as err:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=out,
                                    stderr=err, timeout=900, check=False)
        rows.append({'command': command, 'exit': result.returncode,
                     'elapsed_seconds': time.monotonic() - started,
                     'stdout': f'{index}.stdout.txt', 'stderr': f'{index}.stderr.txt'})
        print(f'{args.record}: {command} => {result.returncode}', flush=True)
        if result.returncode:
            break
    result = {'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'driver_sha256': sha(Path(__file__)), 'commands': rows,
              'source_manifest_sha256': sha(destination / 'sources.json'),
              'source_count': len(before), 'sources_stable': before == sources(),
              'kernel_sha256': kernel_before,
              'kernel_stable': kernel_before == sha(Path(env['QLEISLI_KERNEL'])),
              'kernel_status': 'Reused existing checker; no new Lean build/audit/replay',
              'cargo_target': str(TARGET), 'incremental': False, 'debug_information': False,
              'build_jobs': 2, 'free_bytes_before': free_before,
              'free_bytes_after': shutil.disk_usage(ROOT).free,
              'scope': 'Ten focused integration targets, parameter-pattern library regressions, focused Clippy and CLI build; not all-target/release validation'}
    (destination / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    if not result['sources_stable'] or not result['kernel_stable'] or len(rows) != len(commands) or any(r['exit'] for r in rows):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
