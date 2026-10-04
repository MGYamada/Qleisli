#!/usr/bin/env python3
"""Bounded local validation; no Lean build or repository snapshot copies.

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


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    paths = list((ROOT / 'src').rglob('*.rs'))
    paths += list((ROOT / 'stdlib/src').rglob('*.qli'))
    paths += [ROOT / name for name in (
        'Cargo.toml', 'Cargo.lock', 'tests/unit_patterns.rs',
        'tests/ordinary_types.rs', 'tests/frontend_types.rs',
        'tests/tuple_shapes.rs', 'tests/common/mod.rs',
    )]
    for directory in (
        ROOT / 'tests/fixtures/authoring_sessions/finite-unit-pattern-v030',
        ROOT / 'tests/fixtures/frontend_v030/ordinary-types-independent/sources',
    ):
        paths += list(directory.rglob('*.qli'))
        paths += list(directory.rglob('Qargo.toml'))
    return {str(p.relative_to(ROOT)): sha(p) for p in sorted(set(paths))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--msrv', action='store_true')
    parser.add_argument('--record-name')
    args = parser.parse_args()
    name = 'msrv' if args.msrv else 'latest'
    record = args.record_name or name
    if re.fullmatch(r'[A-Za-z0-9_-]+', record) is None:
        raise SystemExit('Expected a single record directory name')
    destination = HERE / record
    destination.mkdir(exist_ok=True)
    if (destination / 'result.json').exists():
        raise SystemExit('Keep existing observations; choose a separate record before rerunning')
    free_before = shutil.disk_usage(ROOT).free
    if free_before < 8 * 1024**3:
        raise SystemExit('Insufficient free space for bounded validation')
    env = os.environ.copy()
    if args.msrv:
        toolchain = '/Users/masa/.rustup/toolchains/1.85.0-aarch64-apple-darwin/bin'
        env['PATH'] = toolchain + os.pathsep + env['PATH']
    env.update({
        'CARGO_TARGET_DIR': str(TARGET), 'CARGO_INCREMENTAL': '0',
        'CARGO_PROFILE_DEV_DEBUG': '0', 'CARGO_PROFILE_TEST_DEBUG': '0',
        'CARGO_BUILD_JOBS': '2',
        'QLEISLI_KERNEL': str(ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'),
    })
    commands = [
        ['cargo', '--version'], ['rustc', '--version'], ['cargo', 'clippy', '--version'],
        ['cargo', 'test', '--locked', '--offline', '--test', 'unit_patterns',
         '--test', 'ordinary_types', '--test', 'frontend_types', '--test', 'tuple_shapes'],
        ['cargo', 'test', '--locked', '--offline', '--lib',
         'constructed_ordinary_parameter_patterns_reject_before_name_only_lowering'],
        ['cargo', 'clippy', '--locked', '--offline', '--test', 'unit_patterns',
         '--', '-D', 'warnings'],
    ]
    before = sources()
    kernel_before = sha(Path(env['QLEISLI_KERNEL']))
    (destination / 'sources-before.json').write_text(json.dumps(before, indent=2) + '\n')
    rows = []
    for index, command in enumerate(commands):
        started = time.monotonic()
        with (destination / f'{index}.stdout.txt').open('wb') as out, \
                (destination / f'{index}.stderr.txt').open('wb') as err:
            completed = subprocess.run(command, cwd=ROOT, env=env, stdout=out,
                                       stderr=err, check=False, timeout=900)
        rows.append({'command': command, 'exit': completed.returncode,
                     'elapsed_seconds': time.monotonic() - started,
                     'stdout': f'{index}.stdout.txt', 'stderr': f'{index}.stderr.txt'})
        print(f'{name}: {command} => {completed.returncode}', flush=True)
        if completed.returncode:
            break
    after = sources()
    result = {
        'driver_sha256': sha(Path(__file__)),
        'commands': rows, 'source_files': len(before),
        'sources_stable': before == after,
        'source_manifest_sha256': sha(destination / 'sources-before.json'),
        'kernel_sha256': kernel_before,
        'kernel_stable': kernel_before == sha(Path(env['QLEISLI_KERNEL'])),
        'kernel_status': 'Reused existing audited checker; no new Lean build/audit/replay',
        'cargo_target': str(TARGET), 'incremental': False, 'debug_information': False,
        'free_bytes_before': free_before, 'free_bytes_after': shutil.disk_usage(ROOT).free,
        'scope': 'Four bounded Rust integration targets, the manual-AST regression and unit_patterns Clippy; not all-target or release validation',
    }
    (destination / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    if (before != after or not result['kernel_stable']
            or len(rows) != len(commands) or any(r['exit'] for r in rows)):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
