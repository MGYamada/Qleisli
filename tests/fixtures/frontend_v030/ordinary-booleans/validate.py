#!/usr/bin/env python3
"""Record bounded ordinary-Boolean checks in the existing reusable target.

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
TESTS = ['ordinary_booleans', 'runtime_parameter_patterns', 'unit_patterns',
         'frontend_types', 'tuple_shapes', 'parser', 'sized_declarations',
         'source_judgments', 'specification_boundaries']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    paths = list((ROOT / 'src').rglob('*.rs'))
    paths += list((ROOT / 'stdlib/src').rglob('*.qli'))
    paths += [ROOT / name for name in ['Cargo.toml', 'Cargo.lock', 'tests/common/mod.rs']]
    paths += [ROOT / f'tests/{name}.rs' for name in TESTS]
    for name in ['ordinary-boolean-v030', 'runtime-parameter-pattern-v030', 'finite-unit-pattern-v030']:
        directory = ROOT / 'tests/fixtures/authoring_sessions' / name
        paths += list(directory.rglob('*.qli')) + list(directory.rglob('Qargo.toml'))
    return {str(path.relative_to(ROOT)): sha(path) for path in sorted(set(paths))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--msrv', action='store_true')
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
    if args.msrv:
        env['PATH'] = '/Users/masa/.rustup/toolchains/1.85.0-aarch64-apple-darwin/bin' + os.pathsep + env['PATH']
    env.update(CARGO_TARGET_DIR='/private/tmp/qleisli-bounded-validation-target',
               CARGO_INCREMENTAL='0', CARGO_PROFILE_DEV_DEBUG='0',
               CARGO_PROFILE_TEST_DEBUG='0', CARGO_BUILD_JOBS='2',
               QLEISLI_KERNEL=str(ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'))
    commands = [['rustc', '--version'], ['cargo', '--version'], ['cargo', 'clippy', '--version'],
                ['cargo', 'test', '--locked', '--offline',
                 *[argument for name in TESTS for argument in ['--test', name]]],
                ['cargo', 'test', '--locked', '--offline', '--lib', 'raw_source_replay'],
                ['cargo', 'clippy', '--locked', '--offline', '--all-targets', '--', '-D', 'warnings'],
                ['cargo', 'fmt', '--check']]
    before = sources()
    kernel = sha(Path(env['QLEISLI_KERNEL']))
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
                  sources_stable=before == sources(), kernel_sha256=kernel,
                  kernel_stable=kernel == sha(Path(env['QLEISLI_KERNEL'])),
                  kernel_status='Reused existing checker; no new Lean build/audit/replay',
                  target=env['CARGO_TARGET_DIR'], incremental=False, debug_information=False,
                  build_jobs=2, free_bytes_before=free, free_bytes_after=shutil.disk_usage(ROOT).free,
                  scope='Nine focused integration targets, one native-valid mutation replay regression, all-target Clippy and formatting; not all-target runtime or release validation')
    (destination / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
    if len(rows) != len(commands) or any(row['exit'] for row in rows) or not record['sources_stable'] or not record['kernel_stable']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
