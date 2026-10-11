#!/usr/bin/env python3
"""Record the existing small native regressions affected by exact port kinds.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import time

from validate import HERE, ROOT, sha, sources


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--msrv', action='store_true')
    parser.add_argument('--record')
    args = parser.parse_args()
    record_name = args.record or ('msrv-native' if args.msrv else 'latest-native')
    if not re.fullmatch(r'[A-Za-z0-9_-]+', record_name):
        raise SystemExit('Use a single record directory name')
    destination = HERE / record_name
    destination.mkdir(exist_ok=False)
    env = os.environ.copy()
    if args.msrv:
        env['PATH'] = '/Users/masa/.rustup/toolchains/1.85.0-aarch64-apple-darwin/bin' + os.pathsep + env['PATH']
    for name in ['QLEISLI_QPE_PROPOSALS', 'QLEISLI_QPE_PERF_PROPOSALS']:
        env.pop(name, None)
    kernel = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
    env.update(CARGO_TARGET_DIR='/private/tmp/qleisli-bounded-validation-target',
               CARGO_INCREMENTAL='0', CARGO_PROFILE_DEV_DEBUG='0',
               CARGO_PROFILE_TEST_DEBUG='0', CARGO_BUILD_JOBS='2',
               QLEISLI_KERNEL=str(kernel), QLEISLI_HIERARCHY_KERNEL=str(kernel))
    commands = [
        ['rustc', '--version'],
        ['cargo', 'test', '--locked', '--offline', '--test', 'sized_source', '--', '--ignored'],
        ['cargo', 'test', '--locked', '--offline', '--lib', 'frontend::sized::qpe::tests::native_named', '--', '--ignored'],
    ]
    before, kernel_before = sources(), sha(kernel)
    (destination / 'sources.json').write_text(json.dumps(before, indent=2) + '\n')
    rows = []
    for index, command in enumerate(commands):
        started = time.monotonic()
        with (destination / f'{index}.stdout.txt').open('wb') as out, (destination / f'{index}.stderr.txt').open('wb') as err:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=out, stderr=err, timeout=900)
        rows.append(dict(command=command, exit=result.returncode, elapsed_seconds=time.monotonic()-started))
        print(f'{destination.name}: {command} => {result.returncode}', flush=True)
        if result.returncode:
            break
    record = dict(commands=rows, source_count=len(before),
                  source_manifest_sha256=sha(destination / 'sources.json'),
                  sources_stable=before == sources(), kernel_sha256=kernel_before,
                  kernel_stable=kernel_before == sha(kernel), driver_sha256=sha(Path(__file__)),
                  scope='Five existing small native Fourier/QPE/gate regressions; no maximum-profile cases, Lean build/audit or full release validation')
    (destination / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
    if len(rows) != len(commands) or any(row['exit'] for row in rows) or not record['sources_stable'] or not record['kernel_stable']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
