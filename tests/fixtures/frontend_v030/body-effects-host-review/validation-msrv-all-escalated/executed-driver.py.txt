"""Bounded fixed-target validation, retaining exact source maps and raw logs.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""

import hashlib
import json
import os
import signal
from pathlib import Path
import subprocess
import sys
import time

here = Path(__file__).resolve().parent
repo = here.parents[3]
mode = sys.argv[1]
assert mode in {'latest-first', 'latest', 'msrv', 'latest-all', 'msrv-all',
                'latest-all-escalated', 'msrv-all-escalated'}
out = here / ('validation-' + mode)
retry = 0
while out.exists():
    retry += 1
    out = here / ('validation-' + mode + f'-retry-{retry:02d}')
out.mkdir()
env = dict(os.environ, CARGO_TARGET_DIR='/private/tmp/qleisli-bounded-validation-target',
           CARGO_INCREMENTAL='0', CARGO_PROFILE_DEV_DEBUG='0', CARGO_PROFILE_TEST_DEBUG='0',
           CARGO_BUILD_JOBS='2', QLEISLI_KERNEL=str(repo / 'lean-kernel/.lake/build/bin/qleisli-kernel'))
if mode.startswith('msrv'):
    env['PATH'] = '/Users/masa/.rustup/toolchains/1.85.0-aarch64-apple-darwin/bin:' + env['PATH']


def sources():
    paths = sorted((repo / 'src').rglob('*.rs')) + sorted((repo / 'tests').glob('*.rs'))
    paths += sorted((repo / 'stdlib/src').glob('*.qli')) + [repo / 'Cargo.toml', repo / 'Cargo.lock']
    return {str(p.relative_to(repo)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


before = sources()
(out / 'source-files.json').write_text(json.dumps(before, indent=2) + '\n')
(out / 'executed-driver.py.txt').write_bytes(Path(__file__).read_bytes())
(out / 'native.json').write_text(json.dumps({'path': env['QLEISLI_KERNEL'],
    'sha256': hashlib.sha256(Path(env['QLEISLI_KERNEL']).read_bytes()).hexdigest()}, indent=2) + '\n')
targets = ['body_effects', 'sized_source', 'compile', 'parser', 'diagnostics', 'documentation',
           'repair_diagnostics', 'static_operations', 'function_contracts', 'certified_source',
           'operation_parameters', 'selected_source_cli', 'source_judgments']
commands = [['rustc', '--version'], ['cargo', '--version'],
            ['cargo', 'test', '--offline'] + [a for name in targets for a in ['--test', name]],
            ['cargo', 'test', '--offline', '--lib', 'frontend::'],
            ['cargo', 'clippy', '--offline', '--all-targets', '--', '-D', 'warnings']]
if '-all' in mode:
    # The three actual stale diagnostic fixtures justify checking every current
    # Rust consumer. Default ignores stay ignored; no new maximum-size case.
    commands = commands[:2] + [['cargo', 'test', '--offline', '--all-targets']]
    if mode.startswith('msrv'):
        commands += [['cargo', 'clippy', '--offline', '--all-targets', '--', '-D', 'warnings']]
rows = []
for i, argv in enumerate(commands):
    start = time.monotonic()
    timed_out = False
    with (out / f'{i}.stdout.txt').open('wb') as stdout, (out / f'{i}.stderr.txt').open('wb') as stderr:
        process = subprocess.Popen(argv, cwd=repo, env=env, stdout=stdout, stderr=stderr,
                                   start_new_session=True)
        try:
            exit_code = process.wait(timeout=3600)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGTERM)
            try:
                exit_code = process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                exit_code = process.wait()
    row = {'argv': argv, 'exit_code': exit_code, 'timed_out': timed_out,
           'seconds': time.monotonic() - start,
           'stdout': f'{i}.stdout.txt', 'stderr': f'{i}.stderr.txt'}
    rows.append(row)
    stable = before == sources()
    (out / 'result.json').write_text(json.dumps({'mode': mode, 'commands': rows,
        'sources_stable': stable, 'scope': 'Bounded current consumers. Existing ignores retained. No new maximum-size quantum case, fresh Lean replay or release certificate.'}, indent=2) + '\n')
    print(json.dumps(row), flush=True)
    if exit_code or timed_out or not stable:
        raise SystemExit(exit_code if exit_code > 0 else 1)
