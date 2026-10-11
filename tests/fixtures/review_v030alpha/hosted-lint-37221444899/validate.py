#!/usr/bin/env python3
"""Validate the hosted unused-variable repair without linking all test targets.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--msrv', action='store_true')
args = parser.parse_args()
name = 'msrv' if args.msrv else 'latest'
out = HERE / (name + '.json')
assert not out.exists()
assert shutil.disk_usage(ROOT).free > 8 * 1024**3
env = os.environ.copy()
if args.msrv:
    env['PATH'] = '/Users/masa/.rustup/toolchains/1.85.0-aarch64-apple-darwin/bin' + os.pathsep + env['PATH']
env.update({'CARGO_TARGET_DIR': '/private/tmp/qleisli-bounded-validation-target',
            'CARGO_INCREMENTAL': '0', 'CARGO_PROFILE_DEV_DEBUG': '0',
            'CARGO_PROFILE_TEST_DEBUG': '0', 'CARGO_BUILD_JOBS': '2',
            'QLEISLI_KERNEL': str(ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel')})
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
paths = list((ROOT / 'src').rglob('*.rs')) + list((ROOT / 'tests').glob('*.rs'))
paths += list((ROOT / 'examples').glob('*.rs'))
paths += [ROOT / 'Cargo.toml', ROOT / 'Cargo.lock']
before = {str(p.relative_to(ROOT)): sha(p) for p in sorted(paths)}
commands = [['cargo', '--version'], ['rustc', '--version'], ['cargo', 'clippy', '--version'],
            ['cargo', 'clippy', '--locked', '--offline', '--all-targets', '--', '-D', 'warnings'],
            ['cargo', 'test', '--locked', '--offline', '--test', 'specification_boundaries'],
            ['cargo', 'fmt', '--check']]
rows = []
for command in commands:
    start = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True, timeout=900)
    rows.append({'command': command, 'exit': result.returncode,
                 'seconds': time.monotonic() - start, 'stdout': result.stdout, 'stderr': result.stderr})
    print(name, command, result.returncode, flush=True)
    if result.returncode:
        break
stable = before == {str(p.relative_to(ROOT)): sha(p) for p in sorted(paths)}
out.write_text(json.dumps({'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                           'commands': rows, 'sources': before, 'sources_stable': stable,
                           'kernel_sha256': sha(Path(env['QLEISLI_KERNEL'])),
                           'target': env['CARGO_TARGET_DIR'], 'incremental': False, 'debug_information': False,
                           'scope': 'All-target Clippy type-checking and ten existing specification-boundary tests, not all-target test execution or a Lean rebuild.'}, indent=2) + '\n')
if not stable or len(rows) != len(commands) or any(r['exit'] for r in rows):
    raise SystemExit(1)
