#!/usr/bin/env python3
"""Record bounded discovery and existing CLI conformance on one fixed target."""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
parser = argparse.ArgumentParser()
parser.add_argument('--record', required=True)
parser.add_argument('--msrv', action='store_true')
args = parser.parse_args()
out = HERE / args.record
out.mkdir(exist_ok=False)
assert shutil.disk_usage(ROOT).free > 8 * 1024**3
paths = list((ROOT / 'src').rglob('*.rs')) + list((ROOT / 'stdlib/src').rglob('*.qli'))
paths += [ROOT / p for p in ('Cargo.toml', 'Cargo.lock', 'docs/src/reference/discovery.md',
    'tests/discovery_paths.rs', 'tests/selected_source_cli.rs', 'tests/common/mod.rs',
    'scripts/test_cli_json.py')]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


inputs = {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths)}
(out / 'inputs-before.json').write_text(json.dumps(inputs, indent=2) + '\n')
(out / 'driver.py.txt').write_bytes(Path(__file__).read_bytes())
env = os.environ.copy()
native = str(ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel')
env.update(CARGO_TARGET_DIR='/private/tmp/qleisli-bounded-validation-target',
           CARGO_INCREMENTAL='0', CARGO_PROFILE_DEV_DEBUG='0', CARGO_PROFILE_TEST_DEBUG='0',
           CARGO_BUILD_JOBS='2', QLEISLI_KERNEL=native, QLEISLI_HIERARCHY_KERNEL=native)
if args.msrv:
    env['PATH'] = '/Users/masa/.rustup/toolchains/1.85.0-aarch64-apple-darwin/bin:' + env['PATH']
commands = [['rustc', '--version'], ['cargo', '--version'],
    ['cargo', 'test', '--offline', '--locked', '--test', 'discovery_paths',
     '--test', 'selected_source_cli'],
    ['python3', 'scripts/test_cli_json.py', '/private/tmp/qleisli-bounded-validation-target/debug/qleisli'],
    ['cargo', 'clippy', '--offline', '--locked', '--all-targets', '--', '-D', 'warnings'],
    ['cargo', 'fmt', '--check']]
rows = []
for i, argv in enumerate(commands):
    start = time.monotonic()
    result = subprocess.run(argv, cwd=ROOT, env=env, capture_output=True, timeout=600)
    (out / f'{i}.stdout.txt').write_bytes(result.stdout)
    (out / f'{i}.stderr.txt').write_bytes(result.stderr)
    rows.append({'argv': argv, 'exit_code': result.returncode,
                 'seconds': time.monotonic() - start})
    (out / 'commands.json').write_text(json.dumps(rows, indent=2) + '\n')
    print(args.record, argv, result.returncode, flush=True)
    if result.returncode:
        print(result.stdout.decode(), result.stderr.decode())
        break
after = {p: digest(ROOT / p) for p in inputs}
(out / 'inputs-after.json').write_text(json.dumps(after, indent=2) + '\n')
passed = inputs == after and len(rows) == len(commands) and all(
    row['exit_code'] == 0 for row in rows)
(out / 'result.json').write_text(json.dumps({'inputs_stable': inputs == after,
    'source_manifest_sha256': digest(out / 'inputs-before.json'), 'source_count': len(inputs),
    'passed': passed, 'commands': rows,
    'scope': 'Bounded CLI checks; no maximum/ignored stress or local Lean replay'}, indent=2) + '\n')
raise SystemExit(0 if passed else 1)
