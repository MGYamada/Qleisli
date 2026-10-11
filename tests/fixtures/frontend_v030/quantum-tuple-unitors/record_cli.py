#!/usr/bin/env python3
"""Build once and observe the unchanged first packaged-tuple projects.

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

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
STUDY = ROOT / 'tests/fixtures/authoring_sessions/quantum-tuple-unitors-v030'
TARGET = Path('/private/tmp/qleisli-bounded-validation-target')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def inputs():
    paths = list((ROOT / 'src').rglob('*.rs'))
    paths += list((ROOT / 'stdlib/src').rglob('*.qli'))
    paths += [ROOT / 'Cargo.toml', ROOT / 'Cargo.lock']
    paths += list((STUDY / 'attempt-01').rglob('*'))
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths) if p.is_file()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', required=True)
    args = parser.parse_args()
    if not re.fullmatch(r'[a-z0-9-]+', args.record):
        raise SystemExit('Invalid record name')
    out = HERE / args.record
    out.mkdir(exist_ok=False)
    if shutil.disk_usage(ROOT).free < 8 * 1024**3:
        raise SystemExit('Insufficient space for bounded build')
    env = os.environ.copy()
    kernel = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
    env.update(CARGO_TARGET_DIR=str(TARGET), CARGO_INCREMENTAL='0',
               CARGO_PROFILE_DEV_DEBUG='0', CARGO_PROFILE_TEST_DEBUG='0',
               CARGO_BUILD_JOBS='2', QLEISLI_KERNEL=str(kernel),
               QLEISLI_HIERARCHY_KERNEL=str(kernel))
    before, kernel_sha = inputs(), digest(kernel)
    write(out / 'inputs-before.json', before)
    rows = []
    for i, command in enumerate([['rustc', '--version'], ['cargo', '--version'],
                                 ['cargo', 'build', '--offline', '--locked', '--bin', 'qleisli']]):
        start = time.monotonic()
        result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, timeout=900)
        (out / f'build-{i}.stdout.txt').write_bytes(result.stdout)
        (out / f'build-{i}.stderr.txt').write_bytes(result.stderr)
        rows.append(dict(command=command, exit=result.returncode, seconds=time.monotonic()-start))
        write(out / 'build.json', rows)
        print(f'{args.record}: {command}: {result.returncode}', flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)
    binary = TARGET / 'debug/qleisli'
    binary_sha = digest(binary)
    observations = []
    for project in sorted((STUDY / 'attempt-01').iterdir()):
        if not project.is_dir():
            continue
        for route in ['selected', 'finite']:
            command = [str(binary), '--format=json', 'check']
            command += ([f'--entry=main::f', f'--module=main={project / "main.qli"}',
                         '--ir-profile=hierarchy', f'--lean-kernel={kernel}'] if route == 'selected' else [str(project)])
            assert digest(binary) == binary_sha, 'CLI changed before observation'
            start = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, timeout=120)
            assert digest(binary) == binary_sha, 'CLI changed during observation'
            name = f'{project.name}-{route}'
            (out / f'{name}.stdout.txt').write_bytes(result.stdout)
            (out / f'{name}.stderr.txt').write_bytes(result.stderr)
            prior = json.loads((STUDY / 'stable-repeat' / f'{name}.json').read_text())
            observations.append(dict(project=project.name, route=route, command=command,
                exit=result.returncode, seconds=time.monotonic()-start,
                binary_sha256_before=binary_sha, binary_sha256_after=digest(binary),
                stdout=f'{name}.stdout.txt', stderr=f'{name}.stderr.txt',
                unchanged_from_baseline=(result.returncode == prior['exit_code']
                    and result.stdout.decode() == prior['stdout_text']
                    and result.stderr.decode() == prior['stderr'])))
    after = inputs()
    write(out / 'inputs-after.json', after)
    write(out / 'result.json', dict(base_commit=subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        driver_sha256=digest(Path(__file__)), input_count=len(before),
        inputs_stable=before == after, binary_sha256=binary_sha,
        binary_stable=binary_sha == digest(binary), kernel_sha256=kernel_sha,
        kernel_stable=kernel_sha == digest(kernel), observations=observations,
        scope='Actual build and unchanged first-source checks; open functions are not executed, masked diagnostics are not downstream rule checks; no new Lean build/replay.'))
    assert before == after and binary_sha == digest(binary) and kernel_sha == digest(kernel)
    print(f'Recorded {len(observations)} checks; selected accepted: '
          f'{sum(r["exit"] == 0 and r["route"] == "selected" for r in observations)}', flush=True)


if __name__ == '__main__':
    main()
