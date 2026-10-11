#!/usr/bin/env python3
"""Compare current CLI observations without executing commands from old records.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
STUDY = ROOT / 'tests/fixtures/authoring_sessions/ordinary-boolean-v030'
CLI = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
KERNEL = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
CASES = ['constants', 'truth-operations', 'copy-drop', 'mixed-passthrough',
         'classical-control', 'measured-feedback', 'measured-logic',
         'unit-observation-retention', 'eager-and-observation', 'static-selection',
         'static-as-runtime', 'runtime-as-static']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    destination = HERE / 'cli-observations.json'
    if destination.exists():
        raise SystemExit('Keep the existing observation record unchanged')
    build = json.loads((HERE / 'cli-build.json').read_text())
    if build['exit'] or sha(CLI) != build['binary_sha256']:
        raise SystemExit('Current binary differs from its successful build record')
    env = os.environ.copy()
    env['QLEISLI_KERNEL'] = str(KERNEL)
    binary, kernel = sha(CLI), sha(KERNEL)
    rows = []
    for index, name in enumerate(CASES):
        project = STUDY / ('attempt-01' if index < 10 else 'counterexamples') / name
        commands = [('finite', [str(CLI), 'check', str(project), '--format=json'])]
        commands += [('sized', [str(CLI), 'sized', 'check', '--entry=main::f',
                               f'--module=main={project / "main.qli"}', f'--kernel={KERNEL}',
                               *(['--nat=n=1'] if name in ['static-selection', 'static-as-runtime'] else [])])]
        if index < 9:
            commands += [('closed', [str(CLI), 'run', str(project), '--format=json'])]
        for mode, command in commands:
            started = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True,
                                    text=True, timeout=30, check=False)
            baseline = json.loads((STUDY / 'observations' / f'{mode}-{name}.json').read_text())
            rows.append(dict(case=name, mode=mode, command=command, exit=result.returncode,
                             stdout=result.stdout, stderr=result.stderr,
                             elapsed_seconds=time.monotonic() - started,
                             source_sha256=sha(project / 'main.qli'),
                             manifest_sha256=sha(project / 'Qargo.toml'),
                             source_unchanged=sha(project / 'main.qli') == baseline['source_sha256'],
                             same_observation=(result.returncode, result.stdout, result.stderr) ==
                             (baseline['exit_code'], baseline['stdout_raw'], baseline['stderr'])))
    record = dict(binary_sha256=binary, kernel_sha256=kernel,
                  executables_stable=binary == sha(CLI) and kernel == sha(KERNEL),
                  commands=rows, scope='Actual existing finite and sized CLI; Raw API execution is covered separately by Rust tests, not inferred from these profile rejections')
    destination.write_text(json.dumps(record, indent=2) + '\n')
    stable = all(r['same_observation'] for r in rows if r['mode'] != 'sized')
    print(json.dumps(dict(calls=len(rows), finite_and_closed_unchanged=stable,
                          sized_changes=[r['case'] for r in rows if r['mode'] == 'sized' and not r['same_observation']])))
    if not stable or not record['executables_stable'] or not all(r['source_unchanged'] for r in rows):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
