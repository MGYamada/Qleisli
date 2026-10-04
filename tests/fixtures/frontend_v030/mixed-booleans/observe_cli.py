#!/usr/bin/env python3
"""Compare current CLI with frozen mixed observations and named IR controls.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
STUDY = ROOT / 'tests/fixtures/authoring_sessions/mixed-boolean-v030'
PATTERNS = ROOT / 'tests/fixtures/authoring_sessions/runtime-parameter-pattern-v030'
BINARY = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
KERNEL = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    destination = HERE / 'cli-after'
    destination.mkdir(exist_ok=False)
    history = {str(p.relative_to(STUDY)): sha(p) for p in STUDY.rglob('*') if p.is_file()}
    binary, kernel = sha(BINARY), sha(KERNEL)
    rows = []
    for project in json.loads((STUDY / 'projects.json').read_text()):
        directory = STUDY / project['path']
        calls = [('finite', [str(BINARY), 'check', str(directory), '--format=json']),
                 ('sized', [str(BINARY), 'sized', 'check', '--entry=main::f',
                            f'--module=main={directory / "main.qli"}', f'--kernel={KERNEL}',
                            *project['sized_arguments']])]
        if project['closed_probe']:
            calls.append(('closed', [str(BINARY), 'run', str(directory), '--format=json']))
        # Construct commands here; historical command text is never executed.
        for mode, command in calls:
            started = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, capture_output=True, timeout=60,
                                    env=os.environ | {'QLEISLI_KERNEL': str(KERNEL)})
            old = json.loads((STUDY / 'observations' / f"{mode}-{project['name']}.json").read_text())
            row = dict(name=project['name'], mode=mode, command=command,
                       exit=result.returncode, seconds=time.monotonic()-started,
                       stdout=result.stdout.decode(), stderr=result.stderr.decode())
            row['identical'] = (row['exit'] == old['exit_code'] and
                                row['stdout'] == old['stdout_raw'] and row['stderr'] == old['stderr'])
            rows.append(row)
            print(mode, project['name'], result.returncode, 'identical', row['identical'], flush=True)
    controls = [('closed-named-unit', 'followups/closed-named-unit'),
                ('closed-named-swap', 'followups/closed-named-swap'),
                ('named-effectful-unit', 'controls/named-effectful-unit')]
    artifacts = []
    for name, source in controls:
        output = destination / (name + '.qirf.json')
        command = [str(BINARY), 'emit-ir', str(PATTERNS / source), f'--output={output}']
        result = subprocess.run(command, cwd=ROOT, capture_output=True, timeout=60,
                                env=os.environ | {'QLEISLI_KERNEL': str(KERNEL)})
        old = PATTERNS / 'baseline-artifacts' / output.name
        artifacts.append(dict(name=name, command=command, exit=result.returncode,
                              stdout=result.stdout.decode(), stderr=result.stderr.decode(),
                              old_sha256=sha(old), new_sha256=sha(output) if output.exists() else None,
                              identical=output.exists() and old.read_bytes() == output.read_bytes()))
    record = dict(recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  driver_sha256=sha(Path(__file__)), binary_sha256=binary, kernel_sha256=kernel,
                  observations=rows, artifacts=artifacts,
                  history_unchanged=history == {str(p.relative_to(STUDY)): sha(p) for p in STUDY.rglob('*') if p.is_file()},
                  executables_unchanged=binary == sha(BINARY) and kernel == sha(KERNEL),
                  scope='Thirty-five actual preceding-CLI comparisons and three unchanged exact IR controls; mixed Raw API execution is separately tested. No CLI routing convergence claim.')
    (destination / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
    if not record['history_unchanged'] or not record['executables_unchanged'] or not all(r['identical'] for r in rows + artifacts):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
