#!/usr/bin/env python3
"""Observe preserved first sources with the newly built CLI and compare controls.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
STUDY = ROOT / 'tests/fixtures/authoring_sessions/runtime-parameter-pattern-v030'
BINARY = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
KERNEL = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    destination = HERE / 'cli-after'
    destination.mkdir(exist_ok=False)
    before = {str(p.relative_to(STUDY)): sha(p) for p in STUDY.rglob('*') if p.is_file()}
    binary_hash, kernel_hash = sha(BINARY), sha(KERNEL)
    rows = json.loads((STUDY / 'projects.json').read_text())
    rows += json.loads((STUDY / 'additional-projects.json').read_text())
    followups = json.loads((STUDY / 'followup-projects.json').read_text())['projects']
    calls = []
    for row in rows + followups:
        project = STUDY / row['path']
        calls.append((row['path'], 'finite', [str(BINARY), 'check', str(project), '--format=json']))
        sized = row.get('sized', not row['name'].startswith('closed-'))
        if sized:
            calls.append((row['path'], 'sized', [str(BINARY), 'sized', 'check',
                          '--entry=main::f', f'--module=main={project / "main.qli"}',
                          f'--kernel={KERNEL}', *row.get('sized_arguments', [])]))
    # Keep the two original missing-static observations above. These calls
    # explicitly select their separately retained repaired declarations.
    for name in ['static-mixed', 'static-collision']:
        source = STUDY / 'validation-repairs' / f'{name}.qli'
        calls.append((str(source.relative_to(STUDY)), 'sized-repaired',
                      [str(BINARY), 'sized', 'check', '--entry=main::f',
                       f'--module=main={source}', f'--kernel={KERNEL}', '--nat=n=1']))
    controls = [('closed-named-unit', 'followups/closed-named-unit'),
                ('closed-named-swap', 'followups/closed-named-swap'),
                ('named-effectful-unit', 'controls/named-effectful-unit')]
    for name, project in controls:
        calls.append((project, 'emit-ir', [str(BINARY), 'emit-ir', str(STUDY / project),
                      f'--output={destination / (name + ".qirf.json")}']))
    results = []
    for project, mode, command in calls:
        started = time.monotonic()
        result = subprocess.run(command, cwd=ROOT, capture_output=True, timeout=60,
                                env=os.environ | {'QLEISLI_KERNEL': str(KERNEL)})
        results.append({'project': project, 'mode': mode, 'command': command,
                        'exit': result.returncode, 'elapsed_seconds': time.monotonic() - started,
                        'stdout': result.stdout.decode(), 'stderr': result.stderr.decode()})
        print(f'{mode} {project} => {result.returncode}', flush=True)
    comparisons = []
    for name, _ in controls:
        old = STUDY / 'baseline-artifacts' / f'{name}.qirf.json'
        new = destination / f'{name}.qirf.json'
        comparisons.append({'control': name, 'before_sha256': sha(old),
                            'after_sha256': sha(new) if new.exists() else None,
                            'identical': new.exists() and old.read_bytes() == new.read_bytes()})
    unchanged = before == {str(p.relative_to(STUDY)): sha(p) for p in STUDY.rglob('*') if p.is_file()}
    summary = {'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'driver_sha256': sha(Path(__file__)), 'binary_sha256': binary_hash,
               'kernel_sha256': kernel_hash, 'commands': results, 'comparisons': comparisons,
               'historical_study_files_unchanged': unchanged,
               'executables_unchanged': binary_hash == sha(BINARY) and kernel_hash == sha(KERNEL),
               'scope': 'Actual finite/sized CLI observations; three unchanged named controls compare exact emitted IR. Unsupported profiles remain distinct from successful generic checking.'}
    (destination / 'result.json').write_text(json.dumps(summary, indent=2) + '\n')
    if not unchanged or not summary['executables_unchanged'] or not all(c['identical'] for c in comparisons):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
