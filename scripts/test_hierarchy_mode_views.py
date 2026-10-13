#!/usr/bin/env python3
"""Compare actual retained Rust hierarchy plans with the fresh Lean mode gates.
Small curated inputs; existing independent semantic oracles remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
FIXTURE = 'tests/fixtures/verification_v030/execution-view-binding/hierarchy-mode-inputs.json'
TEST = 'interchange::hierarchical::execution::plan::tests::capture_native_hierarchy_mode_plans'


def check_original_capture():
    """Preserve the historical observation; never execute its saved commands."""
    path = ROOT / 'tests/fixtures/verification_v030/execution-view-binding/hierarchy-mode-validation.json'
    historical = json.loads(path.read_text())
    expected = hashlib.sha256((ROOT / FIXTURE).read_bytes()).hexdigest()
    if historical.get('input_sha256') != expected:
        raise ValueError('original mode inputs differ from the retained observation')
    if (historical.get('status') != 'passed' or historical.get('modes') != 5
            or historical.get('invalid_originals') != 3):
        raise ValueError('incomplete original five-mode observation')
    # The recorded result never skips fresh Rust capture or Lean comparison.


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kernel', type=Path,
                        default=ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel')
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    check_original_capture()
    kernel = args.kernel.resolve()
    report = dict(format='qleisli.hierarchy-mode-view-validation', version=1,
                  status='failed', commands=[], source_preservation_proved=False,
                  production_comparison_enabled=False)
    with tempfile.TemporaryDirectory(prefix='qleisli-mode-views-') as temporary:
        environment = os.environ | {'QLEISLI_KERNEL': str(kernel),
                                    'QLEISLI_HIERARCHY_VIEW_CAPTURE': temporary}
        commands = [
            [sys.executable, 'scripts/run_kernel_tests.py', '--', 'cargo', 'test', '--lib',
             TEST, '--', '--exact', '--include-ignored', '--nocapture'],
            ['lake', '-d', 'lean-kernel', 'env', 'lean', '-DwarningAsError=true', '--run',
             'tests/hierarchy_mode_views.lean', FIXTURE, temporary],
        ]
        for command in commands:
            result = subprocess.run(command, cwd=ROOT, env=environment, capture_output=True,
                                    text=True, timeout=600)
            report['commands'].append(dict(argv=command, exit_code=result.returncode,
                                           stdout=result.stdout, stderr=result.stderr))
            print(result.stdout, end='', flush=True)
            print(result.stderr, end='', file=sys.stderr, flush=True)
            if result.returncode:
                if args.record:
                    args.record.write_text(json.dumps(report, indent=2) + '\n')
                return 1
        report.update(status='passed', modes=5, invalid_originals=3,
                      input_sha256=hashlib.sha256((ROOT / FIXTURE).read_bytes()).hexdigest(),
                      kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest(),
                      captures={p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in sorted(Path(temporary).iterdir())})
    if args.record:
        args.record.write_text(json.dumps(report, indent=2) + '\n')
    return 0


if __name__ == '__main__':
    sys.exit(main())
