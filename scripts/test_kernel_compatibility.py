#!/usr/bin/env python3
"""Compare native kernel transports byte for byte with a supplied prior binary.

Existing independent-oracle suites provide inputs and expected decisions. This
optional compatibility check also compares stdout, stderr, exit status and all
reported work counters. It never refreshes the original fixtures.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import hashlib
import importlib
import json
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def compare(before, after):
    run = subprocess.run
    records = []

    def checked(argv, *args, **kwargs):
        result = run(argv, *args, **kwargs)
        if not argv or Path(argv[0]).resolve() != after:
            return result
        previous = run([str(before), *argv[1:]], *args, **kwargs)
        assert (previous.returncode, previous.stdout, previous.stderr) == (
            result.returncode, result.stdout, result.stderr), (argv, previous, result)
        def binary(value):
            return value.encode() if isinstance(value, str) else value or b""
        inputs = []
        for argument in argv[1:]:
            path = Path(argument)
            if path.is_file():
                inputs.append(sha(path.read_bytes()))
        records.append(dict(mode=next((a for a in argv[1:] if str(a).startswith('--')), 'word'),
                            input_sha256=inputs, exit_code=result.returncode,
                            stdout_sha256=sha(binary(result.stdout)),
                            stderr_sha256=sha(binary(result.stderr))))
        return result

    subprocess.run = checked
    try:
        suite = unittest.TestSuite()
        for module, name in [('test_lean_hierarchy', 'HierarchyTests'),
                             ('test_lean_layout', 'LayoutTests'),
                             ('test_lean_layout_dag', 'LayoutDagTests'),
                             ('test_lean_phase_layout', 'PhaseLayoutTests')]:
            tests = importlib.import_module(module)
            tests.BINARY = after
            suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(getattr(tests, name)))
        result = unittest.TextTestRunner(verbosity=1).run(suite)
        assert result.wasSuccessful(), 'independent transport/oracle suite failed'
        for artifact in sorted((ROOT / 'tests/fixtures/verification_v022/native').glob('*.qpk')):
            required = artifact.with_suffix('.qpr')
            checked([str(after), str(artifact), str(required)], capture_output=True, timeout=5)
        # Exercise command dispatch, IO errors and stdin framing for every bridge mode.
        for args in [[], ['--unknown'], ['missing.qpk', 'missing.qpr']]:
            checked([str(after), *args], capture_output=True, timeout=5)
        for mode in ['--hierarchy-pending', '--hierarchy-request-pending',
                     '--hierarchy-fourier-pending', '--readout-check',
                     '--preparation-check', '--instrument-pending', '--qpe-instrument-pending']:
            for payload in [b'', b'BAD1', b'\xff\x00\x00\x00']:
                checked([str(after), mode], input=payload, capture_output=True, timeout=5)
    finally:
        subprocess.run = run
    return dict(format='qleisli.kernel-transport-compatibility', version=1, status='passed',
                before_binary_sha256=sha(before.read_bytes()), after_binary_sha256=sha(after.read_bytes()),
                oracle_tests=result.testsRun, comparisons=len(records),
                records=records, scope='textual profiles and all malformed bridge modes; valid bridge semantics use separate native/host suites')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--before', required=True, type=Path)
    parser.add_argument('--after', type=Path, default=ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel')
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    report = compare(args.before.resolve(strict=True), args.after.resolve(strict=True))
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'records'}, sort_keys=True))


if __name__ == '__main__':
    main()
