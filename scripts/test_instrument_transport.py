#!/usr/bin/env python3
"""Exercise both dynamic component modes against the selected native kernel.

Only one physical qubit is used; component checks are not whole-instrument
acceptance or a source-preservation proof.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tomllib
import unittest
from unittest.mock import patch

import instrument_transport as transport


ROOT = Path(__file__).resolve().parents[1]
KERNEL = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
VERSION = tomllib.loads((ROOT / 'Cargo.toml').read_text())['package']['version']
COMMANDS = []
RUN = subprocess.run


def recorded_run(argv, **kwargs):
    result = RUN(argv, **kwargs)
    COMMANDS.append(dict(argv=[str(a) for a in argv], exit_code=result.returncode,
                         input_sha256=hashlib.sha256(kwargs['input']).hexdigest(),
                         stdout=result.stdout.decode('ascii'),
                         stderr=result.stderr.decode('utf-8', errors='replace')))
    return result


def cases():
    empty = dict(owner=4, basis=[dict(tag='unit')], axes=[])
    bit = dict(owner=7, basis=[dict(tag='bit')], axes=[13])
    inputs = dict(quantum=[empty], classical=[])
    prepared = dict(quantum=[empty, bit], classical=[])
    preparation = dict(initializations=[dict(
        interface=dict(inputs=inputs, outputs=prepared), effect='iso',
        body=dict(tag='init0', output=7))], outputs=prepared)
    measured = dict(quantum=[empty], classical=[dict(value=11, basis=[dict(tag='bit')])])
    outputs = dict(quantum=[empty], classical=[dict(value=99, basis=[dict(tag='bits', width=1)])])
    readout = dict(measurements=[dict(
        interface=dict(inputs=prepared, outputs=measured), effect='observe',
        body=dict(tag='observe_z', input=7, output=11))], pack=[11], outputs=outputs)
    # Break Python aliases: requests and packets are independent transport data.
    return json.loads(json.dumps([
        dict(kind='preparation', request=dict(inputs=inputs, fresh=[bit]), packet=preparation),
        dict(kind='readout', request=dict(inputs=prepared, owners=[7], result=99), packet=readout),
    ]))


def encode(case):
    writer = (transport.encode_preparation if case['kind'] == 'preparation'
              else transport.encode_readout)
    return writer(case['request'], case['packet'])


class InstrumentTransportTests(unittest.TestCase):
    def inspect(self, case, payload=None):
        with patch.object(transport.subprocess, 'run', side_effect=recorded_run):
            return transport.inspect(KERNEL, case['kind'], encode(case) if payload is None else payload)

    def test_matching_version_checks_both_components(self):
        for case in cases():
            with self.subTest(kind=case['kind']):
                result = self.inspect(case)
                self.assertEqual(result['status'], 'checked')
                self.assertGreater(result['work'], 0)
                self.assertEqual(COMMANDS[-1]['argv'],
                                 [str(KERNEL), f'--{case["kind"]}-check', VERSION])

    def test_independent_request_mismatch_is_rejected(self):
        for case in cases():
            with self.subTest(kind=case['kind']):
                changed = copy.deepcopy(case)
                if case['kind'] == 'preparation':
                    changed['request']['fresh'][0]['owner'] = 8
                else:
                    changed['request']['result'] = 100
                self.assertEqual(self.inspect(changed), dict(status='contract'))

    def test_truncated_component_is_rejected(self):
        for case in cases():
            with self.subTest(kind=case['kind']):
                self.assertEqual(self.inspect(case, encode(case)[:-1]), dict(status='format'))

    def test_missing_and_mismatched_versions_are_rejected(self):
        for case in cases():
            for suffix in ([], ['0.0.0']):
                with self.subTest(kind=case['kind'], version=suffix):
                    result = recorded_run([str(KERNEL), f'--{case["kind"]}-check', *suffix],
                                          input=encode(case), capture_output=True, timeout=60)
                    self.assertEqual(result.returncode, 1)
                    self.assertEqual(result.stdout, b'qleisli.qirf-native 1\nerror\nversion\n')

    def test_unknown_component_never_starts_the_kernel(self):
        with patch.object(transport.subprocess, 'run') as run:
            with self.assertRaisesRegex(ValueError, 'unknown component'):
                transport.inspect(KERNEL, 'unknown', b'')
            run.assert_not_called()


def main():
    global KERNEL
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kernel', type=Path, default=KERNEL)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    KERNEL = args.kernel.resolve(strict=True)
    COMMANDS.clear()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(InstrumentTransportTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    report = dict(format='qleisli.component-version-regression', version=1,
                  status='passed' if result.wasSuccessful() else 'failed',
                  product_version=VERSION, tests=result.testsRun, max_qubits=1,
                  kernel_sha256=hashlib.sha256(KERNEL.read_bytes()).hexdigest(),
                  sources={name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                           for name in ('Cargo.toml', 'scripts/instrument_transport.py',
                                        'scripts/test_instrument_transport.py')},
                  commands=COMMANDS,
                  scope='Actual preparation/readout component checks; no whole-instrument acceptance')
    if args.record:
        args.record.write_text(json.dumps(report, indent=2) + '\n')
    raise SystemExit(0 if result.wasSuccessful() else 1)


if __name__ == '__main__':
    main()
