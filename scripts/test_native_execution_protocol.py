#!/usr/bin/env python3
"""Exercise QLV2 through the actual native executable, using retained small vectors.
Byte comparison is not a source-preservation or simulation-correctness proof.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import json
import os
from pathlib import Path
import struct
import subprocess
import tomllib

from native_packet import envelope

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / 'tests/fixtures/verification_v030/execution-view-binding'
VERSION = tomllib.loads((ROOT / 'Cargo.toml').read_text())['package']['version']


def qdv(value):
    def node(v):
        if v is None:
            return b'\0'
        if type(v) is bool:
            return bytes([2 if v else 1])
        if type(v) is int:
            return b'\3' + struct.pack('<Q', v)
        if isinstance(v, str):
            data = v.encode()
            return b'\4' + struct.pack('<I', len(data)) + data
        if isinstance(v, list):
            return b'\5' + struct.pack('<I', len(v)) + b''.join(map(node, v))
        raise ValueError('unexpected shared-vector value')
    return b'QDV1' + node(value)


def inner(artifact, request=None):
    a = json.dumps(artifact, separators=(',', ':')).encode()
    r = b'' if request is None else json.dumps(request, separators=(',', ':')).encode()
    return b'QLV1' + struct.pack('<II', len(a), len(r)) + a + r


class Probe:
    def __init__(self, kernel):
        self.kernel = kernel
        self.count = 0

    def check(self, mode, data, scope=None, error=None):
        result = subprocess.run([str(self.kernel), mode, VERSION], input=data,
                                capture_output=True, timeout=60)
        self.count += 1
        fields = result.stdout.decode().splitlines()
        headers = {'--qirf-native': 'qleisli.qirf-native 2', '--qirf-contract': 'qleisli.qirf-native 2',
                   '--hierarchy-pending': 'qleisli.hierarchy-pending 4',
                   '--hierarchy-request-pending': 'qleisli.hierarchy-request-pending 4',
                   '--hierarchy-fourier-pending': 'qleisli.hierarchy-fourier-pending 4',
                   '--instrument-pending': 'qleisli.instrument-pending 4',
                   '--qpe-instrument-pending': 'qleisli.qpe-instrument-pending 4'}
        assert fields and fields[0] == headers[mode], (mode, result)
        if error:
            assert result.returncode == 1 and fields[1:] == ['error', error], (mode, result)
        else:
            assert result.returncode == 0 and fields[1] in ('accepted', 'pending'), (mode, result)
            assert fields[2] == scope, (scope, result)
        return fields


def finite(probe):
    rows = json.loads((FIXTURE / 'finite-graph-vectors.json').read_text())
    for row in rows:
        original = inner(row['artifact'])
        view = qdv(row['view'])
        probe.check('--qirf-native', envelope(original), 'inspection')
        probe.check('--qirf-native', envelope(original, view), 'execution')
        wrong = qdv(['wrong-graph', *row['view'][1:]])
        probe.check('--qirf-native', envelope(original, wrong), error='decoded_view')
        probe.check('--qirf-native', original, error='format')
    original = inner(rows[0]['artifact'])
    good = envelope(original, qdv(rows[0]['view']))
    for bad in [good + b'x', good[:-1], b'QLV1' + good[4:], good[:4] + struct.pack('<I', 99) + good[8:],
                good[:4] + struct.pack('<I', 0) + good[8:], good[:20] + struct.pack('<I', 100001) + good[24:]]:
        probe.check('--qirf-native', bad, error='format')


def contracts(probe):
    sources = json.loads((FIXTURE / 'contract-walker-vectors.json').read_text())
    for row in json.loads((FIXTURE / 'complete-contract-vectors.json').read_text()):
        source = sources[row['source_index']]
        request = source['request'] | ({'expected_artifact': row['expected_artifact']}
                                      if 'expected_artifact' in row else {})
        original = inner(source['artifact'], request)
        view = ['native-contract', source['view'], row['actual_graph'], row['expected_graph']]
        probe.check('--qirf-contract', envelope(original), 'inspection')
        probe.check('--qirf-contract', envelope(original, qdv(view)), 'execution')
        probe.check('--qirf-contract', envelope(original, qdv(['wrong-contract', *view[1:]])),
                    error='decoded_view')
        probe.check('--qirf-contract', original, error='format')
        actual = row['actual_graph']
        caller = ['caller-origin', actual[2], actual[6], []]
        probe.check('--qirf-contract', envelope(original, qdv(view), qdv(caller)), 'caller')
        probe.check('--qirf-contract', envelope(original, qdv(view), qdv(['wrong-caller', *caller[1:]])),
                    error='decoded_view')


def callers(probe):
    for row in json.loads((FIXTURE / 'caller-alias-recipes.json').read_text()):
        original, graph = inner(row['artifact']), qdv(row['graph_view'])
        probe.check('--qirf-native', envelope(original, graph, qdv(row['view']), row['indices']), 'caller')
        wrong = qdv(['wrong-caller', *row['view'][1:]])
        probe.check('--qirf-native', envelope(original, graph, wrong, row['indices']), error='decoded_view')


def hierarchy(kernel, directory):
    probe = Probe(kernel)
    modes = ['--hierarchy-pending', '--hierarchy-request-pending', '--hierarchy-fourier-pending',
             '--instrument-pending', '--qpe-instrument-pending']
    for index, mode in enumerate(modes):
        original = (directory / f'{index}.bridge').read_bytes()
        graph = (directory / f'{index}.qdv').read_bytes()
        probe.check(mode, envelope(original), 'inspection')
        probe.check(mode, envelope(original, graph), 'execution')
        # Valid QDV1 framing with a different top-level record name.
        wrong = bytearray(graph)
        assert wrong[4] == 5 and wrong[9] == 4
        wrong[14] ^= 1
        probe.check(mode, envelope(original, bytes(wrong)), error='decoded_view')
        probe.check(mode, original, error='format')
        probe.check(mode, envelope(original, graph, qdv(['caller-origin']), []), error='format')
    return probe.count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kernel', type=Path, default=os.environ.get('QLEISLI_KERNEL',
                        ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'))
    args = parser.parse_args()
    probe = Probe(args.kernel.resolve())
    finite(probe)
    contracts(probe)
    callers(probe)
    print(f'QLV2 native finite/contract/caller checks: {probe.count} passed')


if __name__ == '__main__':
    main()
