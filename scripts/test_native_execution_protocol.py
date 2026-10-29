#!/usr/bin/env python3
"""Exercise QLV3 through the actual native executable, using retained small vectors.
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

from native_packet import envelope, parse_reply, MODES

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


def check_response_contexts():
    """Synthetic framing negatives supplement, never replace, native decisions."""
    assert len(MODES) == 16
    for mode, (claim, scopes) in MODES.items():
        for scope in scopes:
            frame = f'qleisli.native-result 3\n{claim}\n2026\n{VERSION}\n{mode}\n{scope}\n42\n'.encode()
            context = dict(edition='2026', product=VERSION, mode=mode, scope=scope)
            reply = parse_reply(frame, **context)
            assert reply.claim == claim and reply.payload == ('42',)
            assert (reply.context.edition, reply.context.product, reply.context.mode,
                    reply.context.scope) == ('2026', VERSION, mode, scope)
            for changed in (
                    frame.replace(b'native-result 3', b'qirf-native 2'),
                    frame.replace(b'\n2026\n', b'\n2027\n'),
                    frame.replace(b'\n2026\n', b'\n02026\n'),
                    frame.replace(VERSION.encode(), b'0.0.0'),
                    frame.replace(mode.encode(), b'--unknown-native-mode'),
                    frame.replace(f'\n{scope}\n'.encode(), b'\nwrong-scope\n'),
                    frame.replace(f'\n{claim}\n'.encode(), b'\nunverified\n'),
                    frame.replace(b'\n42\n', b'\n042\n'),
                    frame.replace(b'\n42\n', b'\n42 \n'),
                    frame[:-1], frame + b'\n', frame + b'extra\n'):
                try:
                    parse_reply(changed, **context)
                except ValueError:
                    pass
                else:
                    raise AssertionError(('ambiguous context accepted', changed))
        for code in ('format', 'limit', 'contract', 'invalid_ir', 'decoded_view', 'version', 'edition'):
            frame = f'qleisli.native-result 3\nerror\n{code}\n'.encode()
            context = dict(edition='2026', product=VERSION, mode=mode, scope=scopes[0])
            reply = parse_reply(frame, **context)
            assert reply.error == code and reply.context is None
            for changed in (frame[:-1], frame + b'0\n', frame.replace(code.encode(), b'unknown')):
                try:
                    parse_reply(changed, **context)
                except ValueError:
                    pass
                else:
                    raise AssertionError(('ambiguous failure accepted', changed))
    for edition in (None, 2026, 'latest', 'current', '*', '2027'):
        try:
            envelope(edition, b'original')
        except ValueError:
            pass
        else:
            raise AssertionError(('implicit or unsupported edition', edition))
    framed = envelope('2026', b'original', b'graph', b'caller', (7,))
    assert framed[:28] == b'QLV3' + struct.pack('<6I', 2026, 2, 8, 5, 6, 1)
    assert framed[28:] == b'originalgraphcaller' + struct.pack('<I', 7)


class Probe:
    def __init__(self, kernel, *, edition):
        self.kernel = kernel
        self.edition = edition
        self.count = 0

    def check(self, mode, data, scope=None, error=None):
        result = subprocess.run([str(self.kernel), mode, VERSION], input=data,
                                capture_output=True, timeout=60)
        self.count += 1
        reply = parse_reply(result.stdout, edition=self.edition, product=VERSION,
                            mode=mode, scope=scope or 'inspection')
        if error:
            expected = error if isinstance(error, tuple) else (error,)
            assert result.returncode == 1 and reply.error in expected, (mode, result)
        else:
            assert result.returncode == 0 and reply.claim in ('accepted', 'pending'), (mode, result)
            assert reply.context.scope == scope, (scope, result)
            if reply.claim == 'accepted':
                assert len(reply.payload) == 2 and 0 <= int(reply.payload[0]) <= 10_000_000, reply
                requested = mode in ('--qirf-contract', '--carrier-pure-check',
                                     '--ordinary-root-check', '--qmatch-source-check')
                assert reply.payload[1] == ('1' if requested else '0'), reply
            else:
                check_pending_payload(mode, reply.payload)
        return reply


def check_pending_payload(mode, payload):
    assert len(payload) >= 3 and 0 <= int(payload[0]) <= 2_000_000, payload
    assert 0 <= int(payload[1]) <= 10_000_000, payload
    bounds = [100_000]
    if mode != '--hierarchy-pending':
        bounds.append(8 if mode == '--hierarchy-fourier-pending' else 100_000)
    if mode == '--qpe-instrument-pending':
        bounds.append(16)
    position = 2
    for bound in bounds:
        assert position < len(payload), payload
        count = int(payload[position]); position += 1
        assert count <= bound and position + count <= len(payload), payload
        assert all(0 <= int(value) <= 99_999 for value in payload[position:position + count]), payload
        position += count
    assert position == len(payload), payload


def finite(probe):
    rows = json.loads((FIXTURE / 'finite-graph-vectors.json').read_text())
    for row in rows:
        original = inner(row['artifact'])
        view = qdv(row['view'])
        probe.check('--qirf-native', envelope('2026', original), 'inspection')
        probe.check('--qirf-native', envelope('2026', original, view), 'execution')
        wrong = qdv(['wrong-graph', *row['view'][1:]])
        probe.check('--qirf-native', envelope('2026', original, wrong), error='decoded_view')
        probe.check('--qirf-native', original, error='format')
    original = inner(rows[0]['artifact'])
    good = envelope('2026', original, qdv(rows[0]['view']))
    for bad in [good + b'x', good[:-1], b'QLV1' + good[4:], b'QLV2' + good[4:],
                good[:8] + struct.pack('<I', 99) + good[12:],
                good[:8] + struct.pack('<I', 0) + good[12:],
                good[:24] + struct.pack('<I', 100001) + good[28:]]:
        probe.check('--qirf-native', bad, error='format')
    for edition in (0, 2027, 2**32 - 1):
        probe.check('--qirf-native', good[:4] + struct.pack('<I', edition) + good[8:], error='edition')


def contracts(probe):
    sources = json.loads((FIXTURE / 'contract-walker-vectors.json').read_text())
    for row in json.loads((FIXTURE / 'complete-contract-vectors.json').read_text()):
        source = sources[row['source_index']]
        request = source['request'] | ({'expected_artifact': row['expected_artifact']}
                                      if 'expected_artifact' in row else {})
        original = inner(source['artifact'], request)
        view = ['native-contract', source['view'], row['actual_graph'], row['expected_graph']]
        probe.check('--qirf-contract', envelope('2026', original), 'inspection')
        probe.check('--qirf-contract', envelope('2026', original, qdv(view)), 'execution')
        probe.check('--qirf-contract', envelope('2026', original, qdv(['wrong-contract', *view[1:]])),
                    error='decoded_view')
        probe.check('--qirf-contract', original, error='format')
        actual = row['actual_graph']
        caller = ['caller-origin', actual[2], actual[6], []]
        probe.check('--qirf-contract', envelope('2026', original, qdv(view), qdv(caller)), 'caller')
        probe.check('--qirf-contract', envelope('2026', original, qdv(view), qdv(['wrong-caller', *caller[1:]])),
                    error='decoded_view')


def callers(probe):
    for row in json.loads((FIXTURE / 'caller-alias-recipes.json').read_text()):
        original, graph = inner(row['artifact']), qdv(row['graph_view'])
        probe.check('--qirf-native', envelope('2026', original, graph, qdv(row['view']), row['indices']), 'caller')
        wrong = qdv(['wrong-caller', *row['view'][1:]])
        probe.check('--qirf-native', envelope('2026', original, graph, wrong, row['indices']), error='decoded_view')


def qmatch(probe):
    path = ROOT / 'tests/fixtures/qmatch_v030/execution-cases.json'
    rows = json.loads(path.read_text())['cases']
    assert len(rows) == 26
    for row in rows:
        original = inner(row['artifact'], row['request'])
        graph = qdv(row['view'])
        error = (None if row['accepted'] else 'decoded_view'
                 if row['error'] == 'decodedView' else ('invalid_ir', 'contract', 'limit'))
        probe.check('--qmatch-source-check', envelope('2026', original, graph),
                    'execution', error=error)
        if row['accepted']:
            probe.check('--qmatch-source-check', envelope('2026', original), error='format')
            probe.check('--qmatch-source-check', envelope('2026', original, graph, qdv([])),
                        'caller', error='format')
            probe.check('--qmatch-source-check', original, error='format')
            probe.check('--qmatch-source-check', envelope('2026', original, b'QDV1'),
                        'execution', error='format')


def hierarchy(kernel, directory):
    probe = Probe(kernel, edition='2026')
    modes = ['--hierarchy-pending', '--hierarchy-request-pending', '--hierarchy-fourier-pending',
             '--instrument-pending', '--qpe-instrument-pending']
    for index, mode in enumerate(modes):
        original = (directory / f'{index}.bridge').read_bytes()
        graph = (directory / f'{index}.qdv').read_bytes()
        probe.check(mode, envelope('2026', original), 'inspection')
        probe.check(mode, envelope('2026', original, graph), 'execution')
        # Valid QDV1 framing with a different top-level record name.
        wrong = bytearray(graph)
        assert wrong[4] == 5 and wrong[9] == 4
        wrong[14] ^= 1
        probe.check(mode, envelope('2026', original, bytes(wrong)), error='decoded_view')
        probe.check(mode, original, error='format')
        probe.check(mode, envelope('2026', original, graph, qdv(['caller-origin']), []), error='format')
    return probe.count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kernel', type=Path, default=os.environ.get('QLEISLI_KERNEL',
                        ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'))
    args = parser.parse_args()
    check_response_contexts()
    probe = Probe(args.kernel.resolve(), edition='2026')
    finite(probe)
    contracts(probe)
    callers(probe)
    qmatch(probe)
    print(f'QLV3 native finite/contract/caller/qmatch checks: {probe.count} passed')


if __name__ == '__main__':
    main()
