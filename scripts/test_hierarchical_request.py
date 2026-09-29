#!/usr/bin/env python3
"""Independent root-request framing, graph-proposal and contract mutations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The handwritten transport never invokes the Rust proposal producer.
"""
import argparse
import hashlib
import json
from pathlib import Path
import struct
import subprocess
import time

from test_hierarchical_host import phase_bridge

ROOT = Path(__file__).resolve().parent.parent


def request_bridge(*, meanings=1, pairs=None, order=None):
    embedded = phase_bridge()
    words = []
    fields = {}

    def put(name, values):
        fields[name] = 8 + len(embedded) + 4 * len(words)
        words.extend(values)

    side = [1, 0, 1, 1, 1, 7, 0]
    interface = side + side
    put('kind', [0])
    put('effect', [0])
    put('interface', interface)
    put('meaning_count', [meanings])
    for i in range(meanings):
        put(f'meaning_{i}', interface)
        put(f'body_{i}', [9, 1, 8])
    put('entry', [0])
    pairs = [(0, 0, [])] if pairs is None else pairs
    order = list(range(len(pairs))) if order is None else order
    put('pair_count', [len(pairs)])
    for i, (a, r, children) in enumerate(pairs):
        put(f'pair_{i}', [a, r, len(children), *children])
    put('order', [len(order), *order])
    return (b'QLR1' + struct.pack('<I', len(embedded)) + embedded
            + struct.pack('<' + 'I' * len(words), *words)), fields


def replace_word(data, offset, value):
    return data[:offset] + struct.pack('<I', value) + data[offset+4:]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    binary = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
    good, fields = request_bridge()
    cases = [('phase-match', good, 'pending'), ('magic', b'NOPE' + good[4:], 'format'),
             ('trailing', good+b'\0', 'format'), ('empty', b'', 'format')]
    cases += [(f'truncated-{i}', good[:i], 'format') for i in range(1, len(good))]
    for name, field, delta, value, expected in [
            ('embedded-too-large', None, 4, 67108865, 'limit'),
            ('unknown-kind', 'kind', 0, 2, 'format'),
            ('instrument-kind', 'kind', 0, 1, 'contract'),
            ('unknown-effect', 'effect', 0, 3, 'format'),
            ('observe-effect', 'effect', 0, 2, 'contract'),
            ('header-owner', 'interface', 4, 8, 'contract'),
            ('header-axis', 'interface', 20, 8, 'contract'),
            ('meaning-owner', 'meaning_0', 4, 8, 'contract'),
            ('phase-exponent', 'body_0', 8, 7, 'contract'),
            ('unknown-constructor', 'body_0', 0, 12, 'format'),
            ('missing-entry', 'entry', 0, 1, 'contract'),
            ('missing-actual-node', 'pair_0', 0, 1, 'contract'),
            ('missing-requested-node', 'pair_0', 4, 1, 'contract'),
            ('wrong-order-index', 'order', 4, 1, 'invalid_ir'),
            ('huge-meaning-count', 'meaning_count', 0, 100001, 'limit'),
            ('huge-pair-count', 'pair_count', 0, 100001, 'limit'),
            ('huge-order-count', 'order', 0, 100001, 'limit')]:
        offset = fields[field] if field else 0
        cases.append((name, replace_word(good, offset+delta, value), expected))
    for j in range(256):
        cases.append((f'independent-phase-{j}', replace_word(good, fields['body_0']+4, j),
                      'pending' if j == 1 else 'contract'))
    for name, kwargs, expected in [
            ('uncovered-request', {'meanings': 2}, 'contract'),
            ('missing-request', {'meanings': 0}, 'limit'),
            ('missing-pairs', {'pairs': []}, 'limit'),
            ('pair-cycle', {'pairs': [(0,0,[0])]}, 'invalid_ir'),
            ('missing-child-pair', {'pairs': [(0,0,[1])]}, 'invalid_ir'),
            ('unreachable-pair', {'pairs': [(0,0,[]),(0,0,[])]}, 'invalid_ir'),
            ('aggregate-pair-work', {'pairs': [(0,0,[])] * 5000}, 'limit'),
            ('missing-order', {'order': []}, 'invalid_ir'),
            ('duplicate-order', {'order': [0,0]}, 'invalid_ir')]:
        cases.append((name, request_bridge(**kwargs)[0], expected))
    started = time.monotonic()
    observed = []
    for name, data, expected in cases:
        result = subprocess.run([str(binary), '--hierarchy-request-pending'], input=data,
                                capture_output=True, timeout=30)
        lines = result.stdout.decode().splitlines()
        assert lines[:1] == ['qleisli.hierarchy-request-pending 1'], (name, result)
        if lines[1:2] == ['pending']:
            actual = 'pending'
            assert result.returncode == 0 and len(lines) == 5 and lines[3:] == ['0','0'], (name, lines)
            assert 0 < int(lines[2]) <= 2_000_000, (name, lines)
        else:
            assert result.returncode == 1 and lines[1:2] == ['error'] and len(lines) == 3, (name, result)
            actual = lines[2]
        assert actual == expected, (name, expected, actual)
        observed.append({'case': name, 'result': actual})
    record = {'format': 'qleisli.hierarchy-root-request-validation', 'version': 1,
              'status': 'passed', 'cases': len(cases), 'results': observed,
              'seconds': round(time.monotonic()-started,3),
              'binary_sha256': hashlib.sha256(binary.read_bytes()).hexdigest()}
    if args.record:
        args.record.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({k:v for k,v in record.items() if k != 'results'}))


if __name__ == '__main__':
    main()
