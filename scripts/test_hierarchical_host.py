#!/usr/bin/env python3
"""Fresh hierarchy/finite host checks and independent binary-boundary faults.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This validates reconstruction, not an independently requested production root.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import struct
import subprocess
import time
import tomllib

ROOT = Path(__file__).resolve().parent.parent
PRODUCT_VERSION = tomllib.loads((ROOT / 'Cargo.toml').read_text())['package']['version']


def phase_bridge():
    # Handwritten fixture independent of the Rust external codec. One Bit
    # phase, identical identity encodings, and its actual phase equation.
    port = [0, 1, 1, 1, 7]  # owner, type-atom count, Bit, axis count, axis
    side = [1, *port, 0]  # one quantum port, zero classical ports
    interface = side + side
    definition = interface + [0, 9, 0, 1, 8]  # unitary, phase(target=0,j=1,k=8)
    meaning = interface + [9, 1, 8]
    encoding = side + side + [0]
    proof = [0, 9, 0, 0, 0, 0, 1, 1, 0, 0]  # equation, phase, no premises; witness v1
    words = [1, *definition, 1, *meaning, 2, *encoding, *encoding, 1, *proof,
             0, 0, 5, 0, 1, 2, 3, 4]
    return b'QLH1' + struct.pack('<' + 'I' * len(words), *words)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    parser.add_argument('--cargo', default='cargo')
    args = parser.parse_args()
    binary = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
    if not binary.is_file():
        raise SystemExit('Build lean-kernel before running host validation')
    good = phase_bridge()
    cases = [('phase', good, 'pending'), ('magic', b'BAD1' + good[4:], 'format'),
             ('trailing', good + b'\0', 'format'), ('empty', b'', 'format'),
             ('huge-table', b'QLH1' + struct.pack('<I', 100001), 'limit')]
    # Every framing truncation must fail, including inside a four-byte number.
    cases.extend((f'truncated-{i}', good[:i], 'format') for i in range(1, len(good)))
    # A schedule is a proposal: duplicate and reversed entries are rejected.
    cases.append(('schedule-duplicate', good[:-4] + struct.pack('<I', 3), 'invalid_ir'))
    cases.append(('schedule-reversed', good[:-20] + struct.pack('<5I', 4, 3, 2, 1, 0), 'invalid_ir'))
    start = time.monotonic()
    for name, data, expected in cases:
        result = subprocess.run([str(binary), '--hierarchy-pending', PRODUCT_VERSION], input=data,
                                capture_output=True, timeout=30)
        lines = result.stdout.decode().splitlines()
        if lines[:2] == ['qleisli.hierarchy-pending 3', 'pending']:
            actual = 'pending'
            assert result.returncode == 0 and lines[4] == '0', (name, lines)
        else:
            assert lines[:2] == ['qleisli.hierarchy-pending 3', 'error'], (name, result)
            assert result.returncode != 0 and len(lines) == 3, (name, result)
            actual = lines[2]
        assert actual == expected, (name, expected, actual)
    env = os.environ.copy()
    env['QLEISLI_HIERARCHY_KERNEL'] = str(binary)
    command = [args.cargo, 'test', '--test', 'hierarchical_host', '--', '--ignored', '--nocapture']
    result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True, timeout=120)
    report = {'format': 'qleisli.hierarchy-host-validation', 'version': 1,
              'status': 'passed' if result.returncode == 0 else 'failed',
              'binary_sha256': hashlib.sha256(binary.read_bytes()).hexdigest(),
              'binary_cases': len(cases), 'seconds': round(time.monotonic()-start, 3),
              'host_command': command, 'exit_code': result.returncode,
              'stdout': result.stdout, 'stderr': result.stderr}
    if args.record:
        args.record.write_text(json.dumps(report, indent=2) + '\n')
    if result.returncode:
        print(result.stdout + result.stderr)
    print(json.dumps({k: v for k, v in report.items() if k not in ('stdout', 'stderr')}))
    return bool(result.returncode)


if __name__ == '__main__':
    raise SystemExit(main())
