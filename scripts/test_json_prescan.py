#!/usr/bin/env python3
"""Regression checks for #290's already-streaming JSON prescan.

Run actual parser decisions and bounded near-16-MiB host-memory probes. These
are transport tests, not quantum maximum-size cases or resource certificates.
Each RSS observation comes from a fresh helper with exactly one measured child,
so earlier compilers/children cannot inflate its high-water mark. macOS reports
bytes; Linux reports KiB. Original fixtures and production sources stay fixed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import struct
import subprocess
import sys
import tempfile
import time
import tomllib

import native_harness
from native_packet import envelope

ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / 'tests/json_prescan.lean'
MAX_BYTES = 16 * 1024 * 1024
SIZES = (1024 * 1024, 4 * 1024 * 1024, 8 * 1024 * 1024, MAX_BYTES - 65536)
# Test-only high-water envelope. Does not alter any production byte/work limit.
# The former List Char implementation (~1.1 GiB near the limit) exceeds this.
RSS_BASE_BYTES = 96 * 1024 * 1024
RSS_BYTES_PER_INPUT_BYTE = 16


def measure_child(command):
    import resource
    started = time.monotonic()
    result = subprocess.run(command, input=sys.stdin.buffer.read(), capture_output=True, timeout=60)
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    if sys.platform == 'linux':
        rss *= 1024
    return dict(returncode=result.returncode, stdout=result.stdout.decode('utf-8'),
                stderr=result.stderr.decode('utf-8'), peak_rss_bytes=rss,
                seconds=time.monotonic() - started)


def measured(command, payload=b''):
    result = subprocess.run([sys.executable, str(Path(__file__).resolve()), '--measure-child',
                             *map(str, command)], input=payload, capture_output=True, timeout=70)
    if result.returncode or result.stderr:
        raise ValueError(f'memory probe failed: {result.stderr!r}')
    return json.loads(result.stdout)


def cases():
    return [
        ('empty-object', b'{}', 128, True),
        ('nested-distinct-keys', b'{"a":{"a":0},"b":{"a":1}}', 128, True),
        ('escaped-distinct-keys', b'{"a":0,"\\u0062":1}', 128, True),
        ('unicode', '{"日本語":"\\\"😀\\\\"}'.encode(), 128, True),
        ('unsigned-max', b'[0,18446744073709551615,true,false,null]', 128, True),
        ('duplicate', b'{"a":0,"a":1}', 128, False),
        ('escaped-duplicate', b'{"a":0,"\\u0061":1}', 128, False),
        ('nested-duplicate', b'{"outer":{"x":0,"x":1}}', 128, False),
        ('leading-zero', b'[01]', 128, False),
        ('negative', b'[-1]', 128, False),
        ('fraction', b'[1.0]', 128, False),
        ('exponent', b'[1e0]', 128, False),
        ('u64-overflow', b'[18446744073709551616]', 128, False),
        ('too-many-digits', b'[111111111111111111111]', 128, False),
        ('depth-at-limit', b'[' * 128 + b']' * 128, 128, True),
        ('depth-over-limit', b'[' * 129 + b']' * 129, 128, False),
        ('finite-depth-at-limit', b'[' * 64 + b']' * 64, 64, True),
        ('finite-depth-over-limit', b'[' * 65 + b']' * 65, 64, False),
        ('trailing-data', b'{} {}', 128, False),
        ('wrong-close', b'{]', 128, False),
        ('unclosed', b'[[0]', 128, False),
        ('unterminated-string', b'"x', 128, False),
        ('unterminated-escape', b'"x\\', 128, False),
        ('bad-escape', b'"\\x"', 128, False),
        ('bad-unicode-escape', b'"\\u00zz"', 128, False),
        ('control-character', b'"\x00"', 128, False),
        ('field-count-at-limit', json.dumps({f'k{i}': 0 for i in range(64)}).encode(), 128, True),
        ('field-count-over-limit', json.dumps({f'k{i}': 0 for i in range(65)}).encode(), 128, False),
        ('key-at-limit', b'{"' + b'x' * 4094 + b'":0}', 128, True),
        ('key-over-limit', b'{"' + b'x' * 4095 + b'":0}', 128, False),
        ('bytes-at-limit', b'"' + b'x' * (MAX_BYTES - 2) + b'"', 128, True),
        ('bytes-over-limit', b'"' + b'x' * (MAX_BYTES - 1) + b'"', 128, False),
    ]


def large_input(kind, size):
    if kind == 'string':
        return b'"' + b'x' * (size - 2) + b'"'
    # Many small values, kept below the independent 1M-value limit even at 16 MiB.
    count = min(800000, (size - 2) // 20)
    prefix = b'[' + b'0,                  ' * (count - 1) + b'0]'
    return prefix + b' ' * (size - len(prefix))


def checked_response(row, expected, native=False):
    if row['stderr']:
        raise ValueError(f"unexpected child stderr: {row}")
    if native:
        # Memory bodies are valid JSON but deliberately not QIRF envelopes.
        if row['returncode'] != 1 or row['stdout'] != 'qleisli.native-result 3\nerror\ninvalid_ir\n':
            raise ValueError(f"unexpected native refusal (crashes are not rejections): {row}")
    elif expected:
        if row['returncode'] != 0 or row['stdout'] != 'accepted\n':
            raise ValueError(f"valid JSON refused: {row}")
    elif row['returncode'] != 1 or not row['stdout'].startswith('error\n'):
        raise ValueError(f"invalid JSON accepted or parser failed: {row}")


def checked_memory(row):
    if not 0 < row['peak_rss_bytes'] <= row['rss_ceiling_bytes']:
        raise ValueError(f'JSON memory regression: {row}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path, required=True)
    parser.add_argument('--kernel', type=Path, default=ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel')
    args = parser.parse_args()
    if sys.platform not in ('darwin', 'linux'):
        raise ValueError('RSS regression requires macOS or Linux; no skipped success')
    args.record.mkdir(parents=True, exist_ok=False)
    before = native_harness.source_identity()
    kernel = args.kernel.resolve()
    identities = dict(kernel=native_harness.digest(kernel), driver=native_harness.digest(DRIVER),
                      harness=native_harness.digest(Path(__file__)))
    report = dict(format='qleisli.json-prescan-regression', version=1, status='failed',
                  platform=platform.platform(), baseline_commit=subprocess.check_output(
                      ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                  identities=identities, cases=[], memory=[], commands=[],
                  scope='JSON decisions and host RSS only; no QIRF acceptance or resource theorem')
    try:
        with tempfile.TemporaryDirectory(prefix='qleisli-json-prescan-') as temporary:
            project = Path(temporary)
            (project / 'Main.lean').write_bytes(DRIVER.read_bytes())
            driver = native_harness.build(project, report['commands'])
            report['driver_binary_sha256'] = native_harness.digest(driver)
            path = project / 'input.json'
            for name, payload, depth, expected in cases():
                path.write_bytes(payload)
                row = measured([driver, path, depth])
                row.update(name=name, input_sha256=hashlib.sha256(payload).hexdigest(),
                           bytes=len(payload), depth=depth, expected=expected)
                report['cases'].append(row)
                checked_response(row, expected)
            # Product identity comes from Cargo, not a historical fixture/version guess.
            version = tomllib.loads((ROOT / 'Cargo.toml').read_text())['package']['version']
            for kind in ('string', 'array'):
                for size in SIZES:
                    payload = large_input(kind, size)
                    assert len(payload) == size
                    path.write_bytes(payload)
                    for boundary in ('parser', 'native'):
                        if boundary == 'parser':
                            row = measured([driver, path, 128])
                        else:
                            packet = envelope('2026', b'QLV1' + struct.pack('<II', size, 0) + payload)
                            row = measured([kernel, '--qirf-native', version], packet)
                        row.update(kind=kind, boundary=boundary, bytes=size,
                                   input_sha256=hashlib.sha256(payload).hexdigest(),
                                   rss_ceiling_bytes=RSS_BASE_BYTES + RSS_BYTES_PER_INPUT_BYTE * size)
                        report['memory'].append(row)
                        checked_response(row, True, native=boundary == 'native')
                        checked_memory(row)
        if before != native_harness.source_identity() or identities != dict(
                kernel=native_harness.digest(kernel), driver=native_harness.digest(DRIVER),
                harness=native_harness.digest(Path(__file__))):
            raise ValueError('sources or measured binary changed during the run')
        report['status'] = 'passed'
    except Exception as error:
        report['error'] = str(error)
        raise
    finally:
        (args.record / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f"JSON prescan: {len(report['cases'])} decisions and {len(report['memory'])} RSS probes passed")
    return 0


if __name__ == '__main__':
    if sys.argv[1:2] == ['--measure-child']:
        print(json.dumps(measure_child(sys.argv[2:])))
    else:
        raise SystemExit(main())
