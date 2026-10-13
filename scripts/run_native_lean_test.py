#!/usr/bin/env python3
"""Compile and run an unchanged Lean comparison driver with the current kernel.
This is test execution, not a proof of native compilation or runtime preservation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
from pathlib import Path
import sys
import tempfile

import native_harness


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('arguments', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    source = args.source.resolve()
    original = source.read_bytes()
    log = []
    with tempfile.TemporaryDirectory(prefix='qleisli-native-lean-test-') as temporary:
        project = Path(temporary)
        (project / 'Main.lean').write_bytes(original)
        binary = native_harness.build(project, log)
        if source.read_bytes() != original:
            raise ValueError('comparison source changed during native compilation')
        output = native_harness.run([str(binary), *args.arguments], native_harness.ROOT, log)
        print(output, end='', flush=True)
        print(log[-1]['stderr'], end='', file=sys.stderr, flush=True)
        if source.read_bytes() != original:
            raise ValueError('comparison source changed during execution')
    return 0


if __name__ == '__main__':
    sys.exit(main())
