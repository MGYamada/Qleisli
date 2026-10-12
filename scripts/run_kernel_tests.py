#!/usr/bin/env python3
"""Run a native Rust test command and reject conditional native skips.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import os
from pathlib import Path
import re
import subprocess
import sys

SKIP_REASON = 'native-kernel gate: requires QLEISLI_KERNEL'
SUMMARY = re.compile(r'^test result: ok\. (\d+) passed; \d+ failed; \d+ ignored;')


def run(command):
    kernel = os.environ.get('QLEISLI_KERNEL', '')
    if not kernel or not Path(kernel).is_file() or not os.access(kernel, os.X_OK):
        print('native test gate: select an executable QLEISLI_KERNEL', file=sys.stderr)
        return 1
    skipped = False
    passed = 0
    try:
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True, errors='replace')
        assert process.stdout is not None
        for line in process.stdout:
            print(line, end='', flush=True)
            skipped |= SKIP_REASON in line and 'ignored' in line
            if match := SUMMARY.match(line):
                passed += int(match[1])
        status = process.wait()
    except OSError as error:
        print(f'native test gate: {error}', file=sys.stderr)
        return 1
    if status:
        return status if status > 0 else 1
    if skipped or not passed:
        print('native test gate: conditional native tests were skipped or no tests passed',
              file=sys.stderr)
        return 1
    print('native test gate: zero conditional native skips')
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command:
        parser.error('a Rust test command is required')
    return run(command)


if __name__ == '__main__':
    sys.exit(main())
