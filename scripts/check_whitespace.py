#!/usr/bin/env python3
"""Check the whole source tree with Git's whitespace rules and attributes.

The default includes working changes and non-ignored untracked inputs, so the
same check can run before a commit and in a clean hosted checkout.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def check(root: Path, committed: bool = False) -> bool:
    empty = subprocess.check_output(
        ['git', 'hash-object', '-t', 'tree', '--stdin'], cwd=root, input=b'').decode().strip()
    command = ['git', 'diff', '--check', '--no-ext-diff', empty]
    if committed:
        command.append('HEAD')
    result = subprocess.run([*command, '--'], cwd=root)
    passed = result.returncode == 0
    if not committed:
        names = subprocess.check_output(
            ['git', 'ls-files', '--others', '--exclude-standard', '-z'], cwd=root)
        for name in names.split(b'\0'):
            if name:
                result = subprocess.run(
                    ['git', 'diff', '--no-index', '--check', '--no-ext-diff',
                     '--', os.devnull, os.fsdecode(name)], cwd=root,
                    stderr=subprocess.PIPE, text=True)
                # --no-index adds exit bit 1 for a difference, even when clean.
                # Read errors can also return 1; never count a Git diagnostic as
                # a clean difference (for example, an input removed mid-check).
                if result.stderr:
                    print(result.stderr, end='', file=sys.stderr)
                passed = result.returncode in (0, 1) and not result.stderr and passed
    return passed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--committed', action='store_true', help='inspect HEAD only')
    args = parser.parse_args()
    try:
        if not check(ROOT, args.committed):
            return 1
    except (OSError, subprocess.SubprocessError) as error:
        print(f'Whitespace check: {error}', file=sys.stderr)
        return 1
    print('Git whitespace checks passed for the complete ' +
          ('committed tree.' if args.committed else 'working source tree.'))
    return 0


if __name__ == '__main__':
    sys.exit(main())
