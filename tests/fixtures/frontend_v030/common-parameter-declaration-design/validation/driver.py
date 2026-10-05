#!/usr/bin/env python3
"""Bounded parameter-declaration validation using the reviewed fixed driver.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
from pathlib import Path
import hashlib
import importlib.util

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
PARENT = ROOT / 'tests/fixtures/frontend_v030/common-pattern-design/validation/driver.py'


def main():
    # This imports authored code, never argv or executable code from a record.
    # The parent has no import-time subprocess and its __main__ guard is false.
    expected = 'a9c33268c544dd12817f186472fd065ef76df82a617067e5605ac65267a78433'
    digest = hashlib.sha256(PARENT.read_bytes()).hexdigest()
    if digest != expected:
        raise SystemExit('reviewed validation driver identity mismatch')
    spec = importlib.util.spec_from_file_location('bounded_pattern_validation', PARENT)
    parent = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parent)
    parent.HERE = HERE
    parent.FIXED_INPUTS += (
        PARENT.relative_to(ROOT).as_posix(),
        'tests/fixtures/frontend_v030/common-parameter-declaration-design/candidate-01.md',
        'tests/fixtures/frontend_v030/common-parameter-declaration-design/author-design.md',
        'tests/fixtures/frontend_v030/common-parameter-declaration-design/contract-before-code.md',
        'tests/fixtures/authoring_sessions/common-parameter-declaration-v030/first-files.json',
        'tests/fixtures/authoring_sessions/common-parameter-declaration-v030/session.json',
        'tests/fixtures/authoring_sessions/common-parameter-declaration-v030/results-before.md',
    )
    parent.FIXTURE_DIRECTORIES += (
        'tests/fixtures/authoring_sessions/common-parameter-declaration-v030/attempt-01',
    )
    return parent.main()


if __name__ == '__main__':
    raise SystemExit(main())
