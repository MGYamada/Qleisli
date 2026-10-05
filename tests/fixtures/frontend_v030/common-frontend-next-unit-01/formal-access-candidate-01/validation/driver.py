#!/usr/bin/env python3
"""Fixed bounded actual-consumer validation for shared formal declarations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
from pathlib import Path
import hashlib
import importlib.util

HERE = Path(__file__).resolve().parent
ROOT = Path('/Users/masa/git/Qleisli')
PARENT = ROOT / 'tests/fixtures/frontend_v030/common-pattern-design/validation/driver.py'


def main():
    # Reviewed authored code, never a command read from an observation.
    expected = 'a9c33268c544dd12817f186472fd065ef76df82a617067e5605ac65267a78433'
    if hashlib.sha256(PARENT.read_bytes()).hexdigest() != expected:
        raise SystemExit('reviewed validation driver identity mismatch')
    spec = importlib.util.spec_from_file_location('bounded_formal_validation', PARENT)
    parent = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parent)
    parent.HERE = HERE
    parent.TARGETS += ('operation_parameters', 'basis_polymorphism')
    parent.FIXED_INPUTS += (
        PARENT.relative_to(ROOT).as_posix(),
        'tests/fixtures/frontend_v030/common-frontend-next-unit-01/formal-access-candidate-01/phased-contract-01.md',
        'tests/fixtures/frontend_v030/common-frontend-next-unit-01/formal-access-candidate-01/github-before-code-32.json',
        'tests/fixtures/authoring_sessions/common-formal-access-v030/first-files.json',
        'tests/fixtures/authoring_sessions/common-formal-access-v030/session.json',
    )
    parent.FIXTURE_DIRECTORIES += (
        'tests/fixtures/authoring_sessions/common-formal-access-v030/attempt-01',
    )
    return parent.main()


if __name__ == '__main__':
    raise SystemExit(main())
