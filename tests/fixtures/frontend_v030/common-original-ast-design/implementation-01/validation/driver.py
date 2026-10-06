#!/usr/bin/env python3
"""Fixed bounded commands; never execute stored result metadata.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
from pathlib import Path
import importlib.util
import sys
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]
PARENT = ROOT / 'tests/fixtures/frontend_v030/common-pattern-design/validation/driver.py'
spec = importlib.util.spec_from_file_location('reviewed_validation', PARENT)
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
base.HERE = HERE
base.TARGETS = base.TARGETS + (
    'source_judgments', 'operation_parameters', 'basis_polymorphism',
    'static_operations', 'static_semantics', 'certified_source', 'compile',
    'tuple_shapes', 'quantum_unit_source', 'predicate_domain', 'mixed_booleans',
    'ordinary_booleans', 'isometry_source', 'source_scope',
    'common_source_provider_access', 'sized_review_dialects',
)
base.FIXTURE_DIRECTORIES = base.FIXTURE_DIRECTORIES + (
    'tests/fixtures/authoring_sessions/common-provider-access-v030/attempt-01',
    'tests/fixtures/authoring_sessions/common-static-value-v030/attempt-01',
    'corpus/sized/qualtran_arithmetic', 'corpus/sized/qualtran_xor',
    'corpus/sized/katas_ghz',
)
base.FIXED_INPUTS = base.FIXED_INPUTS + (
    'corpus/manifest.json',
    'tests/fixtures/frontend_v030/common-original-ast-design/implementation-01/root-migrations-01/before.json',
    'tests/fixtures/frontend_v030/common-original-ast-design/implementation-01/root-migrations-01/initialization.after.json',
    'tests/fixtures/frontend_v030/common-original-ast-design/implementation-01/root-repairs-after-06/before.json',
    'tests/fixtures/frontend_v030/common-original-ast-design/implementation-01/root-repairs-after-06/after-authored.json',
    'tests/fixtures/authoring_sessions/common-provider-access-v030/first-files.json',
    str(PARENT.relative_to(ROOT)),
    'tests/fixtures/frontend_v030/common-original-ast-design/contract-01.md',
    'tests/fixtures/frontend_v030/common-original-ast-design/provider-access-clarification-01.md',
    'tests/fixtures/frontend_v030/common-original-ast-design/provider-access-before-code-01.json',
    'tests/fixtures/frontend_v030/common-original-ast-design/runtime-group-clarification-01.md',
    'tests/fixtures/frontend_v030/common-original-ast-design/runtime-group-before-code-01.json',
)
parent_commands = base.tool_commands

def original_commands(mode):
    commands = []
    for label, argv in parent_commands(mode):
        if label == 'focused-integration-tests':
            argv.insert(argv.index('--'), '--no-fail-fast')
        commands.append((label, argv))
        if label == 'focused-integration-tests':
            cargo = ['/opt/homebrew/bin/cargo'] if mode == 'latest' else [
                '/opt/homebrew/bin/rustup', 'run', '1.85.0', 'cargo']
            commands.append(('native-small-arithmetic-tests', cargo + [
                'test', '--locked', '--jobs=2', '--test', 'sized_review_dialects',
                'rust_arithmetic_and_ghz_proposals_preserve_small_reference_columns_natively',
                '--', '--ignored', '--nocapture', '--test-threads=2',
            ]))
    return tuple(commands)

base.tool_commands = original_commands

def compile_commands(mode):
    all_commands = original_commands(mode)
    return tuple(row for row in all_commands if row[0] in {
        'cargo-version', 'rustc-version', 'check-all-targets'})

if __name__ == '__main__':
    if len(sys.argv) == 4 and sys.argv[3] == 'compile':
        base.tool_commands = compile_commands
        sys.argv.pop()
    raise SystemExit(base.main())
