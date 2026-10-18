#!/usr/bin/env python3
"""Calibrate typed source growth and exhaustive selected-adapter handling.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

from check_verification_inventory import check_language_primitives

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='qleisli-catalog-mutation-') as directory:
        copy = Path(directory)
        for name in ('Cargo.toml', 'Cargo.lock'):
            shutil.copy2(ROOT / name, copy / name)
        for name in ('src', 'stdlib'):
            shutil.copytree(ROOT / name, copy / name)
        language = copy / 'src/frontend/primitive.rs'
        original_language = language.read_text()
        assert original_language.count('pub enum PrimitiveId {') == 1
        language.write_text(original_language.replace(
            'pub enum PrimitiveId {', 'pub enum PrimitiveId { OmittedSourcePrimitive,', 1))
        try:
            check_language_primitives(copy)
        except ValueError as error:
            assert 'unreviewed typed language primitive identity set' in str(error), error
        else:
            raise AssertionError('unreviewed source primitive growth was accepted')
        language.write_text(original_language)
        check_language_primitives(copy)
        path = copy / 'src/frontend/specialize/primitive.rs'
        text = path.read_text()
        assert text.count('primitives! {') == 1
        path.write_text(text.replace('primitives! {', '''primitives! {
    OmittedPrimitive => (0, Fixed(&[Bit], Bit), Unitary, None),''', 1))
        command = ['cargo', 'check', '--offline', '--lib', '--target-dir', str(copy / 'target')]
        result = subprocess.run(command, cwd=copy, capture_output=True, text=True, timeout=180)
        assert result.returncode != 0, 'unhandled primitive compiled'
        assert 'Primitive::OmittedPrimitive' in result.stderr, result.stderr
        passes = ['src/frontend/specialize/elaborate.rs', 'src/frontend/specialize/lower.rs',
                  'src/frontend/specialize/lower/preservation.rs']
        for name in passes:
            assert name in result.stderr, result.stderr
        report = dict(format='qleisli.primitive-omission-validation', version=1,
                      status='detected', mutation='unhandled-selected-adapter-row',
                      source_mutation='extra-typed-source-identity', source_status='detected',
                      required_passes=passes, command=command, exit_code=result.returncode,
                      diagnostics=result.stderr.replace(str(copy), '<temporary-checkout>'))
        if args.record:
            args.record.write_text(json.dumps(report, indent=2) + '\n')
        print('Typed source growth rejected; omitted selected adapter rejected by preparation, lowering and preservation.')


if __name__ == '__main__':
    main()
