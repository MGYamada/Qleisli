#!/usr/bin/env python3
"""Calibrate exhaustive primitive handling with a compile-time omission fault.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

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
        path = copy / 'src/frontend/specialize/primitive.rs'
        text = path.read_text()
        assert text.count('primitives! {') == 1
        path.write_text(text.replace('primitives! {', '''primitives! {
    OmittedPrimitive => ("std::quantum::omitted", 0, Fixed(&[Bit], Bit), Unitary, None),''', 1))
        command = ['cargo', 'check', '--offline', '--lib', '--target-dir', str(copy / 'target')]
        result = subprocess.run(command, cwd=copy, capture_output=True, text=True, timeout=180)
        assert result.returncode != 0, 'unhandled primitive compiled'
        assert 'Primitive::OmittedPrimitive' in result.stderr, result.stderr
        passes = ['src/frontend/specialize/elaborate.rs', 'src/frontend/specialize/lower.rs',
                  'src/frontend/specialize/lower/preservation.rs']
        for name in passes:
            assert name in result.stderr, result.stderr
        report = dict(format='qleisli.primitive-omission-validation', version=1,
                      status='detected', mutation='unhandled-primitive-catalog-row',
                      required_passes=passes, command=command, exit_code=result.returncode,
                      diagnostics=result.stderr.replace(str(copy), '<temporary-checkout>'))
        if args.record:
            args.record.write_text(json.dumps(report, indent=2) + '\n')
        print('Omitted primitive rejected by concrete preparation, lowering and preservation.')


if __name__ == '__main__':
    main()
