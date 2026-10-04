#!/usr/bin/env python3
"""Bounded diagnostic/proposal replay; saved records are data, never commands.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tree', type=Path, required=True)
    parser.add_argument('--kernel', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    tree, kernel, out = args.tree.resolve(), args.kernel.resolve(), args.output_dir.resolve()
    here = Path(__file__).resolve().parent
    out.mkdir(parents=True, exist_ok=True)
    records = []

    def run(label, argv):
        result = subprocess.run(argv, cwd=tree, capture_output=True, timeout=120)
        stdout, stderr = label + '.stdout', label + '.stderr'
        (out / stdout).write_bytes(result.stdout)
        (out / stderr).write_bytes(result.stderr)
        records.append(dict(label=label, argv=argv, cwd=str(tree), exit_code=result.returncode, stdout=stdout, stderr=stderr))
        (out / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
        return result.returncode

    assert run('build', ['cargo', 'build', '--offline', '--lib', '--bin', 'qleisli']) == 0
    observe = out / 'observe'
    assert run('observer-build', ['rustc', '--edition=2024', str(here / 'initial-study/observe.rs'), '--extern', 'qleisli=' + str(tree / 'target/debug/libqleisli.rlib'), '-L', 'dependency=' + str(tree / 'target/debug/deps'), '-o', str(observe)]) == 0
    for source in sorted((here / 'initial-study').glob('*/main.qli')):
        name = source.parent.name
        assert run(name + '-observer', [str(observe), str(source)]) == 0
        if not name.startswith('sized-') and name != 'basis-generic':
            assert run(name + '-check', [str(tree / 'target/debug/qleisli'), 'check', str(source.parent), '--format=json', '--lean-kernel=' + str(kernel)]) in (0, 1)
    proposals = []
    for name, directory, bindings in [
        ('shared', here.parent / 'common-parser', []),
        ('contextual-type-name', here.parent / 'common-parser', []),
        ('static-fold', here.parent / 'common-parser', ['--nat=n=1']),
        ('empty-owner', here.parent / 'common-parser', []),
        *[(name, here / 'proposal-sources', []) for name in ['h', 'pair', 'register-two', 'measured-one']],
    ]:
        source = directory / (name + '.qli')
        output = out / (name + '.proposal.json')
        code = run(name + '-proposal', [str(tree / 'target/debug/qleisli'), 'sized', 'emit-proposal', '--entry=main::f', '--module=main=' + str(source), *bindings, '--output=' + str(output)])
        proposals.append(dict(name=name, source=str(source), source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(), exit_code=code, output=output.name, sha256=hashlib.sha256(output.read_bytes()).hexdigest() if code == 0 else None))
    (out / 'proposals.json').write_text(json.dumps(proposals, indent=2) + '\n')
    print(f'Saved 22 syntax/profile observations, 12 native source checks and {len(proposals)} proposal attempts to {out}')


if __name__ == '__main__':
    main()
