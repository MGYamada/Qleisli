#!/usr/bin/env python3
"""Replay bounded lexical observations and one-qubit proposal comparisons.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import hashlib
import json
import os
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
    out.mkdir(parents=True, exist_ok=False)
    records = []

    def identity():
        production = [tree / 'Cargo.toml', tree / 'Cargo.lock', *sorted((tree / 'src').rglob('*.rs')),
                      *sorted((tree / 'stdlib').rglob('*.qli')), *sorted((tree / 'stdlib').rglob('Qargo.toml'))]
        fixture = [here / 'initial-study/observer.rs']
        for folder in ('initial-study', 'additional-study', 'sources'):
            fixture.extend(sorted((here / folder).rglob('*.qli')))
            fixture.extend(sorted((here / folder).rglob('Qargo.toml')))
        return dict(production={str(p.relative_to(tree)): hashlib.sha256(p.read_bytes()).hexdigest() for p in production},
                    fixture_inputs={str(p.relative_to(here)): hashlib.sha256(p.read_bytes()).hexdigest() for p in fixture},
                    kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest())

    original_identity = identity()
    (out / 'source-identity.json').write_text(json.dumps(original_identity, indent=2) + '\n')

    def run(label, argv):
        result = subprocess.run(argv, cwd=tree, env=dict(os.environ, QLEISLI_KERNEL=str(kernel)), capture_output=True, timeout=120)
        (out / (label + '.stdout')).write_bytes(result.stdout)
        (out / (label + '.stderr')).write_bytes(result.stderr)
        records.append(dict(label=label, argv=argv, cwd=str(tree), QLEISLI_KERNEL=str(kernel), exit_code=result.returncode,
                            stdout=label + '.stdout', stderr=label + '.stderr'))
        (out / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
        if result.returncode:
            raise RuntimeError(f'{label}: exit {result.returncode}; see recorded streams')

    run('build', ['cargo', 'build', '--offline', '--lib', '--bin', 'qleisli'])
    observer = out / 'observer'
    run('observer-build', ['rustc', '--edition=2024', str(here / 'initial-study/observer.rs'), '--extern',
                          'qleisli=' + str(tree / 'target/debug/libqleisli.rlib'), '-L',
                          'dependency=' + str(tree / 'target/debug/deps'), '-o', str(observer)])
    for directory in sorted((here / 'initial-study').iterdir()):
        if directory.is_dir() and (directory / 'Qargo.toml').exists():
            run(directory.name, [str(observer), str(directory), 'check'])
    for directory in sorted((here / 'additional-study').iterdir()):
        if directory.is_dir() and (directory / 'Qargo.toml').exists():
            run('additional-' + directory.name, [str(observer), str(directory), 'check'])
    cli = tree / 'target/debug/qleisli'
    proposals = []
    for label in ('finite-rebind', 'finite-branch'):
        directory = here / 'sources' / label
        output = out / (label + '.proposal.json')
        run(label + '-proposal', [str(cli), 'emit-ir', str(directory), '--output=' + str(output)])
        run(label + '-check', [str(cli), 'check', str(directory), '--format=json'])
        run(label + '-run', [str(cli), 'run', str(directory), '--format=json'])
        proposals.append(dict(label=label, file=output.name, sha256=hashlib.sha256(output.read_bytes()).hexdigest()))
    for label, case, bindings in (
        ('sized-fold', 'sized-fold', []),
        ('sized-recursive', 'sized-recursive', ['--nat=n=2']),
        ('provider-h', 'providers', ['--operation=U=a::gate']),
        ('provider-x', 'providers', ['--operation=U=b::gate']),
    ):
        directory = here / 'sources' / case
        modules = ['--module=' + p.stem + '=' + str(p) for p in sorted(directory.glob('*.qli'))]
        common = ['--entry=main::f', *modules, *bindings]
        output = out / (label + '.proposal.json')
        run(label + '-proposal', [str(cli), 'sized', 'emit-proposal', *common, '--output=' + str(output)])
        run(label + '-check', [str(cli), 'sized', 'check', *common, '--kernel=' + str(kernel)])
        run(label + '-run', [str(cli), 'sized', 'run', *common, '--kernel=' + str(kernel), '--basis=0'])
        proposals.append(dict(label=label, file=output.name, sha256=hashlib.sha256(output.read_bytes()).hexdigest()))
    (out / 'proposals.json').write_text(json.dumps(proposals, indent=2) + '\n')
    (out / 'executables.json').write_text(json.dumps({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in (cli, kernel, observer)}, indent=2) + '\n')
    if identity() != original_identity:
        raise RuntimeError('Production source, fixture inputs or native checker changed during replay')
    print('Saved ten original and two additional profile observations, six proposals, six native checks and six one-qubit runs.')


if __name__ == '__main__':
    main()
