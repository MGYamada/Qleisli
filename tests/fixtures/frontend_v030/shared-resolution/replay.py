#!/usr/bin/env python3
"""Replay bounded resolver observations with fixed commands, not recorded input.

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
    out.mkdir(parents=True, exist_ok=True)
    records = []

    def run(label, argv):
        result = subprocess.run(argv, cwd=tree, env=dict(os.environ, QLEISLI_KERNEL=str(kernel)), capture_output=True, timeout=120)
        (out / (label + '.stdout')).write_bytes(result.stdout)
        (out / (label + '.stderr')).write_bytes(result.stderr)
        records.append(dict(label=label, argv=argv, cwd=str(tree), QLEISLI_KERNEL=str(kernel), exit_code=result.returncode, stdout=label + '.stdout', stderr=label + '.stderr'))
        (out / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
        return result.returncode

    assert run('build', ['cargo', 'build', '--offline', '--lib', '--bin', 'qleisli']) == 0
    observer = out / 'observer'
    assert run('observer-build', ['rustc', '--edition=2024', str(here / 'initial-study/observer.rs'), '--extern', 'qleisli=' + str(tree / 'target/debug/libqleisli.rlib'), '-L', 'dependency=' + str(tree / 'target/debug/deps'), '-o', str(observer)]) == 0
    for directory in sorted((here / 'initial-study').iterdir()):
        if directory.is_dir() and (directory / 'Qargo.toml').exists():
            argv = [str(observer), str(directory)]
            if directory.name in ('same-module-two-declarations', 'moved-local-shadows-import', 'declaration-call-cycle'):
                argv.append('check')
            assert run(directory.name, argv) == 0
    cli = tree / 'target/debug/qleisli'
    proposals = []
    for label, case, bindings in [
        ('provider-h', 'providers', ['--operation=U=a::gate']),
        ('provider-x', 'providers', ['--operation=U=b::gate']),
        ('cross-module', 'cross-module', []),
        ('recursive-zero', 'recursive', ['--nat=n=0']),
        ('recursive-two', 'recursive', ['--nat=n=2']),
    ]:
        directory = here / 'sources' / case
        modules = ['--module=' + p.stem + '=' + str(p) for p in sorted(directory.glob('*.qli'))]
        common = ['--entry=main::f', *modules, *bindings]
        output = out / (label + '.proposal.json')
        assert run(label + '-proposal', [str(cli), 'sized', 'emit-proposal', *common, '--output=' + str(output)]) == 0
        proposals.append(dict(label=label, output=output.name, sha256=hashlib.sha256(output.read_bytes()).hexdigest()))
        assert run(label + '-native-check', [str(cli), 'sized', 'check', *common, '--kernel=' + str(kernel)]) == 0
        assert run(label + '-native-run', [str(cli), 'sized', 'run', *common, '--kernel=' + str(kernel), '--basis=0']) == 0
    (out / 'proposals.json').write_text(json.dumps(proposals, indent=2) + '\n')
    print('Saved 10 profile observations, 5 proposals, 5 native checks and 5 one-qubit executions.')


if __name__ == '__main__':
    main()
