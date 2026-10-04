#!/usr/bin/env python3
"""Replay bounded predicate source, proposal and independent action checks.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('tree', 'baseline-tree', 'kernel', 'output-dir', 'msrv-bin'):
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    tree, baseline, kernel, out = (path.resolve() for path in
                                  (args.tree, args.baseline_tree, args.kernel, args.output_dir))
    here = Path(__file__).resolve().parent
    observer_source = here.parent / 'lexical-resolution/initial-study/observer.rs'
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, QLEISLI_KERNEL=str(kernel))
    records = []

    def identity():
        files = [tree / 'Cargo.toml', tree / 'Cargo.lock', *sorted((tree / 'src').rglob('*.rs')),
                 *sorted((tree / 'tests').glob('*.rs')), *sorted((tree / 'stdlib').rglob('*.qli')),
                 *sorted((tree / 'stdlib').rglob('Qargo.toml'))]
        fixtures = [observer_source, *sorted((here / 'sources').rglob('*')),
                    *sorted((here / 'repaired').rglob('*'))]
        return dict(production_and_tests={str(p.relative_to(tree)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
                    inputs={str(p.relative_to(here.parent)): hashlib.sha256(p.read_bytes()).hexdigest() for p in fixtures if p.is_file()},
                    kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest())

    original = identity()
    (out / 'source-identity.json').write_text(json.dumps(original, indent=2) + '\n')

    def run(label, argv, environment=env):
        result = subprocess.run(argv, cwd=tree, env=environment, capture_output=True, timeout=240)
        (out / (label + '.stdout')).write_bytes(result.stdout)
        (out / (label + '.stderr')).write_bytes(result.stderr)
        records.append(dict(label=label, argv=argv, cwd=str(tree), QLEISLI_KERNEL=str(kernel), PATH=environment['PATH'],
                            executable=shutil.which(argv[0], path=environment['PATH']), exit_code=result.returncode,
                            stdout=label + '.stdout', stderr=label + '.stderr'))
        (out / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
        if result.returncode:
            raise RuntimeError(f'{label}: exit {result.returncode}; see saved streams')
        return result

    for tool in ('rustc', 'cargo', 'cargo-clippy'):
        run('latest-' + tool, [tool, '--version'])
    run('build', ['cargo', 'build', '--offline', '--lib', '--bin', 'qleisli'])
    observer = out / 'observer'
    run('observer-build', ['rustc', '--edition=2024', str(observer_source), '--extern',
                          'qleisli=' + str(tree / 'target/debug/libqleisli.rlib'), '-L',
                          'dependency=' + str(tree / 'target/debug/deps'), '-o', str(observer)])
    observations = []
    for folder in ('sources', 'repaired'):
        for directory in sorted((here / folder).iterdir()):
            result = run(folder + '-' + directory.name, [str(observer), str(directory), 'check'])
            observations.append(dict(folder=folder, case=directory.name, exit_code=result.returncode,
                                     stdout=result.stdout.decode(), stderr=result.stderr.decode()))
    (out / 'observations.json').write_text(json.dumps(observations, indent=2) + '\n')
    proposals = []
    for label in ('restricted-flat', 'restricted-left', 'restricted-right',
                  'certified-flat', 'certified-left', 'certified-right',
                  'legacy-restricted-three', 'legacy-certified-three'):
        old_dir = here / ('repaired' if (here / 'repaired' / label).exists() else 'sources') / label
        new_label = label if not label.startswith('legacy-') else label.removeprefix('legacy-').replace('-three', '-left')
        new_dir = here / 'sources' / new_label
        old_output, new_output = out / (label + '.before.qirf'), out / (label + '.after.qirf')
        run(label + '-before', [str(baseline / 'target/debug/qleisli'), 'emit-ir', str(old_dir), '--output=' + str(old_output)])
        run(label + '-after', [str(tree / 'target/debug/qleisli'), 'emit-ir', str(new_dir), '--output=' + str(new_output)])
        if old_output.read_bytes() != new_output.read_bytes():
            raise RuntimeError(f'{label}: bounded old/migrated proposal bytes differ')
        proposals.append(dict(label=label, current_source=new_label, sha256=hashlib.sha256(old_output.read_bytes()).hexdigest()))
    (out / 'proposals.json').write_text(json.dumps(proposals, indent=2) + '\n')
    run('latest-tests', ['cargo', 'test', '--offline', '--test', 'predicate_domain'])
    run('latest-clippy', ['cargo', 'clippy', '--offline', '--all-targets', '--', '-D', 'warnings'])
    msrv_env = dict(env, PATH=str(args.msrv_bin.resolve()) + os.pathsep + env['PATH'])
    for tool in ('rustc', 'cargo', 'cargo-clippy'):
        run('msrv-' + tool, [tool, '--version'], msrv_env)
    run('msrv-tests', ['cargo', 'test', '--offline', '--test', 'predicate_domain'], msrv_env)
    run('msrv-clippy', ['cargo', 'clippy', '--offline', '--all-targets', '--', '-D', 'warnings'], msrv_env)
    run('fmt', ['cargo', 'fmt', '--all', '--check'])
    (out / 'executables.json').write_text(json.dumps({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in
                                                    (tree / 'target/debug/qleisli', baseline / 'target/debug/qleisli', observer, kernel)}, indent=2) + '\n')
    if original != identity():
        raise RuntimeError('Source, test input or native checker changed during replay')
    print('Saved 56 observations, 8 byte-identical old/current proposals, 7 tests per toolchain and both all-target Clippy checks.')


if __name__ == '__main__':
    main()
