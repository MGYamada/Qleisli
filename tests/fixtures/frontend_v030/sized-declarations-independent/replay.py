#!/usr/bin/env python3
"""Record bounded declaration observations and independent Rust/native tests.

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
    parser.add_argument('--tree', type=Path, required=True)
    parser.add_argument('--kernel', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--msrv-bin', type=Path, required=True)
    args = parser.parse_args()
    tree, kernel, out = args.tree.resolve(), args.kernel.resolve(), args.output_dir.resolve()
    here = Path(__file__).resolve().parent
    observer_source = here.parent / 'lexical-resolution/initial-study/observer.rs'
    out.mkdir(parents=True, exist_ok=False)

    def identity():
        files = [tree / 'Cargo.toml', tree / 'Cargo.lock', tree / 'tests/sized_declarations.rs',
                 *sorted((tree / 'src').rglob('*.rs')), *sorted((tree / 'stdlib').rglob('*.qli')),
                 *sorted((tree / 'stdlib').rglob('Qargo.toml'))]
        fixtures = [observer_source, *sorted((here / 'sources').rglob('*.qli')),
                    *sorted((here / 'sources').rglob('Qargo.toml'))]
        return dict(production={str(p.relative_to(tree)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
                    inputs={str(p.relative_to(here.parent)): hashlib.sha256(p.read_bytes()).hexdigest() for p in fixtures},
                    kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest())

    original = identity()
    (out / 'source-identity.json').write_text(json.dumps(original, indent=2) + '\n')
    records = []
    env = dict(os.environ, QLEISLI_KERNEL=str(kernel))

    def run(label, argv, environment=env):
        result = subprocess.run(argv, cwd=tree, env=environment, capture_output=True, timeout=180)
        (out / (label + '.stdout')).write_bytes(result.stdout)
        (out / (label + '.stderr')).write_bytes(result.stderr)
        records.append(dict(label=label, argv=argv, cwd=str(tree), QLEISLI_KERNEL=str(kernel),
                            PATH=environment['PATH'], executable=shutil.which(argv[0], path=environment['PATH']),
                            exit_code=result.returncode, stdout=label + '.stdout', stderr=label + '.stderr'))
        (out / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
        if result.returncode:
            raise RuntimeError(f'{label}: exit {result.returncode}; see saved streams')
        return result

    for tool in ('rustc', 'cargo', 'cargo-clippy'):
        run('latest-' + tool, [tool, '--version'])
    run('build', ['cargo', 'build', '--offline', '--lib'])
    observer = out / 'observer'
    run('observer-build', ['rustc', '--edition=2024', str(observer_source), '--extern',
                          'qleisli=' + str(tree / 'target/debug/libqleisli.rlib'), '-L',
                          'dependency=' + str(tree / 'target/debug/deps'), '-o', str(observer)])
    observations = []
    for directory in sorted((here / 'sources').iterdir()):
        result = run(directory.name, [str(observer), str(directory), 'check'])
        observations.append(dict(case=directory.name, stdout=result.stdout.decode(), stderr=result.stderr.decode(),
                                 exit_code=result.returncode))
    (out / 'observations.json').write_text(json.dumps(observations, indent=2) + '\n')
    (out / 'observer-identity.json').write_text(json.dumps({
        'source': str(observer_source), 'source_sha256': hashlib.sha256(observer_source.read_bytes()).hexdigest(),
        'executable_sha256': hashlib.sha256(observer.read_bytes()).hexdigest()}, indent=2) + '\n')
    run('latest-tests', ['cargo', 'test', '--offline', '--test', 'sized_declarations'])
    run('latest-clippy', ['cargo', 'clippy', '--offline', '--all-targets', '--', '-D', 'warnings'])
    msrv_env = dict(env, PATH=str(args.msrv_bin.resolve()) + os.pathsep + env['PATH'])
    for tool in ('rustc', 'cargo', 'cargo-clippy'):
        run('msrv-' + tool, [tool, '--version'], msrv_env)
    run('msrv-tests', ['cargo', 'test', '--offline', '--test', 'sized_declarations'], msrv_env)
    run('msrv-clippy', ['cargo', 'clippy', '--offline', '--all-targets', '--', '-D', 'warnings'], msrv_env)
    run('fmt', ['cargo', 'fmt', '--all', '--check'])
    if original != identity():
        raise RuntimeError('Source, test input or native checker changed during replay')
    print('Saved 18 source observations, 7 tests on each toolchain, and both all-target Clippy checks.')


if __name__ == '__main__':
    main()
