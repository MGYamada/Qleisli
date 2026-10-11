#!/usr/bin/env python3
"""Replay the ten preserved studies without changing their original records.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kernel', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    root = here.parents[3]
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    kernel = args.kernel.resolve()
    env = dict(os.environ, QLEISLI_KERNEL=str(kernel))
    observer_source = here.parent / 'lexical-resolution/initial-study/observer.rs'

    def inputs():
        paths = [root / 'Cargo.toml', root / 'Cargo.lock',
                 root / 'tests/sized_source.rs', root / 'tests/shared_resolution.rs',
                 root / 'lean/schema-registry.json', observer_source,
                 *sorted((root / 'src').rglob('*.rs')),
                 *sorted((root / 'stdlib').rglob('*.qli')),
                 *sorted((root / 'stdlib').rglob('Qargo.toml')),
                 *sorted((here / 'initial-study').rglob('*.qli')),
                 *sorted((here / 'initial-study').rglob('Qargo.toml'))]
        return {str(p.relative_to(root)): sha(p) for p in paths}

    initial = inputs()
    kernel_hash = sha(kernel)
    records = []

    def run(label, argv):
        start = time.monotonic()
        result = subprocess.run(argv, cwd=root, env=env, capture_output=True, timeout=180)
        elapsed = time.monotonic() - start
        stdout, stderr = label + '.stdout.txt', label + '.stderr.txt'
        (out / stdout).write_bytes(result.stdout)
        (out / stderr).write_bytes(result.stderr)
        records.append(dict(label=label, argv=argv, cwd=str(root),
                            QLEISLI_KERNEL=str(kernel), exit_code=result.returncode,
                            seconds=elapsed, stdout=stdout, stderr=stderr))
        (out / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
        if result.returncode:
            raise RuntimeError(f'{label}: exit {result.returncode}; see saved streams')
        return result

    run('build', ['cargo', 'build', '--offline', '--lib'])
    observer = out / 'observer'
    run('observer-build', ['rustc', '--edition=2024', str(observer_source), '--extern',
                          'qleisli=' + str(root / 'target/debug/libqleisli.rlib'),
                          '-L', 'dependency=' + str(root / 'target/debug/deps'),
                          '-o', str(observer)])
    observations = []
    for directory in sorted((here / 'initial-study').iterdir()):
        if directory.is_dir() and (directory / 'Qargo.toml').exists():
            result = run(directory.name, [str(observer), str(directory), 'check'])
            observations.append(dict(case=directory.name, stdout=result.stdout.decode(),
                                     stderr=result.stderr.decode(), exit_code=result.returncode))
    (out / 'observations.json').write_text(json.dumps(observations, indent=2) + '\n')
    run('focused-tests', ['cargo', 'test', '--offline', '--test', 'sized_source',
                          '--test', 'shared_resolution'])
    unchanged = inputs() == initial and sha(kernel) == kernel_hash
    files = {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file() and p != observer}
    record = dict(format='qleisli.multi-declaration-replay', version=1,
                  git_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root,
                                                   text=True).strip(),
                  working_tree='uncommitted multi-declaration integration; see exact input hashes',
                  inputs=initial, inputs_and_kernel_unchanged=unchanged,
                  toolchain={name: subprocess.check_output([name, '--version'], env=env,
                                                          text=True).strip()
                             for name in ('cargo', 'rustc')},
                  executables={str(kernel): kernel_hash, str(observer): sha(observer)},
                  files=files,
                  scope='Ten actual observer processes and focused Rust tests. Process exit zero '
                        'does not mean source checking succeeded: read the saved diagnostics. '
                        'The native artifact/phase oracle is separate independent evidence.')
    (out / 'validation.json').write_text(json.dumps(record, indent=2) + '\n')
    if not unchanged:
        raise RuntimeError('Inputs or kernel changed during replay')
    print('Saved ten observer results and focused tests with unchanged source/kernel identities.')


if __name__ == '__main__':
    main()
