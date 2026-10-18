#!/usr/bin/env python3
"""Check complete, disjoint Cargo target selection before native-gated tests.

This checks scheduling coverage, not source semantics or native acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

import ci_runtime
import ci_source_checks

ROOT = Path(__file__).resolve().parents[1]
HEAVY = ['frontend_ownership_differential', 'source_ir_correspondence']
CATEGORIES = ['--lib', '--bins', '--examples', '--benches']
EXAMPLES = ['interop', 'lean_kernel', 'native_acceptance', 'sampled_shor15', 'shor15']
WRAPPER = ['python3', 'scripts/run_kernel_tests.py', '--']
SCHEDULER = ['python3', 'scripts/run_rust_tests.py', '--workers', '2', '--record', '{record}', '--']
LATEST = ['cargo', '+1.98.1']
MSRV = ['python3', 'scripts/run_msrv.py']
NAME = re.compile(r'[a-zA-Z_][a-zA-Z_0-9-]*\Z')


def cargo(group):
    """Return the same pinned Cargo entry point used by the test commands."""
    if group == 'rust-latest':
        return LATEST
    if group == 'rust-msrv':
        return MSRV
    raise ValueError('unsupported Rust partition group')


def names(arguments):
    """Require explicit positive integration targets, with no test-name filter."""
    if not arguments or len(arguments) % 2:
        raise ValueError('missing explicit integration targets')
    selected = []
    for flag, name in zip(arguments[::2], arguments[1::2]):
        if flag != '--test' or not isinstance(name, str) or not NAME.fullmatch(name):
            raise ValueError('unsupported integration target selection')
        selected.append(name)
    if selected != sorted(set(selected)):
        raise ValueError('duplicate or unordered integration target selection')
    return selected


def selection(group, commands):
    """Bind both literal commands, native wrappers and all surrounding checks."""
    entry = cargo(group)
    prefix = [entry + ['fmt', '--check']] if group == 'rust-latest' else []
    guard = ['python3', 'scripts/check_rust_test_partition.py', '--group', group]
    suffix = [
        WRAPPER + entry + ['test', '--test', 'sized_review_dialects', '--', '--ignored', '--skip', 'native'],
        ['python3', 'scripts/test_sized_primitive_catalog.py'],
        entry + ['doc', '--no-deps'],
        WRAPPER + entry + ['test', '--doc'],
    ] if group == 'rust-latest' else []
    offset = len(prefix) + 1
    if (len(commands) != len(prefix) + 4 + len(suffix)
            or commands[:offset] != prefix + [guard]
            or commands[offset + 1] != guard
            or commands[offset + 3:] != suffix):
        raise ValueError('changed partition guard order or surrounding Rust checks')
    first, second = commands[offset], commands[offset + 2]
    head = WRAPPER + SCHEDULER + entry + ['test']
    if first[:len(head)] != head or second[:len(head) + len(CATEGORIES)] != head + CATEGORIES:
        raise ValueError('changed native wrapper, Cargo entry point or target categories')
    heavy = names(first[len(head):])
    rest = names(second[len(head) + len(CATEGORIES):])
    if heavy != HEAVY or set(heavy) & set(rest):
        raise ValueError('changed heavy targets or overlapping integration partitions')
    return heavy, rest


def inventory(metadata, root):
    """Reject unreviewed target conventions or feature/workspace selection."""
    if metadata.get('version') != 1 or metadata.get('workspace_root') != str(root):
        raise ValueError('metadata format or workspace root differs')
    packages = metadata.get('packages')
    if not isinstance(packages, list) or len(packages) != 1:
        raise ValueError('expected only the root package in no-deps metadata')
    package = packages[0]
    package_id = package.get('id')
    if (not isinstance(package_id, str) or not package_id
            or package.get('name') != 'qleisli'
            or package.get('manifest_path') != str(root / 'Cargo.toml')
            or package.get('edition') != '2024'
            or package.get('features') != {}
            or metadata.get('workspace_members') != [package_id]
            or metadata.get('workspace_default_members') != [package_id]):
        raise ValueError('changed package, features or workspace selection')
    targets = package.get('targets')
    if not isinstance(targets, list) or not targets:
        raise ValueError('missing Cargo targets')
    rows, seen = [], set()
    for target in targets:
        kinds, name = target.get('kind'), target.get('name')
        if (not isinstance(kinds, list) or len(kinds) != 1
                or kinds[0] not in {'lib', 'bin', 'test', 'example', 'custom-build'}
                or not isinstance(name, str) or not NAME.fullmatch(name)):
            raise ValueError('unknown target kind or name; target conventions need review')
        kind = kinds[0]
        key = kind, name
        if key in seen:
            raise ValueError('duplicate Cargo target')
        seen.add(key)
        if kind == 'custom-build':
            if name != 'build-script-build':
                raise ValueError('changed automatic Cargo build script')
            path = 'build.rs'
        elif kind in {'lib', 'bin'}:
            if name != 'qleisli':
                raise ValueError('changed library or binary target')
            path = 'src/lib.rs' if kind == 'lib' else 'src/bin/qleisli.rs'
        else:
            path = ('tests/' if kind == 'test' else 'examples/') + name + '.rs'
        flags = dict(test=kind in {'lib', 'bin', 'test'}, doctest=kind == 'lib', doc=kind in {'lib', 'bin'})
        if (target.get('src_path') != str(root / path)
                or target.get('crate_types') != (['lib'] if kind == 'lib' else ['bin'])
                or target.get('edition') != '2024'
                or target.get('required-features', []) != []
                or any(type(target.get(flag)) is not bool or target[flag] != value
                       for flag, value in flags.items())):
            raise ValueError('changed target path, crate type, features or eligibility')
        rows.append(dict(kind=kind, name=name, source=path, crate_types=target['crate_types'],
                         edition=target['edition'], required_features=[], **flags))
    expected_non_tests = {('lib', 'qleisli'), ('bin', 'qleisli'), ('custom-build', 'build-script-build'),
                          *(('example', name) for name in EXAMPLES)}
    if {key for key in seen if key[0] != 'test'} != expected_non_tests:
        raise ValueError('changed non-integration target inventory')
    return sorted(rows, key=lambda row: (row['kind'], row['name']))


def validate(group, commands, metadata, root):
    """Compare explicit positive partitions with the complete Cargo inventory."""
    heavy, rest = selection(group, commands)
    rows = inventory(metadata, root)
    actual = {row['name'] for row in rows if row['kind'] == 'test'}
    if set(heavy + rest) != actual:
        raise ValueError('integration partition differs from complete Cargo target inventory')
    return dict(inventory=rows, heavy=heavy, remaining=rest)


def manifest_conventions(root, contents):
    """Metadata omits harness flags: refuse unreviewed manifest target overrides."""
    manifest = tomllib.loads(contents.decode())
    if (set(manifest) != {'package', 'lib', 'dependencies', 'target', 'lints'}
            or manifest['lib'] != {'name': 'qleisli', 'path': 'src/lib.rs'}
            or any(key in manifest['package'] for key in
                   ('autolib', 'autobins', 'autotests', 'autoexamples', 'autobenches', 'build', 'default-run'))):
        raise ValueError('changed Cargo target conventions; explicit review required')
    if any((root / '.cargo' / name).exists() for name in ('config', 'config.toml')):
        raise ValueError('Cargo project configuration requires target-selection review')


def main():
    """Record the actual metadata bytes and selected literal commands before tests."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--group', choices=['rust-latest', 'rust-msrv'], required=True)
    args = parser.parse_args()
    try:
        spec = ci_source_checks.definition(args.group)
        if spec['timeout_seconds'] != 3600 or spec['prepare'] != ['native-runtime']:
            raise ValueError('changed per-command timeout or native preparation')
        selection(args.group, spec['commands'])
        cargo_manifest = (ROOT / 'Cargo.toml').read_bytes()
        manifest_conventions(ROOT, cargo_manifest)
        command = cargo(args.group) + ['metadata', '--no-deps', '--locked', '--offline', '--format-version', '1']
        environment = ci_runtime.execution_environment()
        environment.update({key: value.replace('{root}', str(ROOT)) for key, value in spec['environment'].items()})
        observed = subprocess.run(ci_runtime.launch_command(command), cwd=ROOT, env=environment,
                                  check=True, capture_output=True, timeout=60)
        metadata = json.loads(observed.stdout)
        # Preserve the first actual metadata even when coverage validation fails.
        print(json.dumps(dict(command=command, metadata=metadata,
                              metadata_sha256=hashlib.sha256(observed.stdout).hexdigest()), indent=2), flush=True)
        report = validate(args.group, spec['commands'], metadata, ROOT)
        report.update(group=args.group, command=command, metadata_sha256=hashlib.sha256(observed.stdout).hexdigest(),
                      package_id=metadata['packages'][0]['id'], commands=spec['commands'],
                      cargo_manifest_sha256=hashlib.sha256(cargo_manifest).hexdigest(),
                      manifest_sha256=ci_source_checks.digest(ci_source_checks.MANIFEST),
                      status='complete-disjoint-target-selection',
                      scope='Scheduling coverage only; native-gated execution still required.')
        print(json.dumps(report, indent=2))
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print('Rust target partition refused: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
