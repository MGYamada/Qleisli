#!/usr/bin/env python3
"""Build a literal Cargo selection once, then run its complete harnesses in a bounded pool.

The caller still owns source/toolchain binding, the aggregate deadline and the
native skip gate. This scheduler never caches an acceptance decision.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

import check_rust_test_partition as partition
import ci_runtime
import run_kernel_tests

ROOT = Path(__file__).resolve().parents[1]


def selection(command, metadata):
    """Keep the pinned Cargo, positive selectors and complete target conventions."""
    entries = (partition.LATEST, partition.MSRV)
    entry = next((entry for entry in entries if command[:len(entry) + 1] == entry + ['test']), None)
    if entry is None:
        raise ValueError('expected the pinned latest or MSRV Cargo test command')
    arguments = command[len(entry) + 1:]
    inventory = partition.inventory(metadata, ROOT)
    known = {row['name'] for row in inventory if row['kind'] == 'test'}
    categories = arguments == ['--all-targets'] or arguments[:len(partition.CATEGORIES)] == partition.CATEGORIES
    tests = sorted(known) if arguments == ['--all-targets'] else partition.names(
        arguments[len(partition.CATEGORIES):] if categories else arguments)
    if not set(tests) <= known:
        raise ValueError('selected integration target is absent from Cargo metadata')
    expected = {(row['kind'], row['name']) for row in inventory
                if (row['kind'] == 'test' and row['name'] in tests)
                or (categories and row['kind'] in {'lib', 'bin', 'example'})}
    return entry, expected


def artifacts(messages, metadata, expected):
    """Execute only exact root-package test artifacts from this successful build."""
    found = {}
    package = metadata['packages'][0]
    targets = {(tuple(t['kind']), t['name']): t for t in package['targets']}
    for message in messages:
        if (message.get('reason') != 'compiler-artifact'
                or message.get('package_id') != package['id']
                or message.get('profile', {}).get('test') is not True
                or not message.get('executable')):
            continue
        target = message['target']
        key = target['kind'][0], target['name']
        if (key not in expected or key in found
                or targets.get((tuple(target['kind']), target['name'])) != target):
            raise ValueError('unexpected, duplicate or changed root test artifact')
        executable = Path(message['executable']).resolve()
        if (not executable.is_relative_to(Path(metadata['target_directory']).resolve())
                or not executable.is_file() or not os.access(executable, os.X_OK)):
            raise ValueError('test executable is absent or outside the selected target directory')
        found[key] = dict(kind=key[0], name=key[1], executable=str(executable),
                          package_id=package['id'], target=target, profile=message['profile'],
                          sha256=digest(executable), status='not-run')
    if set(found) != expected:
        raise ValueError('built harness inventory differs from the complete literal selection')
    return [found[key] for key in sorted(found)]


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def harness(row, directory):
    """Let Cargo retain its runtime environment and default harness arguments."""
    started = time.monotonic()
    log = directory / (row['kind'] + '-' + row['name'] + '.log')
    result = row | dict(status='failed', log=str(log), executed_command=row['command'] + ['--message-format=json'])
    try:
        if digest(row['executable']) != row['sha256']:
            raise ValueError('test executable changed before execution')
        with tempfile.TemporaryDirectory(prefix='rust-test-') as scratch, log.open('w') as output:
            environment = os.environ | dict(TMPDIR=scratch, TMP=scratch, TEMP=scratch)
            # Inherit the outer command's process group: its timeout must kill
            # this harness and every native/CLI descendant, including workers.
            observed = subprocess.run(result['executed_command'], cwd=ROOT, env=environment,
                                      stdout=output, stderr=subprocess.STDOUT)
        result['exit_code'] = observed.returncode
        lines = log.read_text(errors='replace').splitlines()
        summaries = [run_kernel_tests.SUMMARY.match(line) for line in lines]
        summaries = [match for match in summaries if match]
        built = [json.loads(line) for line in lines if line.startswith('{')]
        built = [item for item in built if item.get('reason') == 'compiler-artifact'
                 and item.get('package_id') == row['package_id'] and item.get('profile', {}).get('test')]
        if (len(built) != 1 or built[0]['target'] != row['target'] or built[0]['profile'] != row['profile']
                or Path(built[0]['executable']).resolve() != Path(row['executable']).resolve()):
            raise ValueError('Cargo selected a different harness than the bound build artifact')
        skipped = any(run_kernel_tests.SKIP_REASON in line and 'ignored' in line for line in lines)
        if (observed.returncode or len(summaries) != 1 or skipped
                or digest(row['executable']) != row['sha256']):
            raise ValueError('harness failed, skipped native tests, lacked one summary or changed executable')
        result.update(status='passed', passed=int(summaries[0][1]), exit_code=0)
    except (OSError, ValueError) as error:
        result['error'] = str(error)
    return result | dict(seconds=time.monotonic() - started)


def schedule(rows, workers, directory, update):
    """Stop submitting after failure; retain already running and unstarted targets."""
    results = [row.copy() for row in rows]
    pending = iter(enumerate(rows))
    failed = False
    with ThreadPoolExecutor(max_workers=workers) as pool:
        running = {}
        def submit():
            item = next(pending, None)
            if item is not None:
                index, row = item
                results[index] = row | dict(status='running')
                update(results)
                print(f"Rust harness start: {row['kind']} {row['name']}", flush=True)
                running[pool.submit(harness, row, directory)] = index
        for _ in range(workers):
            submit()
        while running:
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                index = running.pop(future)
                results[index] = future.result()
                result = results[index]
                failed |= result['status'] != 'passed'
                print(f"Rust harness {result['status']}: {result['kind']} {result['name']} "
                      f"({result['seconds']:.2f}s)", flush=True)
                log = Path(result['log'])
                if log.exists():
                    print(log.read_text(errors='replace'), end='', flush=True)
            update(results)
            if not failed:
                for _ in done:
                    submit()
    return results


def execute(command, workers, record):
    record.parent.mkdir(parents=True, exist_ok=True)
    directory = record.parent / 'rust-harnesses'
    directory.mkdir()
    started = time.monotonic()
    report = dict(format=1, status='failed', command=command, workers=workers, harnesses=[],
                  scope='Complete selected harness execution; no semantic acceptance cache.')
    def retain(rows=None):
        if rows is not None:
            report['harnesses'] = rows
        report['seconds'] = time.monotonic() - started
        temporary = record.with_suffix('.pending')
        temporary.write_text(json.dumps(report, indent=2) + '\n')
        temporary.replace(record)
    retain()
    try:
        kernel = Path(os.environ.get('QLEISLI_KERNEL', ''))
        if not kernel.is_file() or not os.access(kernel, os.X_OK):
            raise ValueError('select an executable QLEISLI_KERNEL before building tests')
        partition.manifest_conventions(ROOT, (ROOT / 'Cargo.toml').read_bytes())
        entry = next((entry for entry in (partition.LATEST, partition.MSRV)
                      if command[:len(entry) + 1] == entry + ['test']), None)
        if entry is None:
            raise ValueError('expected pinned Cargo test')
        probe = ci_runtime.launch_command(entry + ['metadata', '--no-deps', '--locked', '--offline',
                                                   '--format-version', '1'])
        observed = subprocess.run(probe, cwd=ROOT, capture_output=True, check=True)
        (directory / 'metadata.json').write_bytes(observed.stdout)
        metadata = json.loads(observed.stdout)
        _, expected = selection(command, metadata)
        report['metadata_sha256'] = hashlib.sha256(observed.stdout).hexdigest()
        report['expected'] = sorted(expected)
        build = ci_runtime.launch_command(command + ['--locked', '--no-run', '--message-format=json'])
        report['build_command'] = build
        retain()
        with (directory / 'build.jsonl').open('w') as output, (directory / 'build.stderr').open('w') as error:
            observed = subprocess.run(build, cwd=ROOT, stdout=output, stderr=error)
        report['build_exit_code'] = observed.returncode
        messages = [json.loads(line) for line in (directory / 'build.jsonl').read_text().splitlines()]
        if observed.returncode or not messages or messages[-1] != dict(reason='build-finished', success=True):
            raise ValueError('Cargo did not finish a successful complete build')
        rows = artifacts(messages, metadata, expected)
        # Cargo releases its compilation lock before running a harness. The
        # complete build above prevents competing builds, while Cargo itself
        # supplies platform-specific library paths and test runtime variables.
        for row in rows:
            flag = '--lib' if row['kind'] == 'lib' else '--' + row['kind']
            selector = [flag] if row['kind'] == 'lib' else [flag, row['name']]
            row['command'] = ci_runtime.launch_command(entry + ['test', '--locked', *selector])
        retain(rows)
        results = schedule(rows, workers, directory, retain)
        if not results or any(row['status'] != 'passed' for row in results):
            raise ValueError('selected harnesses failed or remain unexecuted')
        if not sum(row['passed'] for row in results):
            raise ValueError('no tests passed')
        report['status'] = 'passed'
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        report['error'] = str(error)
        print('Rust harness scheduling refused: ' + str(error), file=sys.stderr)
    retain()
    return 0 if report['status'] == 'passed' else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, choices=[1, 2, 4], required=True)
    parser.add_argument('--record', type=Path, required=True)
    parser.add_argument('--target-dir', type=Path, help='Use the caller-owned target directory (no cache is created).')
    parser.add_argument('--offline', action='store_true', help='Keep all Cargo invocations offline.')
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.target_dir is not None:
        os.environ['CARGO_TARGET_DIR'] = str(args.target_dir.resolve())
    if args.offline:
        os.environ['CARGO_NET_OFFLINE'] = 'true'
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    return execute(command, args.workers, args.record)


if __name__ == '__main__':
    raise SystemExit(main())
