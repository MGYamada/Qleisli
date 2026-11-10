"""Run and validate complete Rust partitions from the candidate's Git archive.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import hashlib
from pathlib import Path
import subprocess
import tempfile

import check_distribution as distribution
import check_rust_test_partition as partition
import ci_runtime
import run_rust_tests
from check_ratification_packet import json_object


def scheduled(command):
    prefix = partition.WRAPPER + partition.SCHEDULER
    return command[:len(prefix)] == prefix


def run(task, root, directory, timeout, environment, expected_commit):
    with tempfile.TemporaryDirectory(prefix='rust-archive-', dir=directory.parent.parent) as work:
        work = Path(work).resolve()
        candidate = distribution.clean_candidate(root)
        distribution.require(candidate['commit'] == expected_commit, 'archive test commit differs')
        tracked = distribution.tracked_files(root, expected_commit)
        archive = work / 'source.tar'
        with archive.open('xb') as output:
            subprocess.run(distribution.source_archive_command(expected_commit), cwd=root,
                           stdout=output, check=True)
        files = distribution.read_archive(archive, expected=tracked)
        source = work / 'source'
        target = work / 'target'
        distribution.extract_checked(files, source)
        with archive.open('rb') as stream:
            archive_sha256 = hashlib.file_digest(stream, 'sha256').hexdigest()
        result = ci_runtime.run_task(task, source, directory, timeout, environment | {
            'CARGO_TARGET_DIR': str(target), 'CARGO_NET_OFFLINE': 'true',
        })
        with archive.open('rb') as stream:
            distribution.require(hashlib.file_digest(stream, 'sha256').hexdigest() == archive_sha256,
                                 'source archive bytes changed during Rust tests')
        distribution.verify_extracted_source(files, source)
        distribution.require(distribution.clean_candidate(root) == candidate,
                             'checkout changed during archive Rust tests')
        return result | dict(archive=dict(candidate=candidate, sha256=archive_sha256,
                                          source=str(source), target=str(target), offline=True))


def verify_execution(command, source, target, full_commands, metadata_raw, record):
    """Check literal selection, Cargo inventory and every native-gated harness."""
    require = distribution.require
    metadata = json_object(metadata_raw, 'archive Cargo metadata')
    require(metadata.get('target_directory') == str(target), 'archive Cargo target directory differs')
    partition.validate('rust-latest', full_commands, metadata, source)
    head = partition.WRAPPER + partition.SCHEDULER
    require(command[:len(head)] == head, 'different archive scheduler command')
    cargo = command[len(head):]
    entry, expected = run_rust_tests.selection(cargo, metadata, source)
    require(entry == partition.LATEST, 'different archive Cargo entry point')
    require(record.get('format') == 1 and type(record['format']) is int
            and record.get('status') == 'passed' and record.get('command') == cargo
            and record.get('metadata_sha256') == distribution.digest(metadata_raw)
            and record.get('workers') == 2 and record.get('harness_threads') == 2
            and record.get('isolated_harness_threads') == 1
            and record.get('isolated_harnesses') == [list(key) for key in sorted(run_rust_tests.ISOLATED)]
            and record.get('expected') == [list(key) for key in sorted(expected)]
            and type(record.get('build_exit_code')) is int and record['build_exit_code'] == 0
            and record.get('build_command') == ci_runtime.launch_command(
                cargo + ['--locked', '--no-run', '--message-format=json']),
            'changed or incomplete archived Rust scheduler report')
    rows = record.get('harnesses')
    require(type(rows) is list and len(rows) == len(expected), 'incomplete archived Rust harnesses')
    metadata_targets = {(row['kind'][0], row['name']): row
                        for row in metadata['packages'][0]['targets']}
    passed = 0
    for (kind, name), row in zip(sorted(expected), rows):
        require(type(row) is dict and (row.get('kind'), row.get('name')) == (kind, name)
                and row.get('status') == 'passed' and type(row.get('exit_code')) is int
                and row['exit_code'] == 0 and row.get('native_skips') is False
                and type(row.get('passed')) is int and row['passed'] >= 0
                and row.get('package_id') == metadata['packages'][0]['id']
                and row.get('target') == metadata_targets[kind, name],
                'failed, skipped or different archived Rust harness')
        executable = Path(row['executable'])
        require(executable.is_absolute() and executable.is_relative_to(target)
                and '..' not in executable.parts
                and isinstance(row.get('sha256'), str) and len(row['sha256']) == 64
                and all(char in '0123456789abcdef' for char in row['sha256']),
                'invalid archived Rust harness executable')
        selector = ['--lib'] if kind == 'lib' else ['--' + kind, name]
        command = ci_runtime.launch_command(partition.LATEST + ['test', '--locked'] + selector)
        isolated = (kind, name) in run_rust_tests.ISOLATED
        require(row.get('isolated') is isolated and row.get('test_threads') == (1 if isolated else 2)
                and row.get('command') == command
                and row.get('executed_command') == command + run_rust_tests.TEST_ARGUMENTS[:-1]
                + ['1' if isolated else '2'], 'different archived Rust harness invocation')
        passed += row['passed']
    require(passed > 0, 'no archived Rust tests passed')
