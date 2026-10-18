"""Validate passive Rust CI receipts against both actual producers and this source.

These records describe executed CI commands. They grant no Qleisli acceptance,
compiler/runtime proof, authenticated provenance outside the calling workflow,
or release approval.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import sys

import ci_runtime
import ci_source_checks as checks
from ci_rust_producers import RUST_SUITES, SHA, expected_producer_receipts, producer_jobs, require, validate_context
from check_ratification_packet import ROOT, exact_keys, json_object, read_file

LIMIT = 16 * 1024 * 1024
QUICK_FAULTS = {'rx_missing_scalar', 'swapped_bell_labels', 'missing_add_two', 'incomplete_swap'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def same_data(left, right):
    # Preserve JSON types: False/0 and True/1 are not interchangeable metadata.
    return json.dumps(left, sort_keys=True, allow_nan=False) == json.dumps(right, sort_keys=True, allow_nan=False)


def blob(data):
    require(len(data) <= LIMIT, 'Rust CI metadata exceeds its size limit')
    return dict(sha256=digest(data), base64=base64.b64encode(data).decode())


def unblob(value):
    exact_keys(value, {'sha256', 'base64'}, 'Rust report bytes')
    require(type(value['base64']) is str and len(value['base64']) <= (LIMIT + 2) // 3 * 4,
            'invalid Rust report byte size')
    data = base64.b64decode(value['base64'], validate=True)
    require(len(data) <= LIMIT and value['sha256'] == digest(data), 'changed Rust report bytes')
    return data


def groups(profile, partition):
    producer_jobs(profile)
    require(partition in {'differential', 'remaining'}, 'unknown Rust producer partition')
    result = {f'rust-{profile}': partition}
    if partition == 'remaining':
        result['source-contracts'] = None
        if profile == 'latest':
            result['source-semantics'] = None
        result[f'rust-{profile}-lint-research'] = None
    return result


def binary_identity(root, value, path):
    exact_keys(value, {'path', 'sha256'}, 'Rust binary identity')
    require(value['path'] == str(root / path) and type(value['sha256']) is str
            and SHA.fullmatch(value['sha256']), 'wrong Rust binary identity')


def check_source_report(root, raw, group, partition, binding, manifest_raw, kernel, compiler):
    report = json_object(raw, group)
    require(type(report.get('format')) is int and report['format'] == 1
            and report.get('group') == group and report.get('status') == 'passed', 'incomplete Rust source report')
    spec = checks.describe(group, partition=partition, root=root, contents=manifest_raw)
    require(same_data(report.get('plan'), spec) and report.get('binding') == binding
            and report.get('manifest_sha256') == digest(manifest_raw), 'stale or changed Rust source plan/binding')
    commands = [[str(root / 'target/debug/qleisli') if arg == '{compiler}' else arg for arg in argv]
                for argv in spec['commands']]
    actual = report.get('commands')
    require(type(actual) is list and len(actual) == len(commands), 'missing Rust command results')
    for number, (row, argv) in enumerate(zip(actual, commands)):
        require(type(row) is dict and row.get('argv') == argv and row.get('id') == str(number)
                and row.get('status') == 'passed', 'failed or different Rust command')
        log = row.get('log')
        require(type(log) is str and '\x00' not in log and Path(log).is_absolute()
                and '..' not in Path(log).parts, 'invalid Rust command log identity')
        nested = row.get('commands')
        require(type(nested) is list and len(nested) == 1 and type(nested[0]) is dict,
                'missing executed Rust command')
        expected = ci_runtime.record_command(argv, Path(log).parent)
        run = nested[0]
        require(run.get('command') == expected and run.get('executed_command') == ci_runtime.launch_command(expected)
                and run.get('status') == 'passed' and type(run.get('exit_code')) is int
                and run['exit_code'] == 0, 'Rust command failed or changed after selection')
    tools = report.get('toolchain')
    require(type(tools) is dict and set(tools) == set(spec['tools']), 'missing Rust toolchain probes')
    for name, tool in spec['tools'].items():
        observed = tools[name]
        require(type(observed) is dict and observed.get('command') == ci_runtime.launch_command(tool['command'])
                and type(observed.get('exit_code')) is int and observed['exit_code'] == 0
                and type(observed.get('version')) is str
                and re.fullmatch(tool['pattern'], observed['version']), 'wrong Rust toolchain version')
    environment = report.get('environment')
    require(type(environment) is dict, 'missing Rust execution environment')
    declared = {key: value.replace('{root}', str(root)) for key, value in spec['environment'].items()}
    declared.update(CARGO_PROFILE_DEV_DEBUG='0', CARGO_PROFILE_TEST_DEBUG='0', CARGO_INCREMENTAL='0')
    require(all(environment.get(key) == value for key, value in declared.items()), 'changed Rust execution settings')
    require(not {'RUSTFLAGS', 'CARGO_ENCODED_RUSTFLAGS', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER'} & set(environment),
            'unreviewed Rust compiler override')
    require(report.get('kernel') == kernel, 'different native checker across Rust checks')
    required_compiler = group in {'source-contracts', 'source-semantics'}
    require((report.get('compiler') == compiler) if required_compiler else 'compiler' not in report,
            'different or unexpected source compiler')


def check_corpus(root, raw, compiler, read_source):
    from check_input_corpus import representative_entries
    report = json_object(raw, 'Rust corpus report')
    manifest_raw = read_source('corpus/manifest.json')
    manifest = json_object(manifest_raw, 'corpus manifest')
    negative_raw = read_source('corpus/' + manifest['negative_expectations']['path'])
    require(digest(negative_raw) == manifest['negative_expectations']['sha256'], 'changed corpus counterexample manifest')
    negative = json_object(negative_raw, 'negative manifest')
    require(type(report.get('format')) is int and report['format'] == 1 and report.get('status') == 'passed'
            and report.get('validation_mode') == 'quick-representative-v1' and report.get('failures') == []
            and report.get('manifest_sha256') == digest(manifest_raw)
            and report.get('oracle_script_sha256') == digest(read_source('scripts/check_input_corpus.py'))
            and report.get('compiler_sha256') == compiler['sha256'], 'wrong or incomplete Rust corpus report')
    expected = {'cases': {row['id'] for row in manifest['cases']}, 'semantic_faults': QUICK_FAULTS,
                'negative_cases': {row['id'] for row in negative['cases']}}
    probes = representative_entries(manifest['cases'])
    require(same_data(report.get('representative_entries'), json.loads(json.dumps(probes)))
            and report.get('exhaustive_unitary_entries') is False
            and report.get('upstream_frameworks_executed') is False, 'changed Rust corpus checking profile')
    require(type(report.get('expected_ids')) is dict and set(report['expected_ids']) == set(expected),
            'missing Rust corpus coverage')
    for key, identifiers in expected.items():
        rows, declared = report.get(key), report['expected_ids'][key]
        require(type(rows) is list and all(type(row) is dict and type(row.get('id')) is str for row in rows)
                and len(rows) == len(identifiers) and {row['id'] for row in rows} == identifiers
                and type(declared) is list and len(declared) == len(identifiers) and set(declared) == identifiers,
                'omitted or duplicate Rust corpus observations')
    require(all(row.get('shipped_main') == 'passed' and type(row.get('semantic_probes')) is int
                and row['semantic_probes'] == (2 if row['id'] in probes else 0) for row in report['cases']),
            'failed or omitted Rust corpus probes')
    require(all(row.get('typecheck') == 'passed' and type(row.get('semantic_mismatch')) is str
                and row['semantic_mismatch'] for row in report['semantic_faults']), 'undetected Rust semantic fault')
    codes = {row['id']: row['expected_code'] for row in negative['cases']}
    require(all(type(row.get('exit_code')) is int and row['exit_code'] == 1
                and row.get('code') == codes[row['id']] for row in report['negative_cases']),
            'wrong Rust counterexample result')


def validate_child(root, context, profile, partition, raw, binding=None, read_source=None):
    require(len(raw) <= LIMIT, 'Rust producer receipt exceeds its size limit')
    receipt = json_object(raw, 'Rust producer receipt')
    fields = {'format', 'version', 'context', 'job', 'profile', 'partition', 'binding',
              'manifest_sha256', 'kernel', 'compiler', 'reports', 'corpus'}
    exact_keys(receipt, fields, 'Rust producer receipt')
    validate_context(context)
    require(receipt['format'] == 'qleisli.ci-rust-producer' and type(receipt['version']) is int
            and receipt['version'] == 1 and receipt['context'] == context
            and receipt['profile'] == profile and receipt['partition'] == partition
            and receipt['job'] == producer_jobs(profile)[partition], 'wrong Rust producer identity')
    binding = checks.snapshot(root) if binding is None else binding
    require(binding['head'] == context['commit'] and receipt['binding'] == binding,
            'Rust producer source differs from this candidate')
    read_source = (lambda name: read_file(root, name)) if read_source is None else read_source
    manifest_raw = read_source('.github/ci/source-checks.json')
    require(receipt['manifest_sha256'] == digest(manifest_raw), 'different Rust source-check manifest')
    binary_identity(root, receipt['kernel'], 'lean-kernel/.lake/build/bin/qleisli-kernel')
    if partition == 'remaining':
        binary_identity(root, receipt['compiler'], 'target/debug/qleisli')
    else:
        require(receipt['compiler'] is None, 'unexpected differential compiler claim')
    expected = groups(profile, partition)
    require(type(receipt['reports']) is dict and set(receipt['reports']) == set(expected),
            'missing or unexpected Rust source-check group')
    for group, selected in expected.items():
        check_source_report(root, unblob(receipt['reports'][group]), group, selected, binding,
                            manifest_raw, receipt['kernel'], receipt['compiler'])
    if profile == 'latest' and partition == 'remaining':
        check_corpus(root, unblob(receipt['corpus']), receipt['compiler'], read_source)
    else:
        require(receipt['corpus'] is None, 'unexpected Rust corpus claim')
    return receipt


def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + '\n').encode()


def aggregate_files(root, context, profile, children, *, needs=None, binding=None, read_source=None):
    require(type(children) is dict and set(children) == {'differential', 'remaining'}, 'incomplete Rust artifact pair')
    expected = expected_producer_receipts(needs, profile, context) if needs is not None else None
    binding = checks.snapshot(root) if binding is None else binding
    files, identities = {}, {}
    for partition in ('differential', 'remaining'):
        raw = children[partition]
        require(type(raw) is bytes, 'Rust receipt must be the actual downloaded bytes')
        if expected is not None:
            require(digest(raw) == expected[partition]['sha256'], 'Rust artifact differs from trusted producer output')
        validate_child(root, context, profile, partition, raw, binding, read_source)
        files[partition + '.json'] = raw
        identities[partition] = dict(job=producer_jobs(profile)[partition], sha256=digest(raw))
    files['aggregate.json'] = encoded(dict(format='qleisli.ci-rust-aggregate', version=1,
                                         context=context, profile=profile, children=identities))
    return files


def validate_aggregate(root, context, profile, files, *, needs=None, binding=None, read_source=None):
    require(type(files) is dict and set(files) == {'aggregate.json', 'differential.json', 'remaining.json'},
            'missing or unexpected aggregate Rust artifacts')
    expected = aggregate_files(root, context, profile,
                               {part: files[part + '.json'] for part in ('differential', 'remaining')},
                               needs=needs, binding=binding, read_source=read_source)
    # Exact canonical bytes bind the descriptor to both independently inspected children.
    require(files['aggregate.json'] == expected['aggregate.json'], 'changed aggregate Rust receipt')
    return files


def write_files(output, files):
    output.mkdir(parents=True, exist_ok=False)
    for name, data in files.items():
        with (output / name).open('xb') as stream:
            stream.write(data)


def record_producer(root, profile, partition, results, output, env):
    from check_release_ready import capture_context
    context = capture_context(root, env)
    require(env.get('GITHUB_JOB') == producer_jobs(profile)[partition], 'wrong actual Rust producer job')
    require(not output.resolve().is_relative_to(root), 'Rust receipt must be outside the candidate')
    binding = checks.snapshot(root)
    kernel_path = 'lean-kernel/.lake/build/bin/qleisli-kernel'
    require(env.get('QLEISLI_KERNEL') == str(root / kernel_path), 'wrong selected native Rust checker')
    kernel = dict(path=str(root / kernel_path), sha256=digest(read_file(root, kernel_path)))
    compiler = (dict(path=str(root / 'target/debug/qleisli'), sha256=digest(read_file(root, 'target/debug/qleisli')))
                if partition == 'remaining' else None)
    reports = {}
    for group, selected in groups(profile, partition).items():
        directory = group if selected is None else group + '-' + selected
        reports[group] = blob(read_file(results, directory + '/results.json'))
    corpus = blob(read_file(results, 'corpus.json')) if profile == 'latest' and partition == 'remaining' else None
    raw = encoded(dict(format='qleisli.ci-rust-producer', version=1, context=context,
                       job=env['GITHUB_JOB'], profile=profile, partition=partition, binding=binding,
                       manifest_sha256=digest(read_file(root, '.github/ci/source-checks.json')),
                       kernel=kernel, compiler=compiler, reports=reports, corpus=corpus))
    validate_child(root, context, profile, partition, raw, binding)
    require(capture_context(root, env) == context and checks.snapshot(root) == binding
            and digest(read_file(root, kernel_path)) == kernel['sha256']
            and (compiler is None or digest(read_file(root, 'target/debug/qleisli')) == compiler['sha256']),
            'Rust source or binary changed while recording evidence')
    write_files(output, {'receipt.json': raw})
    with open(env['GITHUB_OUTPUT'], 'a') as stream:
        for name, value in dict(source_head=context['commit'], source_tree=context['tree'],
                                source_run_id=context['run_id'], source_attempt=context['attempt'],
                                rust_receipt_sha256=digest(raw)).items():
            stream.write(f'{name}={value}\n')


def record_aggregate(root, profile, evidence, output, env):
    from check_release_ready import capture_context
    context = capture_context(root, env)
    require(env.get('GITHUB_JOB') == RUST_SUITES[profile], 'wrong actual Rust aggregate job')
    require(not output.resolve().is_relative_to(root), 'Rust aggregate must be outside the candidate')
    needs = json_object(env.get('RUST_NEEDS_JSON', '').encode(), 'trusted Rust dependency outputs')
    expected_producer_receipts(needs, profile, context)
    children = {part: read_file(evidence, f'rust-validation-{profile}-{part}-{context["commit"]}-{context["attempt"]}/receipt.json')
                for part in ('differential', 'remaining')}
    binding = checks.snapshot(root)
    files = aggregate_files(root, context, profile, children, needs=needs, binding=binding)
    require(capture_context(root, env) == context and checks.snapshot(root) == binding,
            'Rust aggregate source changed during artifact verification')
    write_files(output, files)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', choices=['latest', 'msrv'], required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--partition', choices=['differential', 'remaining'])
    mode.add_argument('--aggregate', action='store_true')
    parser.add_argument('--results', type=Path)
    parser.add_argument('--evidence', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.aggregate:
            require(args.evidence is not None and args.results is None, 'aggregate requires only --evidence')
            record_aggregate(ROOT, args.profile, args.evidence, args.output, os.environ)
        else:
            require(args.results is not None and args.evidence is None, 'producer requires only --results')
            record_producer(ROOT, args.profile, args.partition, args.results, args.output, os.environ)
        return 0
    except (OSError, ValueError, KeyError, TypeError, UnicodeError) as error:
        print('Rust CI artifacts: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
