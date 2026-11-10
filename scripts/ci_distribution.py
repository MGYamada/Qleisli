"""Join the same-run package checks and independently verified archive tests.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import os
from pathlib import Path
import sys

from check_ratification_packet import json_object, read_file
from check_release_ready import capture_context
from ci_rust_artifacts import archive_evidence, digest, encoded, require, validate_aggregate, verify_archive_evidence


def package_output(path, env):
    require(env.get('GITHUB_JOB') == 'check-distribution-package', 'wrong package job')
    raw = read_file(path.parent, path.name)
    require(json_object(raw, 'package report').get('status') == 'package-passed',
            'incomplete package checks')
    with open(env['GITHUB_OUTPUT'], 'a') as output:
        output.write(f'package_sha256={digest(raw)}\n')


def join(root, package, rust_directory, output, env):
    require(env.get('GITHUB_JOB') == 'check-distribution', 'wrong distribution join job')
    context = capture_context(root, env)
    require(output.resolve().parent == package.parent.resolve()
            and not output.resolve().is_relative_to(root), 'join report must stay with package evidence')
    raw = read_file(package.parent, package.name)
    require(digest(raw) == env.get('PACKAGE_REPORT_SHA256'),
            'package report differs from trusted producer output')
    report = json_object(raw, 'package report')
    require(report.get('format') == 'qleisli.distribution-validation' and report.get('version') == 2
            and report.get('status') == 'package-passed' and 'archive_rust' not in report
            and report.get('candidate') == dict(commit=context['commit'], tree=context['tree'], clean=True),
            'failed or different package candidate')
    rust = {name: read_file(rust_directory, name)
            for name in ('aggregate.json', 'differential.json', 'remaining.json')}
    require(digest(rust['aggregate.json']) == env.get('RUST_AGGREGATE_SHA256'),
            'Rust aggregate differs from trusted producer output')
    validate_aggregate(root, context, 'latest', rust)
    # Resolve producer paths in the downloaded artifact rather than assuming
    # the producer and consumer used the same runner temporary directory.
    old_artifacts = Path(report['artifacts'])
    artifacts = package.parent / old_artifacts.name
    require(artifacts.parent == package.parent and artifacts.name.startswith(package.stem + '-artifacts-'),
            'invalid distribution artifact directory')
    for key in ('crate', 'source_archive'):
        previous = Path(report[key]['path'])
        require(previous.parent == old_artifacts, 'artifact path differs from package report')
        relative = artifacts.name + '/' + previous.name
        require(report[key]['sha256'] == digest(read_file(package.parent, relative)),
                f'{key} differs from package producer digest')
        report[key]['path'] = str(artifacts / previous.name)
    report['artifacts'] = str(artifacts)
    report['archive_rust'] = archive_evidence(rust)
    verify_archive_evidence(report, rust)
    require(capture_context(root, env) == context, 'candidate changed during distribution join')
    report.update(status='passed', package_report_sha256=digest(raw))
    with output.open('xb') as stream:
        stream.write(encoded(report))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', required=True, type=Path)
    parser.add_argument('--rust', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        if args.rust is None and args.output is None:
            package_output(args.package, os.environ)
        else:
            require(args.rust is not None and args.output is not None, 'join requires --rust and --output')
            join(Path(__file__).resolve().parents[1], args.package, args.rust, args.output, os.environ)
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f'Distribution evidence refused: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
