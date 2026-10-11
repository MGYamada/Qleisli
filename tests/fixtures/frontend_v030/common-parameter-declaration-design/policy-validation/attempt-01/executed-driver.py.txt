#!/usr/bin/env python3
"""Fixed parameter-name policy checks; historical metadata regressions are not rerun.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import concurrent.futures
import datetime
import hashlib
import gzip
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
ROOT = Path('/Users/masa/git/Qleisli')
HERE = Path(__file__).resolve().parent
MDBOOK = Path('/private/tmp/qleisli-mdbook-0.5.4-bin/mdbook')
BASE = 'faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2'
CLI = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
STUDY = ROOT / 'tests/fixtures/authoring_sessions/common-parameter-declaration-v030'
VALIDATION = ROOT / 'tests/fixtures/frontend_v030/common-parameter-declaration-design/validation'
METADATA_REVIEW = ROOT / 'tests/fixtures/frontend_v030/common-parameter-declaration-design/metadata-review'
OLD_REGRESSIONS = ROOT / 'tests/fixtures/frontend_v030/common-pattern-design/metadata-review'
OLD_POLICY_IDENTITY = ROOT / 'tests/fixtures/frontend_v030/common-pattern-design/policy-validation/attempt-01/identity.after.json'
METADATA_RECORD_HASHES = {'driver.py': 'cc7337078169660699db8431ac3446a2d3617c3607b39eab2e5c736cf3474c5f', 'source-inputs.before.json': '768838b26876fc26efa62758dfeb3facd995c3432f1f3bd36093611990b7a4a6', 'commands.before.json': '99ace85999be938d2cfbe7cbda7a9c1b0b92590e06b754578308480bf200458d', 'results.json': '9c2fe7ec1435b979c31d7f140ca8cc402920c0ea266fab9685840c625bda0609', 'inventory.before.json.gz': '79a8b79a36aa28506015a4b4e1e562b4fcd8869cba405a534d1870714642e552', 'coverage.before.json.gz': 'ddff77fdcd2282355bfb63d9c499d124ec0ad62306db4ef65dc3a8b2ab203327', 'inventory.after.json.gz': '31c097b4b48b9402641e206d280de4c75d032328a0a82a3425d857ef939e2efa', 'coverage.after.json.gz': '76cfc95d56b11678be2f572b90b9490524792bbffe5df142bcabceb0d869e872', 'before.inventory.stdout.txt': 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855', 'before.inventory.stderr.txt': '81d66a611e55fcfb26971e3add6616941d0e43f635b44e6cf022074cc69163a3', 'before.coverage.stdout.txt': '6bf1f5e58aa6cc2f70c03b3667c992750442dcbe69f91e676bd363c8bde5d930', 'before.coverage.stderr.txt': 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855', 'after.inventory.stdout.txt': '34d429a631330194e5babaadd8bad8e4e9ff2ddc2c769c51bfd67f8ad52f0081', 'after.inventory.stderr.txt': 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855', 'after.coverage.stdout.txt': '6bf1f5e58aa6cc2f70c03b3667c992750442dcbe69f91e676bd363c8bde5d930', 'after.coverage.stderr.txt': 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'}
OLD_REGRESSION_HASHES = {'results.json': 'fae904133d8bcc50413308a011b3a5759bc241d5a73a455842177c70c308e718', 'commands.after.json': '65cc579948704cdc0ae4d9d235dc9d22a5d79bf05428f5a691590dcf737e75a9', 'after.inventory-regression.stdout.txt': 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855', 'after.inventory-regression.stderr.txt': '04eb3dc258bef8dee089f7fe6ba8bac17281dc03f01538cb11dbc837a2b14d4e', 'after.coverage-regression.stdout.txt': 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855', 'after.coverage-regression.stderr.txt': 'e269e66833b388e0094c23daae4694b4692e3e8a894128b34c77952d4b844c0b'}
OLD_POLICY_IDENTITY_SHA256 = 'facf3c4eeaee40725a9ef08172376c83b99f2d8cbcca66adb298a1d0cd0fce54'

STUDY_PROTECTED = {
    'driver.py': '472756feaf2c8ef3c8ec97df25216885708ac8aaea0221147742cfa2c9a2f426',
    'first-files.json': 'b7babe5509ef85fd2aa10b27d07b346083645971a7d26a608d3915f5dda6e2a2',
    'files-before.json': 'd40022d2d61500baff63e7b97439e47637b6a2f745c936174fa27d5d98f3c936',
    'observe-after.py': 'd091ebd76f199fb659ab3a5d8759972b35fe32f8af11d572c8ee63ff339662fe',
    'results-before.md': 'cc2ac246e1eac8edfeffc39a215b24c8dc039a074c57b246423f03fa9c4daf26',
}
EXPECTED_REGRESSIONS = {
    '03.book-regression': 12, '05.authoring-regression': 7,
    '07.edition-regression': 11, '09.docs-regression': 36,
}
NATIVE = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
NATIVE_SHA256 = '39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85'
CHANGED_PATHS = (
    'src/frontend/pattern.rs', 'src/frontend/compile/mod.rs',
    'src/frontend/sized/check.rs',
)
CHECK_SCRIPTS = (
    'check_book.py', 'test_check_book.py',
    'check_authoring_sessions.py', 'test_check_authoring_sessions.py',
    'check_editions.py', 'test_check_editions.py',
    'check_docs.py', 'test_check_docs.py',
    'check_constitution.py', 'check_lean_kernel.py',
    'check_verification_inventory.py', 'test_check_verification_inventory.py',
    'check_production_coverage.py', 'test_check_production_coverage.py',
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(out, name, value):
    with (out / name).open('x', encoding='utf-8') as stream:
        stream.write(json.dumps(value, indent=2) + '\n')


def inputs():
    paths = list((ROOT / 'src').rglob('*.rs'))
    paths += [ROOT / name for name in CHANGED_PATHS]
    paths += [ROOT / 'scripts' / name for name in CHECK_SCRIPTS]
    for directory in ('docs', 'governance'):
        paths += [p for p in (ROOT / directory).rglob('*')
                  if p.is_file() and not p.is_symlink()]
    paths += list((ROOT / 'tests/fixtures/authoring_sessions').glob('*/session.json'))
    paths += list((ROOT / 'stdlib').rglob('*.qli'))
    paths += list((ROOT / 'stdlib').rglob('*.toml'))
    paths += [p for p in (ROOT / 'lean-kernel').rglob('*.lean') if '.lake' not in p.parts]
    paths += [Path(__file__), HERE / 'README.md', OLD_POLICY_IDENTITY]
    paths += [METADATA_REVIEW / name for name in METADATA_RECORD_HASHES]
    paths += [OLD_REGRESSIONS / name for name in OLD_REGRESSION_HASHES]
    # Terminal study/build records are read only as identity/evidence data.
    # Their argv is never used to construct an executable command.
    paths += [p for p in STUDY.rglob('*') if p.is_file()]
    paths += [p for p in VALIDATION.rglob('*') if p.is_file()]
    reviewed = json.loads((METADATA_REVIEW / 'source-inputs.before.json').read_text())['files']
    paths += [ROOT / name for name in reviewed]
    paths += [ROOT / name for name in (
        'AGENTS.md', 'CLAUDE.md', 'README.md', 'ROADMAP.md', 'TRUSTBOUNDARY.md',
        'CONSTITUTION.md', 'GOVERNANCE.md', 'CHANGELOG.md', 'Cargo.toml', 'Cargo.lock',
        '.github/workflows/ci.yml', '.github/ci/README.md',
        'tests/fixtures/verification_v022/inventory.json',
        'tests/fixtures/verification_v029/coverage.json',
        'lean-kernel/lean-toolchain', 'lean-kernel/lakefile.toml',
        'lean-kernel/lake-manifest.json',
        'tests/fixtures/authoring_sessions/README.md',
        'tests/fixtures/frontend_v030/common-parameter-declaration-design/candidate-01.md',
        'tests/fixtures/frontend_v030/common-parameter-declaration-design/contract-before-code.md',
        'tests/fixtures/frontend_v030/common-parameter-declaration-design/author-design.md',
        'tests/fixtures/frontend_v030/common-parameter-declaration-design/independent-implementation-review.md',
        'tests/fixtures/frontend_v030/common-parameter-declaration-design/validation/driver.py',
        'tests/fixtures/frontend_v030/common-parameter-declaration-design/validation/selection.json',
    )]
    return {str(p.relative_to(ROOT)): sha(p) for p in sorted(set(paths))}


def run(out, name, argv):
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    begin = time.monotonic()
    stdout, stderr = out / (name + '.stdout.txt'), out / (name + '.stderr.txt')
    exit_code, launch_error, timed_out = None, None, False
    with stdout.open('xb') as output, stderr.open('xb') as errors:
        try:
            result = subprocess.run(argv, cwd=ROOT, env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'),
                                    stdout=output, stderr=errors, check=False, timeout=180)
            exit_code = result.returncode
        except OSError as error:
            launch_error = repr(error)
        except subprocess.TimeoutExpired:
            timed_out = True
    record = dict(id=name, argv=argv, cwd=str(ROOT), started_at_utc=started,
                  elapsed_seconds=time.monotonic() - begin, exit_code=exit_code,
                  launch_error=launch_error, timed_out=timed_out,
                  stdout=dict(path=stdout.name, sha256=sha(stdout), bytes=stdout.stat().st_size),
                  stderr=dict(path=stderr.name, sha256=sha(stderr), bytes=stderr.stat().st_size))
    save(out, name + '.json', record)
    print(f'{name}: actual exit {exit_code}; launch error {launch_error}; timeout {timed_out}', flush=True)
    return record



def separately_performed_metadata():
    """Bind the current three-file review, never the old pattern source map."""
    for directory, hashes in (
        (METADATA_REVIEW, METADATA_RECORD_HASHES),
        (OLD_REGRESSIONS, OLD_REGRESSION_HASHES),
    ):
        for name, digest in hashes.items():
            if sha(directory / name) != digest:
                raise ValueError('Retained metadata record changed: ' + str(directory / name))
    reviewed = json.loads((METADATA_REVIEW / 'source-inputs.before.json').read_text())['files']
    result = json.loads((METADATA_REVIEW / 'results.json').read_text())
    if (len(reviewed) != 253 or result['source_count'] != 253 or
            not result['source_inputs_unchanged'] or
            not result['other_parsed_metadata_fields_unchanged'] or
            {row['path'] for row in result['source_changes']} != set(CHANGED_PATHS)):
        raise ValueError('Current metadata review scope/invariants differ')
    for name, digest in reviewed.items():
        if sha(ROOT / name) != digest:
            raise ValueError('Source changed after current metadata review: ' + name)
    for name, compressed in (
        ('tests/fixtures/verification_v022/inventory.json', 'inventory.after.json.gz'),
        ('tests/fixtures/verification_v029/coverage.json', 'coverage.after.json.gz'),
    ):
        if (ROOT / name).read_bytes() != gzip.decompress((METADATA_REVIEW / compressed).read_bytes()):
            raise ValueError('Active metadata differs from its current reviewed after copy: ' + name)
    if ([row['exit_code'] for row in result['before']] != [1, 0] or
            [row['exit_code'] for row in result['after']] != [0, 0]):
        raise ValueError('Current retained inventory/coverage guard results differ')
    old_result = json.loads((OLD_REGRESSIONS / 'results.json').read_text())
    if old_result['status'] != 'passed' or any(row['exit_code'] != 0 for row in old_result['actual_checks']):
        raise ValueError('Earlier metadata regression results are incomplete')
    for kind, count in (('inventory', 17), ('coverage', 14)):
        raw = (OLD_REGRESSIONS / ('after.' + kind + '-regression.stderr.txt')).read_text()
        match = re.search(r'Ran (\d+) tests in ', raw)
        if not match or int(match[1]) != count or not raw.rstrip().endswith('OK'):
            raise ValueError('Earlier raw metadata regression result differs: ' + kind)
    if sha(OLD_POLICY_IDENTITY) != OLD_POLICY_IDENTITY_SHA256:
        raise ValueError('Earlier policy identity record changed')
    prior_scripts = json.loads(OLD_POLICY_IDENTITY.read_text())['files']
    for name in ('check_verification_inventory.py', 'check_production_coverage.py',
                 'test_check_verification_inventory.py', 'test_check_production_coverage.py'):
        path = 'scripts/' + name
        if sha(ROOT / path) != prior_scripts[path]:
            raise ValueError('Metadata guard/regression script changed since prior policy: ' + name)
    return dict(current_root_record=str((METADATA_REVIEW / 'results.json').relative_to(ROOT)),
                current_guard_exits=dict(inventory_before=1, inventory_after=0,
                                         coverage_before=0, coverage_after=0),
                current_source_count=253,
                old_root_regression_record=str((OLD_REGRESSIONS / 'results.json').relative_to(ROOT)),
                historical_metadata_regression_counts=dict(inventory=17, coverage=14),
                guard_scripts_match_prior_policy_map=True,
                metadata_regressions_rerun_by_this_driver=False,
                recorded_commands_executed=False,
                identity_limit='Current three-file review is separately bound. The older mutation packet did not freeze regression-script bytes at historical execution; a later policy map is retained, not a manufactured complete historical build/test closure.')


def completed_root_packets():
    """Require terminal records; capture their final bytes only at root execution."""
    for name, digest in STUDY_PROTECTED.items():
        if sha(STUDY / name) != digest:
            raise ValueError('Protected original study record changed: ' + name)
    frozen_before = json.loads((STUDY / 'files-before.json').read_text())['files']
    if len(frozen_before) != 200:
        raise ValueError('Original before packet count changed')
    for name, row in frozen_before.items():
        if sha(STUDY / name) != row['sha256']:
            raise ValueError('Original before packet changed: ' + name)
    after = STUDY / 'after-attempt-01'
    summary = json.loads((after / 'summary.json').read_text())
    if (summary['status'] != 'all_equal' or summary['actual_observation_count'] != 40 or
            summary['actual_native_calls'] != 44 or summary['output_normalizations'] != 0):
        raise ValueError('Root after comparison is not the complete unchanged forty checks')
    after_files = json.loads((after / 'files.json').read_text())['files']
    for name, row in after_files.items():
        if sha(after / name) != row['sha256']:
            raise ValueError('Root after packet changed: ' + name)
    after_identity = json.loads((after / 'identity.final.json').read_text())['identity']
    for name in CHANGED_PATHS:
        if sha(ROOT / name) != after_identity['files'][name]:
            raise ValueError('Source differs from the completed root after comparison: ' + name)
    rust = {}
    for mode in ('latest', 'msrv'):
        directory = VALIDATION / (mode + '-attempt-01')
        result = json.loads((directory / 'results.json').read_text())
        if (result['status'] != 'passed' or result['remaining_stages_not_run'] != 0 or
                len(result['records']) != 8 or not result['source_inputs_unchanged'] or
                any(row['exit_code'] != 0 or row['launch_error'] or row['timed_out'] or
                    row['postcondition_error'] for row in result['records'])):
            raise ValueError('Root Rust validation is not terminal success: ' + mode)
        source = json.loads((directory / 'inputs-after.json').read_text())['files']
        for name in CHANGED_PATHS:
            if sha(ROOT / name) != source[name]:
                raise ValueError('Source differs from root Rust validation: ' + mode + ' ' + name)
        rust[mode] = dict(record=str((directory / 'results.json').relative_to(ROOT)),
                         record_sha256=sha(directory / 'results.json'), stages=8)
    return dict(before_map_sha256=sha(STUDY / 'files-before.json'),
                before_packet_file_count=200,
                after_map_sha256=sha(after / 'files.json'),
                after_packet_file_count=len(after_files),
                root_after_observations=40, root_after_native_calls=44,
                root_after_output_normalizations=0, root_rust_records=rust,
                scope='Separate completed root observations/validation identities; this driver does not replay them or claim complete proof/build closure.')


def main():
    if len(sys.argv) != 2 or not re.fullmatch(r'attempt-[0-9]{2}', sys.argv[1]):
        raise SystemExit('usage: driver.py attempt-NN; root runs after source/metadata/Reference barrier')
    out = HERE / sys.argv[1]
    out.mkdir(exist_ok=False)
    before = inputs()
    book_before, native_before, cli_before = sha(MDBOOK), sha(NATIVE), sha(CLI)
    save(out, 'identity.before.json', dict(status='selected-policy-input-byte-identities',
         observed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), files=before,
         changed_paths={name: before[name] for name in CHANGED_PATHS},
         mdbook_path=str(MDBOOK), mdbook_sha256=book_before,
         native_path=str(NATIVE), native_sha256=native_before,
         cli_path=str(CLI), cli_sha256=cli_before,
         python_executable=sys.executable, python_version=sys.version,
         identity_limit='Declared input map only, not complete fixture/proof/build closure or authentication.'))
    (out / 'executed-driver.py.txt').open('xb').write(Path(__file__).read_bytes())
    if sys.version_info < (3, 11) or native_before != NATIVE_SHA256:
        save(out, 'startup-failure.json', dict(no_child_command_started=True,
             reason='Python must be 3.11+ and selected native digest must match',
             actual_native_sha256=native_before))
        return 1
    try:
        prior_metadata = separately_performed_metadata()
        root_packets = completed_root_packets()
    except (OSError, ValueError, KeyError, TypeError) as error:
        save(out, 'startup-failure.json', dict(no_child_command_started=True,
             reason='Separate current metadata or terminal root packet binding failed',
             error=repr(error)))
        return 1
    save(out, 'separate-metadata-checks.json', prior_metadata)
    save(out, 'separate-root-packets.json', root_packets)
    records = [run(out, '00.mdbook-version', [str(MDBOOK), '--version'])]
    pinned = records[0]['exit_code'] == 0 and (out / '00.mdbook-version.stdout.txt').read_text().strip() == 'mdbook v0.5.4'
    rendered = None
    if pinned:
        # Only this small owned output tree is removed; failure logs survive.
        with tempfile.TemporaryDirectory(prefix='qleisli-parameter-policy-book-', dir='/private/tmp') as temp:
            book = Path(temp) / 'book'
            build = run(out, '01.mdbook-build', [str(MDBOOK), 'build', 'docs', '--dest-dir', str(book)])
            records.append(build)
            if build['exit_code'] == 0:
                records.append(run(out, '02.rendered-book', [sys.executable, 'scripts/check_book.py', '--root', str(book)]))
            generated = {str(p.relative_to(book)): dict(sha256=sha(p), bytes=p.stat().st_size)
                         for p in sorted(book.rglob('*')) if p.is_file()}
            rendered = dict(files=generated, total_bytes=sum(row['bytes'] for row in generated.values()),
                            output_root=str(book), temporary_output_cleaned_after_check=True,
                            limit='Generated HTML/assets and local links/anchors only; external URLs are not fetched.')
            save(out, 'rendered-files.json', rendered)
    # All invocations below are explicitly authored; neither inventory nor a
    # historical command record is used to construct an executable command.
    commands = (
        ('03.book-regression', [sys.executable, 'scripts/test_check_book.py']),
        ('04.authoring', [sys.executable, 'scripts/check_authoring_sessions.py']),
        ('05.authoring-regression', [sys.executable, 'scripts/test_check_authoring_sessions.py']),
        ('06.editions', [sys.executable, 'scripts/check_editions.py']),
        ('07.edition-regression', [sys.executable, 'scripts/test_check_editions.py']),
        ('08.docs', [sys.executable, 'scripts/check_docs.py']),
        ('09.docs-regression', [sys.executable, 'scripts/test_check_docs.py']),
        ('10.constitution', [sys.executable, 'scripts/check_constitution.py', '--base-ref', BASE]),
        ('11.inventory', [sys.executable, 'scripts/check_verification_inventory.py']),
        ('12.coverage', [sys.executable, 'scripts/check_production_coverage.py']),
    )
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        records.extend(pool.map(lambda item: run(out, *item), commands))
    after = inputs()
    changes = {name: dict(before=before.get(name), after=after.get(name))
               for name in before.keys() | after.keys() if before.get(name) != after.get(name)}
    book_after, native_after, cli_after = sha(MDBOOK), sha(NATIVE), sha(CLI)
    save(out, 'identity.after.json', dict(files=after, mismatches=changes,
         mdbook_sha256=book_after, native_sha256=native_after, cli_sha256=cli_after, selected_input_count=len(after)))
    save(out, 'commands.json', dict(commands=records, recorded_commands_executed=False,
                                  fixed_driver_sha256=sha(Path(__file__))))
    counts = {}
    for record in records:
        match = re.search(r'Ran (\d+) tests in ', (out / record['stderr']['path']).read_text())
        if match:
            counts[record['id']] = int(match[1])
    passed = pinned and len(records) == 13 and counts == EXPECTED_REGRESSIONS and not changes and book_after == book_before and native_after == native_before and cli_after == cli_before and all(
        record['exit_code'] == 0 and not record['launch_error'] and not record['timed_out'] for record in records)
    result = dict(status='ordinary-policy-and-docs-checks-passed' if passed else 'checks-incomplete-or-failed',
                  selected_input_count=len(before), source_mismatches=changes,
                  pinned_mdbook_verified=pinned, actual_command_count=len(records),
                  regression_test_counts=counts, actual_regression_test_total=sum(counts.values()), separate_metadata_checks=prior_metadata, separate_root_packets=root_packets, rendered_output_bytes=rendered['total_bytes'] if rendered else None,
                  parameter_scope='Private common parameter spelling claims and iterative original runtime-name scan only; kind/type/premise/access/bind/body policies retain their profile stages.',
                  metadata_scope='Root-reviewed actual source/surface refresh only; route/proof criteria and statuses are not widened.',
                  constitutional_mode='Current source/evidence identity with trusted-base continuity; no fresh Lean replay',
                  not_run=['Inventory/coverage mutation suites (root already performed; retained separately)', 'Rust builds/tests (root runs separate validation/driver.py)', 'Lean build/audit/replay',
                           'constitutional mutation suite (unchanged checker)', 'full CI or release-readiness validation'],
                  no_claim=['complete common checker', 'source preservation', 'new guarantee admission', 'proof closure',
                            'canonical generic QFT availability', 'Issue closure', 'release approval'],
                  raw_failures_preserved=True, original_or_previous_records_modified=False)
    save(out, 'results.json', result)
    manifest = {p.name: dict(sha256=sha(p), bytes=p.stat().st_size) for p in sorted(out.iterdir()) if p.is_file()}
    save(out, 'files.json', dict(files=manifest, self_excluded='files.json'))
    print(json.dumps(result, indent=2), flush=True)
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
