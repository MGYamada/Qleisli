#!/usr/bin/env python3
"""Fixed pattern-unit policy checks v2; separate metadata regressions are not rerun.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import concurrent.futures
import datetime
import hashlib
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
METADATA_REVIEW = ROOT / 'tests/fixtures/frontend_v030/common-pattern-design/metadata-review'
METADATA_REFERENCE = HERE / 'metadata-reference-v2.json'
METADATA_REFERENCE_SHA256 = '41312b8982e4bb131e5a1ee2c3d60b3cc412d9e6d2f06f3845713635bfc79865'
METADATA_RECORD_FILES = ('after.coverage-regression.stderr.txt', 'after.coverage-regression.stdout.txt', 'after.coverage.stderr.txt', 'after.coverage.stdout.txt', 'after.inventory-regression.stderr.txt', 'after.inventory-regression.stdout.txt', 'after.inventory.stderr.txt', 'after.inventory.stdout.txt', 'before.coverage.stderr.txt', 'before.coverage.stdout.txt', 'before.inventory.stderr.txt', 'before.inventory.stdout.txt', 'commands.after.json', 'commands.before.json', 'coverage.after.json', 'coverage.before.json', 'driver.py', 'files.json', 'inventory.after.json', 'inventory.before.json', 'metadata-changes.json', 'results.json', 'source-inputs.before.json')
NATIVE = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
NATIVE_SHA256 = '39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85'
CHANGED_PATHS = (
    'src/frontend/pattern.rs', 'src/frontend/mod.rs',
    'src/frontend/compile/lower/mod.rs', 'src/frontend/sized/ast.rs',
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
    paths += [Path(__file__), HERE / 'README-v2.md', METADATA_REFERENCE]
    paths += [HERE / name for name in ('driver.py', 'README.md', 'prepared-files.json')]
    paths += [METADATA_REVIEW / name for name in METADATA_RECORD_FILES]
    # Paths are used only as byte-identity data, never as executable argv.
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
        'tests/fixtures/frontend_v030/common-pattern-design/contract-v2.md',
        'tests/fixtures/frontend_v030/common-pattern-design/revision-v2.json',
        'tests/fixtures/frontend_v030/common-pattern-design/validation/driver.py',
        'tests/fixtures/frontend_v030/common-pattern-design/validation/selection.json',
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
    """Read and bind earlier fixed results; never execute their recorded argv."""
    if sha(METADATA_REFERENCE) != METADATA_REFERENCE_SHA256:
        raise ValueError('Prepared metadata reference changed')
    reference = json.loads(METADATA_REFERENCE.read_text())
    if set(reference['record_file_hashes']) != set(METADATA_RECORD_FILES):
        raise ValueError('Metadata record file set changed')
    for name in METADATA_RECORD_FILES:
        if sha(METADATA_REVIEW / name) != reference['record_file_hashes'][name]:
            raise ValueError('Retained metadata record changed: ' + name)
    for name, digest in reference['earlier_draft_hashes'].items():
        if sha(HERE / name) != digest:
            raise ValueError('Historical prepared v1 changed: ' + name)
    reviewed = json.loads((METADATA_REVIEW / 'source-inputs.before.json').read_text())['files']
    if len(reviewed) != reference['source_file_count']:
        raise ValueError('Reviewed source count changed')
    for name, digest in reviewed.items():
        if sha(ROOT / name) != digest:
            raise ValueError('Source changed after metadata review: ' + name)
    active = (
        ('tests/fixtures/verification_v022/inventory.json', 'active_inventory_sha256'),
        ('tests/fixtures/verification_v029/coverage.json', 'active_coverage_sha256'),
    )
    for name, key in active:
        if sha(ROOT / name) != reference[key]:
            raise ValueError('Active metadata differs from reviewed after copy: ' + name)
    result = json.loads((METADATA_REVIEW / 'results.json').read_text())
    if (result['status'] != 'passed' or not result['source_inputs_unchanged'] or
            len(result['actual_checks']) != 4 or
            any(row['exit_code'] != 0 for row in result['actual_checks'])):
        raise ValueError('Earlier metadata guard/regression results are incomplete')
    for kind, expected in (('inventory', 17), ('coverage', 14)):
        stderr = (METADATA_REVIEW / ('after.' + kind + '-regression.stderr.txt')).read_text()
        match = re.search(r'Ran (\d+) tests in ', stderr)
        if not match or int(match[1]) != expected or not stderr.rstrip().endswith('OK'):
            raise ValueError('Earlier raw regression result differs: ' + kind)
    return dict(status='separate-root-results-read-and-byte-bound',
                root_record=reference['root_review_record'],
                root_record_time_utc=reference['root_record_time_utc'],
                reference_sha256=METADATA_REFERENCE_SHA256,
                source_file_count=len(reviewed),
                actual_regression_counts=reference['actual_regression_counts'],
                rerun_by_this_driver=False, recorded_commands_executed=False,
                identity_limits=reference['identity_limits'])


def main():
    if len(sys.argv) != 2 or not re.fullmatch(r'attempt-[0-9]{2}', sys.argv[1]):
        raise SystemExit('usage: driver-v2.py attempt-NN; root runs after source/metadata/Reference barrier')
    out = HERE / sys.argv[1]
    out.mkdir(exist_ok=False)
    before = inputs()
    book_before, native_before = sha(MDBOOK), sha(NATIVE)
    save(out, 'identity.before.json', dict(status='selected-policy-input-byte-identities',
         observed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), files=before,
         changed_paths={name: before[name] for name in CHANGED_PATHS},
         mdbook_path=str(MDBOOK), mdbook_sha256=book_before,
         native_path=str(NATIVE), native_sha256=native_before,
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
    except (OSError, ValueError, KeyError, TypeError) as error:
        save(out, 'startup-failure.json', dict(no_child_command_started=True,
             reason='Separate metadata record/current source binding failed',
             error=repr(error)))
        return 1
    save(out, 'separate-metadata-checks.json', prior_metadata)
    records = [run(out, '00.mdbook-version', [str(MDBOOK), '--version'])]
    pinned = records[0]['exit_code'] == 0 and (out / '00.mdbook-version.stdout.txt').read_text().strip() == 'mdbook v0.5.4'
    rendered = None
    if pinned:
        # Only this small owned output tree is removed; failure logs survive.
        with tempfile.TemporaryDirectory(prefix='qleisli-pattern-policy-book-', dir='/private/tmp') as temp:
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
    book_after, native_after = sha(MDBOOK), sha(NATIVE)
    save(out, 'identity.after.json', dict(files=after, mismatches=changes,
         mdbook_sha256=book_after, native_sha256=native_after, selected_input_count=len(after)))
    save(out, 'commands.json', dict(commands=records, recorded_commands_executed=False,
                                  fixed_driver_sha256=sha(Path(__file__))))
    counts = {}
    for record in records:
        match = re.search(r'Ran (\d+) tests in ', (out / record['stderr']['path']).read_text())
        if match:
            counts[record['id']] = int(match[1])
    passed = pinned and len(records) == 13 and not changes and book_after == book_before and native_after == native_before and all(
        record['exit_code'] == 0 and not record['launch_error'] and not record['timed_out'] for record in records)
    result = dict(status='ordinary-policy-and-docs-checks-passed' if passed else 'checks-incomplete-or-failed',
                  selected_input_count=len(before), source_mismatches=changes,
                  pinned_mdbook_verified=pinned, actual_command_count=len(records),
                  regression_test_counts=counts, separate_metadata_checks=prior_metadata, rendered_output_bytes=rendered['total_bytes'] if rendered else None,
                  pattern_scope='Private shared runtime pattern-binding judgment only; sized elaboration and coherent basis binder remain separate.',
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
