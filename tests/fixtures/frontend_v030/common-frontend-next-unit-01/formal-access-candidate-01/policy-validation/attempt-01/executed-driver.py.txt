#!/usr/bin/env python3
"""Fixed Formals policy checks; root freezes inputs only after terminal barriers.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import concurrent.futures
import datetime
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path('/Users/masa/git/Qleisli')
HERE = Path(__file__).resolve().parent
UNIT = HERE.parent
STUDY = ROOT / 'tests/fixtures/authoring_sessions/common-formal-access-v030'
VALIDATION = UNIT / 'validation'
METADATA = UNIT / 'metadata-review/attempt-01'
HELPER = ROOT / 'tests/fixtures/frontend_v030/common-parameter-declaration-design/policy-validation/driver.py'
HELPER_SHA = '5ea1858791b3dd58857ef568b3bacb64cd1d8494bc28869d60d83b9be383a9a2'
SOURCE_MAP_SHA = '2ef1440d8b50a22979afde96c24d6adc162e5e500486eacfbd632ccdebd54cef'
FIRST_SHA = '140bc0e555d23460d6f8c523627c8cba643ca3ddc2aaa3d95533e06234a2e454'
MDBOOK = Path('/private/tmp/qleisli-mdbook-0.5.4-bin/mdbook')
NATIVE = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
NATIVE_SHA = '39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85'
CLI = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
BASE = 'faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2'
FROZEN = HERE / 'reviewed-inputs.json'
AFTER = STUDY / 'after-attempt-01'
AFTER_DESIGN = STUDY / 'after-design-01'
AFTER_DRIVER_SHA = 'ecd3c6c89b7b00ca9683eede78ae936c25d7a0be919a4602acd0bcf5e3571296'
AFTER_INPUTS_SHA = '87c408960956464f8cbbd6c48a626da3642ecc37aabf58fcdd8ea4022a0fbac5'
AFTER_SUMMARY_SHA = '41ccc86663b8d11065fb011a03e6cba843979f275a9f392209c2a414acc5ff99'
AFTER_RECEIPT_SHA = 'e218f0e9ced5bb7aef5daf51937e780845440bd82f4e7696dcc2d1f6d9edf7bd'
AFTER_CLI_SHA = '2209c0528e4f25dc46498bbbe8cc3ca3df31201e0fa7bed41130bff593e233c9'
MSRV_CLI_SHA = 'd219e3cb0e546c8173ab1215ffd94cacc7c032ce9abd145b98949bbb2c4d089e'
CASES = ('valid-operation', 'valid-dependent-basis', 'forward-natural', 'forward-basis',
         'duplicate-access', 'wrong-kind-access', 'static-runtime-collision',
         'unused-missing-access', 'natural-priority', 'basis-scan-priority')
FORMS = (('finite', 'text'), ('finite', 'json'),
         ('selected-auto', 'text'), ('selected-auto', 'json'))
PRODUCTION = {
    'src/frontend/formals.rs': '39d64fe7c6090de81b2afa1b6e6b8b8454151b9514138dbba93eed5e3dff322d',
    'src/frontend/mod.rs': '5aa13633507fbc405a126b432f13bc62f480e8c7784e50f0a94beb1f58bbf7df',
    'src/frontend/compile/operations.rs': '9e77a9745cf166a055c4fec5b009d46132dda460751042919f38af84f03fe23a',
    'src/frontend/sized/check.rs': '1099273ca442b33e67c99fc33efc73aaecef448b222c656455b931d0dbaeeb17',
    'src/frontend/sized/linear.rs': 'c9840b426f33976824c0f9a20fefb4f7e84bb23cca9e58e5aa3c4d53580a0979',
    'src/frontend/sized/ast.rs': 'a8b31ab0f612fc7513ae62103ae050874f64b591d0c3af0b99c0747554ac7fe1',
    'src/frontend/sized/parser.rs': 'cb028400f3dfcb698e3682a2ebb3937c1774fdf1a2fc36fe09362b401c99aee0',
}
EXPECTED_REGRESSIONS = {
    '03.book-regression': 12, '05.authoring-regression': 7,
    '07.edition-regression': 11, '09.docs-regression': 36,
}


def helpers():
    if hashlib.sha256(HELPER.read_bytes()).hexdigest() != HELPER_SHA:
        raise ValueError('Reviewed helper driver changed')
    spec = importlib.util.spec_from_file_location('reviewed_formal_policy_helpers', HELPER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.sha, module.save, module.run


def load(path):
    return json.loads(path.read_text())


def relative_file(base, name):
    """Data-only identity paths cannot escape their recorded packet/root."""
    p = Path(name)
    if p.is_absolute() or '..' in p.parts:
        raise ValueError('Non-relative identity path: ' + name)
    resolved = (base / p).resolve(strict=True)
    if not resolved.is_relative_to(base.resolve()) or not resolved.is_file():
        raise ValueError('Identity path escapes packet/root: ' + name)
    return resolved


def mapped_files(base, rows, sha):
    for name, row in rows.items():
        digest = row['sha256'] if isinstance(row, dict) else row
        p = relative_file(base, name)
        if sha(p) != digest:
            raise ValueError('Recorded bytes changed: ' + str(p))
        if isinstance(row, dict) and 'bytes' in row and p.stat().st_size != row['bytes']:
            raise ValueError('Recorded byte count changed: ' + str(p))
        if isinstance(row, dict) and 'mode' in row and (p.stat().st_mode & 0o777) != row['mode']:
            raise ValueError('Recorded mode changed: ' + str(p))


def reviewed_sources(sha):
    p = METADATA / 'all-source-bindings.after.json'
    if sha(p) != SOURCE_MAP_SHA:
        raise ValueError('Reviewed 254-source binding map changed')
    d = load(p)
    if d['count'] != 254 or len(d['files']) != 254:
        raise ValueError('Reviewed source count changed')
    mapped_files(ROOT, d['files'], sha)
    for name, digest in PRODUCTION.items():
        if d['files'].get(name) != digest or sha(ROOT / name) != digest:
            raise ValueError('Frozen production path changed: ' + name)
    inv = load(ROOT / 'tests/fixtures/verification_v022/inventory.json')
    if len(inv['sources']) != 254 or {r['path']: r['sha256'] for r in inv['sources']} != d['files']:
        raise ValueError('Active inventory does not match reviewed 254 sources')
    result = load(METADATA / 'results.json')
    if (result['status'] != 'passed' or result['source_count'] != 254 or
            set(result['source_hash_changes']) != set(PRODUCTION) - {'src/frontend/formals.rs'} or
            result['private_source_added'] != 'src/frontend/formals.rs' or
            not result['other_inventory_fields_unchanged'] or
            result['coverage_changed_fields'] != ['surface_sha256'] or
            [r['exit_code'] for r in result['commands']] != [1, 0, 0, 0, 0]):
        raise ValueError('Current metadata review is incomplete or changed')
    for r in result['commands']:
        for kind in ('stdout', 'stderr'):
            p = relative_file(METADATA, r[kind]['path'])
            if sha(p) != r[kind]['sha256']:
                raise ValueError('Current metadata raw log changed: ' + str(p))
    for name, capture in (
            ('tests/fixtures/verification_v022/inventory.json', 'inventory.after.json.gz'),
            ('tests/fixtures/verification_v029/coverage.json', 'coverage.after.json.gz')):
        if (ROOT / name).read_bytes() != gzip.decompress((METADATA / capture).read_bytes()):
            raise ValueError('Active metadata differs from reviewed after bytes: ' + name)
    return d['files'], {'record': str((METADATA / 'results.json').relative_to(ROOT)),
                       'record_sha256': sha(METADATA / 'results.json'),
                       'source_count': 254,
                       'actual_guard_exits': [1, 0, 0, 0, 0],
                       'commands_executed_by_policy': False}


def terminal_rust(sha):
    records = {}
    for mode, directory in (('latest', VALIDATION / 'latest-attempt-02'),
                            ('msrv', VALIDATION / 'msrv-attempt-01')):
        d = load(directory / 'results.json')
        if (d['status'] != 'passed' or d['mode'] != mode or
                d['remaining_stages_not_run'] != 0 or len(d['records']) != 8 or
                not d['source_inputs_unchanged'] or not d['cli_rebuild_completed']):
            raise ValueError('Root Rust validation is not terminal success: ' + mode)
        tests = []
        for row in d['records']:
            if (row['exit_code'] != 0 or row['launch_error'] or row['timed_out'] or
                    row['postcondition_error'] or not row['identities_unchanged']):
                raise ValueError('Root Rust stage is incomplete/failed: ' + mode)
            for kind in ('stdout', 'stderr'):
                p = relative_file(directory, row[kind]['path'])
                if sha(p) != row[kind]['sha256'] or p.stat().st_size != row[kind]['bytes']:
                    raise ValueError('Root Rust raw log changed: ' + str(p))
            tests += row['actual_test_results']
        if not tests or any(t['status'] != 'ok' or t['failed'] != 0 for t in tests):
            raise ValueError('Root bounded Rust tests are incomplete: ' + mode)
        counts = {k: sum(t[k] for t in tests) for k in ('passed', 'failed', 'ignored')}
        if counts != {'passed': 147, 'failed': 0, 'ignored': 3}:
            raise ValueError('Recorded bounded Rust totals differ: ' + mode)
        source = load(directory / 'inputs-after.json')['files']
        for name in (*PRODUCTION, 'tests/sized_declarations.rs'):
            if sha(ROOT / name) != source[name]:
                raise ValueError('Source/test differs from root Rust validation: ' + name)
        records[mode] = {'record': str((directory / 'results.json').relative_to(ROOT)),
                         'record_sha256': sha(directory / 'results.json'),
                         'stages': 8, 'cli_sha256': d['cli_sha256_after'],
                         'actual_test_counts': counts}
    if (records['latest']['cli_sha256'] != AFTER_CLI_SHA or
            records['msrv']['cli_sha256'] != MSRV_CLI_SHA or
            sha(CLI) != records['msrv']['cli_sha256']):
        raise ValueError('Current selected CLI differs from completed MSRV rebuild')
    return records


def terminal_after(sha):
    if (sha(AFTER_DESIGN / 'observe-after.py') != AFTER_DRIVER_SHA or
            sha(AFTER_DESIGN / 'inputs.json') != AFTER_INPUTS_SHA):
        raise ValueError('Frozen after collector/input bytes changed')
    design = load(AFTER_DESIGN / 'inputs.json')
    if (design['first_file_count'] != 46 or design['first_files_sha256'] != FIRST_SHA or
            len(design['before_inventory']) != 203):
        raise ValueError('Frozen original FIRST/before binding changed')
    mapped_files(ROOT, {r['path']: r for r in design['frozen_files']}, sha)
    if sorted(p.name for p in (STUDY / 'before').iterdir()) != design['before_inventory']:
        raise ValueError('Original before packet member set changed')
    receipt_path = STUDY / 'terminal-after-attempt-01.json'
    if sha(receipt_path) != AFTER_RECEIPT_SHA or sha(AFTER / 'summary.json') != AFTER_SUMMARY_SHA:
        raise ValueError('Actual after summary/terminal receipt changed')
    receipt = load(receipt_path)
    if (receipt['exit_code'] != 0 or receipt['session_id'] != 28584 or
            receipt['result_path'] != str((AFTER / 'summary.json').relative_to(ROOT))):
        raise ValueError('Root after terminal observation is not the reviewed successful capture')
    before = load(AFTER / 'identity.before.json')
    final = load(AFTER / 'identity.final.json')
    summary = load(AFTER / 'summary.json')
    if (summary['status'] != 'all_equal' or summary['actual_observation_count'] != 40 or
            len(summary['comparisons']) != 40 or summary['native_forwarded_attempts'] != 46 or
            summary['output_normalizations'] != 0 or summary['source_repairs'] != 0 or
            summary['recorded_commands_executed'] or summary['source_meaning_verified'] or
            not summary['original_before_packet_unchanged'] or
            not final['selected_inputs_unchanged'] or not final['original_before_packet_unchanged'] or
            before['identity'] != final['identity'] or
            before['identity'] != design['current_identity'] or
            final['identity']['cli_sha256'] != AFTER_CLI_SHA or
            final['identity']['native_sha256'] != NATIVE_SHA or
            before['first_files_sha256'] != FIRST_SHA or
            before['inputs_sha256'] != AFTER_INPUTS_SHA or before['frozen_before_file_count'] != 203):
        raise ValueError('Actual forty-after comparison is incomplete or differs')
    equal_keys = ('command_equal', 'exit_equal', 'stdout_raw_equal', 'stderr_raw_equal',
                  'native_argv_raw_equal', 'native_count_equal')
    if not all(row[k] for row in summary['comparisons'] for k in equal_keys):
        raise ValueError('Actual after raw comparison is not all equal')
    original = load(STUDY / 'before/summary.json')
    expected_order = [(case, profile, presentation) for case in CASES
                      for profile, presentation in FORMS]
    if (original['actual_observation_count'] != 40 or original['native_forwarded_attempts'] != 46 or
            [(r['case'], r['profile'], r['presentation']) for r in original['rows']] !=
            expected_order or [(r['case'], r['profile'], r['presentation'])
                               for r in summary['comparisons']] != expected_order):
        raise ValueError('Actual before/after case order differs')
    file_record = load(AFTER / 'files.json')
    if file_record['self_excluded'] != 'files.json':
        raise ValueError('After file map has a different self exclusion')
    file_map = file_record['files']
    mapped_files(AFTER, file_map, sha)
    if set(file_map) | {'files.json'} != {p.name for p in AFTER.iterdir()}:
        raise ValueError('Actual after terminal packet member set changed')
    for name, digest in PRODUCTION.items():
        if final['identity']['files'][name]['sha256'] != digest or sha(ROOT / name) != digest:
            raise ValueError('Source differs from actual after producer: ' + name)
    total_native = successes = 0
    wrapper = ROOT / 'tests/fixtures/authoring_sessions/common-parameter-declaration-v030/native-log.py'
    for row, original_row in zip(summary['comparisons'], original['rows']):
        p = relative_file(STUDY, row['observation'])
        if p.parent != AFTER:
            raise ValueError('Observation is outside fixed after packet')
        event = load(p)
        old_path = relative_file(STUDY, original_row['observation'])
        if old_path.parent != STUDY / 'before':
            raise ValueError('Observation is outside fixed before packet')
        old = load(old_path)
        project = STUDY / 'attempt-01' / row['case']
        if row['profile'] == 'finite':
            expected_argv = [str(CLI), 'check', str(project)]
        else:
            expected_argv = [str(CLI), 'check', '--entry=main::main',
                             '--module=main=' + str(project / 'main.qli'), '--ir-profile=auto']
        expected_argv.append('--lean-kernel=' + str(wrapper))
        if row['presentation'] == 'json':
            expected_argv.append('--format=json')
        # This authored argv is compared as data; it is never executed here.
        if event['command'] != old['command'] or event['command'] != expected_argv:
            raise ValueError('Actual before/after command bytes differ')
        if (event['exit_code'] != row['actual_exit_code'] or
                event['exit_code'] != old['exit_code'] or
                old['exit_code'] != original_row['exit_code'] or event['exit_code'] not in (0, 1)):
            raise ValueError('Actual before/after status differs')
        for observed in (event, old):
            cap = observed['client_capture']
            if (not cap['spawned'] or cap['reason'] is not None or cap['error'] is not None or
                    cap['stdout_limited'] or cap['stderr_limited'] or
                    cap['returncode'] != observed['exit_code'] or cap['stdin_written'] != 0):
                raise ValueError('Actual observation has operational uncertainty')
        for key, digest_key in (('stdout_raw', 'stdout_sha256'), ('stderr_raw', 'stderr_sha256'),
                                ('native_argv_log', 'native_journal_sha256')):
            raw = relative_file(AFTER, event[key])
            old_raw = relative_file(STUDY / 'before', old[key])
            if (sha(raw) != event[digest_key] or sha(old_raw) != old[digest_key] or
                    raw.read_bytes() != old_raw.read_bytes()):
                raise ValueError('Actual raw before/after logs changed or differ: ' + str(raw))
        journal = relative_file(AFTER, event['native_argv_log']).read_bytes().splitlines()
        if (len(journal) != event['native_forwarded_attempts'] or
                len(journal) != row['native_forwarded_attempts'] or
                len(journal) != old['native_forwarded_attempts'] or
                len(journal) != original_row['native_forwarded_attempts']):
            raise ValueError('After pre-execv journal count differs')
        total_native += len(journal)
        successes += event['exit_code'] == 0
    if total_native != 46 or successes != 6:
        raise ValueError('Actual before/after aggregate counts differ')
    return {'summary': str((AFTER / 'summary.json').relative_to(ROOT)),
            'summary_sha256': sha(AFTER / 'summary.json'), 'files_sha256': sha(AFTER / 'files.json'),
            'terminal_receipt_sha256': sha(receipt_path),
            'actual_observations': 40, 'successes': successes, 'refusals': 40 - successes,
            'pre_execv_forwarded_attempts': total_native,
            'output_normalizations': 0, 'cli_sha256': final['identity']['cli_sha256'],
            'native_count_limit': 'Actual pre-execv forwarder rows, not independent native starts/exits.',
            'scope': 'Same bounded raw check observations; source preservation remains unproved.'}


def prerequisites(sha):
    if sys.version_info < (3, 11) or sha(NATIVE) != NATIVE_SHA:
        raise ValueError('Python 3.11+ and the fixed selected native bytes are required')
    if sha(STUDY / 'first-files.json') != FIRST_SHA:
        raise ValueError('Historical FIRST map changed')
    first = load(STUDY / 'first-files.json')
    if len(first['files']) != 46:
        raise ValueError('Historical FIRST count changed')
    mapped_files(ROOT, {r['path']: r for r in first['files']}, sha)
    sources, metadata = reviewed_sources(sha)
    after = terminal_after(sha)
    rust = terminal_rust(sha)
    return sources, {'metadata': metadata, 'root_after': after, 'root_rust': rust,
                     'scope': 'Separately performed root records; no stored command executed.'}


def input_files(sources, sha):
    paths = {ROOT / name for name in sources}
    for directory, pattern in ((ROOT / 'src', '*.rs'), (ROOT / 'docs', '*'),
                               (ROOT / 'governance', '*'), (ROOT / 'scripts', '*.py'),
                               (ROOT / '.github', '*'), (STUDY, '*'),
                               (UNIT, '*')):
        paths.update(p for p in directory.rglob(pattern)
                     if p.is_file() and not p.is_symlink() and HERE not in p.parents)
    paths.update((ROOT / 'tests').glob('*.rs'))
    paths.update((ROOT / 'tests/fixtures/authoring_sessions').glob('*/session.json'))
    paths.update((UNIT / name) for name in (
        'candidate.md', 'inputs.json', 'phased-contract-01.md', 'phased-contract-01.inputs.json',
        'github-before-code-32.json', 'independent-phased-preparation-review-by-cli-tests.md',
        'independent-phased-preparation-review-by-cli-tests-inputs.json'))
    paths.update(ROOT / name for name in (
        'AGENTS.md', 'CLAUDE.md', 'README.md', 'ROADMAP.md', 'TRUSTBOUNDARY.md',
        'CONSTITUTION.md', 'GOVERNANCE.md', 'CHANGELOG.md', 'Cargo.toml', 'Cargo.lock',
        'docs/book.toml', 'tests/fixtures/authoring_sessions/README.md',
        'tests/fixtures/verification_v022/inventory.json',
        'tests/fixtures/verification_v029/coverage.json'))
    paths.update((Path(__file__), HERE / 'README.md', HELPER))
    paths.add(UNIT / 'results.md')  # Required final root overview, never a prospective result.
    # Never collect our own attempts, reviewed-inputs.json or temporary book output.
    return {str(p.relative_to(ROOT)): {'sha256': sha(p), 'bytes': p.stat().st_size,
                                       'mode': p.stat().st_mode & 0o777}
            for p in sorted(paths)}


def binaries(sha):
    return {str(p): sha(p) for p in (MDBOOK, NATIVE, CLI)}


def freeze_inputs(sha, save):
    sources, separate = prerequisites(sha)
    before = input_files(sources, sha)
    selected = binaries(sha)
    if before != input_files(sources, sha) or selected != binaries(sha):
        raise ValueError('Inputs changed during freeze')
    save(HERE, FROZEN.name, {'format': 'qleisli.formal-policy-reviewed-inputs', 'version': 1,
        'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'status': 'root-frozen-terminal-policy-inputs', 'files': before,
        'selected_binaries': selected, 'separate_root_packets': separate,
        'declared_incomplete_closure': True,
        'excluded': ['policy attempt outputs', 'this input map', 'generated temporary book'],
        'commands_executed': False})
    print('Frozen input map SHA-256: ' + sha(FROZEN), flush=True)
    return 0


def finish(out, save, sha, result):
    save(out, 'results.json', result)
    save(out, 'files.json', {'files': {p.name: {'sha256': sha(p), 'bytes': p.stat().st_size}
                                     for p in sorted(out.iterdir()) if p.is_file()},
                            'self_excluded': 'files.json'})
    print(json.dumps(result, indent=2), flush=True)
    return 0 if result.get('status') == 'ordinary-policy-and-docs-checks-passed' else 1


def execute(attempt, map_sha, sha, save, run):
    out = HERE / attempt
    out.mkdir(exist_ok=False)
    (out / 'executed-driver.py.txt').open('xb').write(Path(__file__).read_bytes())
    try:
        if sha(FROZEN) != map_sha:
            raise ValueError('Caller-reviewed input map hash differs')
        frozen = load(FROZEN)
        sources, separate = prerequisites(sha)
        current, selected = input_files(sources, sha), binaries(sha)
        if current != frozen['files'] or selected != frozen['selected_binaries']:
            raise ValueError('Current inputs/binaries differ from the root-frozen map')
        if separate != frozen['separate_root_packets']:
            raise ValueError('Terminal root packets changed after freeze')
        save(out, 'identity.before.json', {'files': current, 'selected_binaries': selected,
             'reviewed_input_map_sha256': map_sha, 'separate_root_packets': separate,
             'python_executable': sys.executable, 'python_version': sys.version})
    except (OSError, ValueError, KeyError, TypeError) as error:
        return finish(out, save, sha, {'status': 'startup-rejected', 'error': repr(error),
                                       'actual_command_count': 0, 'raw_failures_preserved': True})
    try:
        return perform_checks(out, current, selected, sources, separate, map_sha, sha, save, run)
    except Exception as error:
        completed = sorted(p.name for p in out.glob('*.json')
                           if re.match(r'^[0-9]{2}[.]', p.name))
        return finish(out, save, sha, {
            'status': 'wrapper-aborted', 'error': repr(error),
            'actual_command_count': None, 'completed_command_records': completed,
            'raw_failures_preserved': True,
            'scope': 'Unexpected wrapper failure; retained command records do not assert a complete run.'})


def perform_checks(out, current, selected, sources, separate, map_sha, sha, save, run):
    records = [run(out, '00.mdbook-version', [str(MDBOOK), '--version'])]
    pinned = (records[0]['exit_code'] == 0 and
              (out / '00.mdbook-version.stdout.txt').read_text().strip() == 'mdbook v0.5.4')
    rendered = None
    if pinned:
        with tempfile.TemporaryDirectory(prefix='qleisli-formal-policy-book-', dir='/private/tmp') as temp:
            book = Path(temp) / 'book'
            records.append(run(out, '01.mdbook-build', [str(MDBOOK), 'build', 'docs', '--dest-dir', str(book)]))
            if records[-1]['exit_code'] == 0:
                records.append(run(out, '02.rendered-book',
                                   [sys.executable, 'scripts/check_book.py', '--root', str(book)]))
            generated = {str(p.relative_to(book)): {'sha256': sha(p), 'bytes': p.stat().st_size}
                         for p in sorted(book.rglob('*')) if p.is_file()}
            rendered = {'files': generated, 'total_bytes': sum(r['bytes'] for r in generated.values()),
                        'output_root': str(book), 'cleanup': 'Only this owned temporary tree after hashes/logs are saved',
                        'scope': 'Rendered HTML/assets, local links/anchors; external URLs not fetched.'}
            save(out, 'rendered-files.json', rendered)
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
    after, end_binaries = input_files(sources, sha), binaries(sha)
    changes = {p: {'before': current.get(p), 'after': after.get(p)}
               for p in current.keys() | after.keys() if current.get(p) != after.get(p)}
    save(out, 'identity.after.json', {'files': after, 'mismatches': changes,
                                    'selected_binaries': end_binaries})
    save(out, 'commands.json', {'commands': records, 'recorded_commands_executed': False,
                               'driver_sha256': sha(Path(__file__)), 'helper_sha256': sha(HELPER)})
    counts = {}
    for row in records:
        raw = (out / row['stderr']['path']).read_text()
        match = re.search(r'Ran (\d+) tests in ', raw)
        if match and raw.rstrip().endswith('OK'):
            counts[row['id']] = int(match[1])
    book_counts = None
    if (out / '02.rendered-book.stdout.txt').exists():
        match = re.search(r'rendered book: (\d+) HTML files, (\d+) local links, (\d+) anchors checked',
                          (out / '02.rendered-book.stdout.txt').read_text())
        if match:
            book_counts = dict(zip(('html_files', 'local_links', 'anchors'), map(int, match.groups())))
    passed = (pinned and len(records) == 13 and counts == EXPECTED_REGRESSIONS and
              book_counts is not None and not changes and selected == end_binaries and
              sha(FROZEN) == map_sha and all(r['exit_code'] == 0 and not r['launch_error'] and
                                            not r['timed_out'] for r in records))
    return finish(out, save, sha, {
        'status': 'ordinary-policy-and-docs-checks-passed' if passed else 'checks-incomplete-or-failed',
        'actual_command_count': len(records), 'actual_regression_counts': counts,
        'actual_regression_total': sum(counts.values()), 'actual_rendered_book_counts': book_counts,
        'generated_bytes': rendered['total_bytes'] if rendered else None,
        'selected_input_count': len(current), 'source_mismatches': changes,
        'reviewed_input_map_sha256': map_sha, 'pinned_mdbook_verified': pinned,
        'separate_root_packets': separate, 'raw_failures_preserved': True,
        'scope': 'Private shared checked formals/access and current documentation/policy only.',
        'not_run': ['Rust/Lean builds, tests or native/CLI replay', 'unchanged metadata/constitutional mutation suites',
                    'full CI/release-ready validation'],
        'no_claim': ['complete common checker', 'source/runtime preservation', 'new guarantee/adoption',
                     'general-family proof', 'canonical std/QFT exposure', 'Issue closure', 'release approval']})


def main():
    sha, save, run = helpers()
    if sys.argv[1:] == ['--freeze-inputs']:
        return freeze_inputs(sha, save)
    if (len(sys.argv) == 3 and re.fullmatch(r'attempt-[0-9]{2}', sys.argv[1]) and
            re.fullmatch(r'[a-f0-9]{64}', sys.argv[2])):
        return execute(sys.argv[1], sys.argv[2], sha, save, run)
    raise SystemExit('usage: driver.py --freeze-inputs OR driver.py attempt-NN EXACT_INPUT_MAP_SHA256; root only after final barriers')


if __name__ == '__main__':
    raise SystemExit(main())
