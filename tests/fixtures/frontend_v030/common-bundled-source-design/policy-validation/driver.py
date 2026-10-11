#!/usr/bin/env python3
"""Fixed ordinary documentation/policy checks; never execute record commands.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import concurrent.futures
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
ROOT = Path('/Users/masa/git/Qleisli')
DEST = Path(__file__).resolve().parent
MDBOOK = Path('/private/tmp/qleisli-mdbook-0.5.4-bin/mdbook')
BASE = 'faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2'
RECORDS = []


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(name, value):
    with (DEST / name).open('x', encoding='utf-8') as out:
        json.dump(value, out, indent=2)
        out.write('\n')


def run(name, argv):
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    begin = time.monotonic()
    result = subprocess.run(argv, cwd=ROOT, capture_output=True,
                            check=False, timeout=180)
    for suffix, output in [('stdout.txt', result.stdout), ('stderr.txt', result.stderr)]:
        with (DEST / (name + '.' + suffix)).open('xb') as out:
            out.write(output)
    record = dict(id=name, argv=argv, cwd=str(ROOT), started_at_utc=started,
                  elapsed_seconds=time.monotonic()-begin, exit_code=result.returncode,
                  stdout=name+'.stdout.txt', stderr=name+'.stderr.txt')
    print(f'{name}: exit {result.returncode}', flush=True)
    return record


def main():
    # Selection is fixed here, never read from commands/results metadata.
    inventory = json.loads((ROOT / 'tests/fixtures/verification_v022/inventory.json').read_text())
    inputs = {row['path'] for row in inventory['sources']}
    inputs.update(str(path.relative_to(ROOT)) for path in (ROOT / 'docs').rglob('*')
                  if path.is_file() and not path.is_symlink())
    inputs.update(str(path.relative_to(ROOT)) for path in (ROOT / 'governance').rglob('*')
                  if path.is_file() and not path.is_symlink())
    inputs.update(str(path.relative_to(ROOT)) for path in
                  (ROOT / 'tests/fixtures/authoring_sessions').glob('*/session.json'))
    inputs.update([
        'AGENTS.md', 'CLAUDE.md', 'README.md', 'ROADMAP.md', 'TRUSTBOUNDARY.md',
        'CONSTITUTION.md', 'GOVERNANCE.md', 'CHANGELOG.md', 'Cargo.toml', 'Cargo.lock',
        'stdlib/Qargo.toml', '.github/workflows/ci.yml', '.github/ci/README.md',
        'scripts/check_book.py', 'scripts/test_check_book.py',
        'scripts/check_docs.py', 'scripts/test_check_docs.py',
        'scripts/check_editions.py', 'scripts/test_check_editions.py',
        'scripts/check_authoring_sessions.py', 'scripts/test_check_authoring_sessions.py',
        'scripts/check_constitution.py', 'scripts/check_lean_kernel.py',
        'scripts/check_verification_inventory.py', 'scripts/check_production_coverage.py',
        'tests/fixtures/verification_v022/inventory.json',
        'tests/fixtures/verification_v029/coverage.json',
    ])
    before = {name: sha(ROOT / name) for name in sorted(inputs)}
    save('identity.before.json', dict(status='selected-policy-input-byte-identities',
         observed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
         files=before, mdbook_path=str(MDBOOK), mdbook_sha256=sha(MDBOOK),
         identity_limit='Selected input identity is not proof, full CI or authentication.'))
    version = run('00.mdbook-version', [str(MDBOOK), '--version'])
    RECORDS.append(version)
    pinned = (version['exit_code'] == 0 and
              (DEST / version['stdout']).read_text().strip() == 'mdbook v0.5.4')
    rendered = None
    if pinned:
        # Build outputs are small and temporary; retain their byte identities,
        # actual build/check logs and counts, then clean only this owned tempdir.
        with tempfile.TemporaryDirectory(prefix='qleisli-common-source-book-',
                                         dir='/private/tmp') as temp:
            book = Path(temp) / 'book'
            build = run('01.mdbook-build', [str(MDBOOK), 'build', 'docs', '--dest-dir', str(book)])
            RECORDS.append(build)
            if build['exit_code'] == 0:
                links = run('02.rendered-book', [sys.executable, 'scripts/check_book.py',
                                                '--root', str(book)])
                RECORDS.append(links)
                files = {str(path.relative_to(book)): dict(sha256=sha(path), bytes=path.stat().st_size)
                         for path in sorted(book.rglob('*')) if path.is_file()}
                rendered = dict(files=files, total_bytes=sum(row['bytes'] for row in files.values()),
                                output_root=str(book), temporary_output_cleaned_after_check=True,
                                limit='HTML/assets/local href/src and anchors only; external URLs not fetched.')
                save('rendered-files.json', rendered)
    commands = [
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
    ]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        RECORDS.extend(pool.map(lambda item: run(*item), commands))
    after = {name: sha(ROOT / name) for name in before}
    changes = {name: dict(before=digest, after=after[name])
               for name, digest in before.items() if after[name] != digest}
    save('identity.after.json', dict(files=after, mismatches=changes,
         mdbook_sha256=sha(MDBOOK), selected_input_count=len(before)))
    save('commands.json', dict(commands=RECORDS, recorded_commands_executed=False,
         fixed_driver_sha256=sha(Path(__file__))))
    counts = {}
    for record in RECORDS:
        stderr = (DEST / record['stderr']).read_text()
        match = re.search(r'Ran (\d+) tests in ', stderr)
        if match:
            counts[record['id']] = int(match[1])
    passed = pinned and rendered is not None and not changes and all(
        record['exit_code'] == 0 for record in RECORDS)
    result = dict(status='ordinary-policy-and-docs-checks-passed' if passed else 'checks-incomplete-or-failed',
                  selected_input_count=len(before), source_mismatches=changes,
                  pinned_mdbook_verified=pinned, actual_command_count=len(RECORDS),
                  regression_test_counts=counts, rendered_output_bytes=rendered['total_bytes'] if rendered else None,
                  native_acceptance_authority='unchanged Lean-only',
                  constitutional_mode='current source/evidence identity with trusted-base continuity; no fresh Lean replay',
                  not_run=['Cargo/Rust builds or tests', 'Lean build/audit/replay',
                           'constitutional mutation suite (unchanged checker; prior results not rerun)',
                           'inventory/coverage mutation suites (already run for same metadata inputs)',
                           'full CI or release-readiness validation'],
                  no_claim=['new guarantee admission', 'proof closure', 'complete common checker',
                            'canonical generic QFT availability', 'Issue closure', 'release approval'],
                  raw_failures_preserved=True, original_or_previous_records_modified=False)
    save('results.json', result)
    manifest = {path.name: dict(sha256=sha(path), bytes=path.stat().st_size)
                for path in sorted(DEST.iterdir()) if path.is_file()}
    save('files.json', dict(files=manifest, self_excluded='files.json'))
    print(json.dumps(result, indent=2), flush=True)
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
