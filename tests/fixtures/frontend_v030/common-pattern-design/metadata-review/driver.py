#!/usr/bin/env python3
"""Review only the fixed pattern-unit inventory changes; no recorded argv execution.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path('/Users/masa/git/Qleisli')
DEST = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts'))
from check_verification_inventory import public_surface
from check_production_coverage import surface_identity

INVENTORY = ROOT / 'tests/fixtures/verification_v022/inventory.json'
COVERAGE = ROOT / 'tests/fixtures/verification_v029/coverage.json'
CHANGED = {
    'src/frontend/mod.rs', 'src/frontend/sized/ast.rs',
    'src/frontend/sized/check.rs', 'src/frontend/compile/lower/mod.rs',
}
NEW = 'src/frontend/pattern.rs'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(name, value):
    with (DEST / name).open('x', encoding='utf-8') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def run(name, argv):
    start = time.monotonic()
    result = subprocess.run(argv, cwd=ROOT, capture_output=True, timeout=120)
    for suffix, raw in [('stdout.txt', result.stdout), ('stderr.txt', result.stderr)]:
        with (DEST / f'{name}.{suffix}').open('xb') as stream:
            stream.write(raw)
    row = dict(argv=argv, exit_code=result.returncode,
               seconds=time.monotonic() - start, stdout=f'{name}.stdout.txt',
               stderr=f'{name}.stderr.txt')
    print(name, result.returncode, flush=True)
    return row


def main():
    old = json.loads(INVENTORY.read_bytes())
    old_coverage = json.loads(COVERAGE.read_bytes())
    before_inputs = {row['path']: sha(ROOT / row['path']) for row in old['sources']}
    before_inputs[NEW] = sha(ROOT / NEW)
    save('source-inputs.before.json', dict(files=before_inputs,
         scope='Inventoried source identities plus the new private helper; not complete compilation/runtime closure.'))
    for name, path in [('inventory.before.json', INVENTORY), ('coverage.before.json', COVERAGE)]:
        with (DEST / name).open('xb') as stream:
            stream.write(path.read_bytes())
    commands = [run('before.inventory', [sys.executable, 'scripts/check_verification_inventory.py']),
                run('before.coverage', [sys.executable, 'scripts/check_production_coverage.py'])]
    save('commands.before.json', commands)
    assert commands[0]['exit_code'] != 0, 'Expected stale source inventory must be observed.'
    actual_changed = {row['path'] for row in old['sources']
                      if before_inputs[row['path']] != row['sha256']}
    assert actual_changed == CHANGED, actual_changed
    updated = json.loads(json.dumps(old))
    differences = []
    for row in updated['sources']:
        if row['path'] in CHANGED:
            surface = public_surface((ROOT / row['path']).read_text())
            assert surface == row['surface'], ('API/capacity drift', row['path'])
            differences.append(dict(path=row['path'], before=row['sha256'],
                                    after=before_inputs[row['path']], surface_unchanged=True))
            row['sha256'] = before_inputs[row['path']]
    new_surface = public_surface((ROOT / NEW).read_text())
    assert new_surface == dict(declarations=[], functions=[], capacity_constants=[])
    updated['sources'].append(dict(path=NEW, sha256=before_inputs[NEW],
                                   group='source', surface=new_surface))
    updated['sources'].sort(key=lambda row: row['path'])
    assert {key: value for key, value in old.items() if key != 'sources'} == {
        key: value for key, value in updated.items() if key != 'sources'}
    updated_coverage = json.loads(json.dumps(old_coverage))
    updated_coverage['surface_sha256'] = surface_identity(updated)
    INVENTORY.write_text(json.dumps(updated, indent=2, ensure_ascii=False) + '\n')
    COVERAGE.write_text(json.dumps(updated_coverage, indent=2, ensure_ascii=False) + '\n')
    for name, path in [('inventory.after.json', INVENTORY), ('coverage.after.json', COVERAGE)]:
        with (DEST / name).open('xb') as stream:
            stream.write(path.read_bytes())
    save('metadata-changes.json', dict(
        source_changes=differences, added_private_source=NEW, added_surface=new_surface,
        old_source_count=len(old['sources']), new_source_count=len(updated['sources']),
        old_surface_sha256=old_coverage['surface_sha256'],
        new_surface_sha256=updated_coverage['surface_sha256'],
        other_parsed_inventory_and_coverage_fields_unchanged=True,
        constitutional_authority_and_proof_status_unchanged=True,
        serialization_note='Existing literal Unicode serialization is retained; comparison is of parsed metadata as well as exact before/after bytes.'))
    after_commands = [
        run('after.inventory', [sys.executable, 'scripts/check_verification_inventory.py']),
        run('after.coverage', [sys.executable, 'scripts/check_production_coverage.py']),
        run('after.inventory-regression', [sys.executable, 'scripts/test_check_verification_inventory.py']),
        run('after.coverage-regression', [sys.executable, 'scripts/test_check_production_coverage.py']),
    ]
    save('commands.after.json', after_commands)
    assert all(sha(ROOT / name) == digest for name, digest in before_inputs.items()), 'Source changed during review.'
    passed = all(row['exit_code'] == 0 for row in after_commands)
    save('results.json', dict(status='passed' if passed else 'failed',
         actual_checks=after_commands, reviewed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
         source_inputs_unchanged=True, scope='Metadata identity and guard regressions only; no new native/Lean/source theorem or release readiness.'))
    files = {path.name: dict(sha256=sha(path), bytes=path.stat().st_size)
             for path in sorted(DEST.iterdir()) if path.is_file()}
    save('files.json', dict(files=files, self_excluded='files.json'))
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
