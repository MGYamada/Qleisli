#!/usr/bin/env python3
"""Review only three source hashes and their derived inventory binding.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import datetime
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path('/Users/masa/git/Qleisli')
DEST = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts'))
from check_verification_inventory import public_surface
from check_production_coverage import surface_identity

INVENTORY = ROOT / 'tests/fixtures/verification_v022/inventory.json'
COVERAGE = ROOT / 'tests/fixtures/verification_v029/coverage.json'
CHANGED = {'src/frontend/pattern.rs', 'src/frontend/compile/mod.rs',
           'src/frontend/sized/check.rs'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(name, data):
    with (DEST / name).open('x') as stream:
        stream.write(json.dumps(data, indent=2) + '\n')


def snapshot(name, path):
    raw = path.read_bytes()
    with (DEST / name).open('xb') as stream:
        stream.write(gzip.compress(raw, mtime=0))
    assert gzip.decompress((DEST / name).read_bytes()) == raw


def check(label, script):
    argv = [sys.executable, script]
    result = subprocess.run(argv, cwd=ROOT, capture_output=True, timeout=120)
    for suffix, raw in [('stdout.txt', result.stdout), ('stderr.txt', result.stderr)]:
        (DEST / (label + '.' + suffix)).open('xb').write(raw)
    print(label, result.returncode, flush=True)
    return {'argv': argv, 'exit_code': result.returncode,
            'stdout': label + '.stdout.txt', 'stderr': label + '.stderr.txt'}


def main():
    old = json.loads(INVENTORY.read_bytes())
    old_coverage = json.loads(COVERAGE.read_bytes())
    inputs = {row['path']: sha(ROOT / row['path']) for row in old['sources']}
    save('source-inputs.before.json', {'files': inputs, 'scope':
         'Inventoried sources only, not complete build/runtime closure.'})
    snapshot('inventory.before.json.gz', INVENTORY)
    snapshot('coverage.before.json.gz', COVERAGE)
    before = [check('before.inventory', 'scripts/check_verification_inventory.py'),
              check('before.coverage', 'scripts/check_production_coverage.py')]
    save('commands.before.json', before)
    assert before[0]['exit_code'] != 0, 'Expected stale hashes must be observed.'
    actual = {row['path'] for row in old['sources'] if inputs[row['path']] != row['sha256']}
    assert actual == CHANGED, actual
    updated = json.loads(json.dumps(old))
    changes = []
    for row in updated['sources']:
        if row['path'] in CHANGED:
            assert public_surface((ROOT / row['path']).read_text()) == row['surface'], row['path']
            changes.append({'path': row['path'], 'before': row['sha256'],
                            'after': inputs[row['path']], 'surface_unchanged': True})
            row['sha256'] = inputs[row['path']]
    assert {k: v for k, v in old.items() if k != 'sources'} == {
        k: v for k, v in updated.items() if k != 'sources'}
    revised_coverage = json.loads(json.dumps(old_coverage))
    revised_coverage['surface_sha256'] = surface_identity(updated)
    INVENTORY.write_text(json.dumps(updated, indent=2, ensure_ascii=False) + '\n')
    COVERAGE.write_text(json.dumps(revised_coverage, indent=2, ensure_ascii=False) + '\n')
    snapshot('inventory.after.json.gz', INVENTORY)
    snapshot('coverage.after.json.gz', COVERAGE)
    after = [check('after.inventory', 'scripts/check_verification_inventory.py'),
             check('after.coverage', 'scripts/check_production_coverage.py')]
    assert all(sha(ROOT / name) == digest for name, digest in inputs.items())
    save('results.json', {'format': 'qleisli.parameter-name-metadata-review',
         'version': 1, 'source_changes': changes, 'before': before, 'after': after,
         'source_count': len(updated['sources']), 'source_inputs_unchanged': True,
         'old_surface_sha256': old_coverage['surface_sha256'],
         'new_surface_sha256': revised_coverage['surface_sha256'],
         'other_parsed_metadata_fields_unchanged': True,
         'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'scope': 'Actual source identity guards only, not new regression execution, '
                  'proof discharge, native authority or release readiness.'})
    return int(any(r['exit_code'] != 0 for r in after))


if __name__ == '__main__':
    raise SystemExit(main())
