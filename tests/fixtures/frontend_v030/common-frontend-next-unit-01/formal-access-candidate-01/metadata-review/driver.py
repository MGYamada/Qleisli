#!/usr/bin/env python3
"""Root-reviewed exact formal source bindings; no proof/status transition.
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
HERE = Path(__file__).resolve().parent
EXPECTED = {
    'src/frontend/formals.rs': '39d64fe7c6090de81b2afa1b6e6b8b8454151b9514138dbba93eed5e3dff322d',
    'src/frontend/mod.rs': '5aa13633507fbc405a126b432f13bc62f480e8c7784e50f0a94beb1f58bbf7df',
    'src/frontend/compile/operations.rs': '9e77a9745cf166a055c4fec5b009d46132dda460751042919f38af84f03fe23a',
    'src/frontend/sized/check.rs': '1099273ca442b33e67c99fc33efc73aaecef448b222c656455b931d0dbaeeb17',
    'src/frontend/sized/linear.rs': 'c9840b426f33976824c0f9a20fefb4f7e84bb23cca9e58e5aa3c4d53580a0979',
    'src/frontend/sized/ast.rs': 'a8b31ab0f612fc7513ae62103ae050874f64b591d0c3af0b99c0747554ac7fe1',
    'src/frontend/sized/parser.rs': 'cb028400f3dfcb698e3682a2ebb3937c1774fdf1a2fc36fe09362b401c99aee0',
}
SCRIPTS = {
    'scripts/maintain_release.py': 'c05b7775773dbe6cfc0ec59de734d08a8aece4707caf9f1e996d911330676641',
    'scripts/check_verification_inventory.py': '71e4de5f852226beba197ba109230fb43be4c6e923d28ccef4b98a8b25d15ace',
    'scripts/check_production_coverage.py': '0b9f1221ed2c659c032c53dd441042937700d279f72875f5b3c4e6f89923e5ee',
}
INVENTORY = ROOT / 'tests/fixtures/verification_v022/inventory.json'
COVERAGE = ROOT / 'tests/fixtures/verification_v029/coverage.json'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(out, name, data):
    with (out / name).open('x') as stream:
        stream.write(json.dumps(data, indent=2) + '\n')


def run(out, label, argv):
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    stdout, stderr = out / (label + '.stdout.txt'), out / (label + '.stderr.txt')
    with stdout.open('xb') as output, stderr.open('xb') as errors:
        result = subprocess.run(argv, cwd=ROOT, stdout=output, stderr=errors,
                                timeout=180, check=False)
    row = dict(label=label, argv=argv, started_utc=started, exit_code=result.returncode,
               stdout=dict(path=stdout.name, sha256=sha(stdout)),
               stderr=dict(path=stderr.name, sha256=sha(stderr)))
    save(out, label + '.json', row)
    print(label + ': ' + str(result.returncode), flush=True)
    return row


def main():
    if len(sys.argv) != 2 or sys.argv[1] != 'attempt-01':
        raise SystemExit('usage: driver.py attempt-01; root reviews before execution')
    out = HERE / sys.argv[1]
    out.mkdir(exist_ok=False)
    for rel, digest in EXPECTED.items() | SCRIPTS.items():
        assert sha(ROOT / rel) == digest, rel
    sys.path.insert(0, str(ROOT / 'scripts'))
    from check_verification_inventory import public_surface
    from check_production_coverage import surface_identity
    old_inventory, old_coverage = json.loads(INVENTORY.read_text()), json.loads(COVERAGE.read_text())
    old_rows = {r['path']: r for r in old_inventory['sources']}
    assert len(old_rows) == 253 and 'src/frontend/formals.rs' not in old_rows
    plan = json.loads(Path('/private/tmp/qleisli-formal-release-plan.json').read_text())
    assert plan['status'] == 'planned' and plan['version'] == '0.3.0-alpha' and not plan['changes']
    changed = set(EXPECTED) - {'src/frontend/formals.rs'}
    assert {r['path'] for r in plan['source_review']} == changed
    assert all(r['diff_base_matches_binding'] and r['after_sha256'] == EXPECTED[r['path']]
               for r in plan['source_review'])
    for name, path in [('inventory', INVENTORY), ('coverage', COVERAGE)]:
        (out / (name + '.before.json.gz')).write_bytes(gzip.compress(path.read_bytes(), mtime=0))
    (out / 'source-plan.before.json').write_bytes(Path('/private/tmp/qleisli-formal-release-plan.json').read_bytes())
    save(out, 'reviewed-inputs.json', dict(source=EXPECTED, scripts=SCRIPTS,
         scope='Reviewed private formal facts/consumers only. No acceptance/proof/status change; public signature scan is bounded and includes methods of private types.'))
    records = [run(out, 'before.inventory', [sys.executable, 'scripts/check_verification_inventory.py']),
               run(out, 'before.coverage', [sys.executable, 'scripts/check_production_coverage.py'])]
    assert [r['exit_code'] for r in records] == [1, 0]
    new = json.loads(INVENTORY.read_text())
    new['sources'].append(dict(path='src/frontend/formals.rs', sha256=EXPECTED['src/frontend/formals.rs'],
        group='source', surface=public_surface((ROOT / 'src/frontend/formals.rs').read_text())))
    INVENTORY.write_text(json.dumps(new, indent=2) + '\n')
    argv = [sys.executable, 'scripts/maintain_release.py', '--write', '--report', str(out / 'source-plan.reviewed.json')]
    for rel in sorted(changed):
        argv += ['--review-source', rel]
    records.append(run(out, 'source-sync', argv))
    assert records[-1]['exit_code'] == 0
    now = json.loads(INVENTORY.read_text())
    new_rows = {r['path']: r for r in now['sources']}
    assert set(new_rows) == set(old_rows) | {'src/frontend/formals.rs'}
    for rel, row in old_rows.items():
        expected = dict(row, sha256=EXPECTED[rel]) if rel in changed else row
        assert new_rows[rel] == expected, rel
    assert {k:v for k,v in now.items() if k != 'sources'} == {k:v for k,v in old_inventory.items() if k != 'sources'}
    source = {rel:sha(ROOT / rel) for rel in new_rows}
    assert all(source[rel] == row['sha256'] for rel,row in new_rows.items())
    coverage = json.loads(COVERAGE.read_text())
    assert coverage == old_coverage
    coverage['surface_sha256'] = surface_identity(now)
    COVERAGE.write_text(json.dumps(coverage, indent=2) + '\n')
    assert {k:v for k,v in coverage.items() if k != 'surface_sha256'} == {k:v for k,v in old_coverage.items() if k != 'surface_sha256'}
    records += [run(out, 'after.inventory', [sys.executable, 'scripts/check_verification_inventory.py']),
                run(out, 'after.coverage', [sys.executable, 'scripts/check_production_coverage.py'])]
    assert all(r['exit_code'] == 0 for r in records[2:])
    for rel,digest in EXPECTED.items() | SCRIPTS.items():
        assert sha(ROOT / rel) == digest, rel
    for name,path in [('inventory', INVENTORY), ('coverage', COVERAGE)]:
        (out / (name + '.after.json.gz')).write_bytes(gzip.compress(path.read_bytes(),mtime=0))
    save(out, 'all-source-bindings.after.json', dict(files=source, count=len(source)))
    save(out, 'results.json', dict(status='passed', commands=records, source_count=len(source),
        source_hash_changes=sorted(changed), private_source_added='src/frontend/formals.rs',
        other_inventory_fields_unchanged=True, coverage_changed_fields=['surface_sha256'],
        scope='Source/surface identity only; no new route, API authority, proof discharge, guarantee or release validation.',
        original_sources_and_historical_records_modified=False))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
