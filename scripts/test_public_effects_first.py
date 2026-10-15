#!/usr/bin/env python3
"""Check the inert pre-implementation public-effect study; execute no record.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
README = ROOT / 'tests/fixtures/authoring_sessions/public-effects-v030/README.md'
STUDY = ROOT / 'tests/fixtures/authoring_sessions/public-effects-v030/first'
FREEZE = '7751de012818e1ca02a6997161a12a2eb100c33a22112922649beb9ed5a58258'
CONTRAST = ROOT / 'tests/fixtures/authoring_sessions/public-effects-v030/quantum-use-contrast'
CONTRAST_FREEZE = '769ceecb8712be36a0123347c733b48a82a0230941486c2493de6ea9267f5aef'


def check_inventory(directory, digest, count):
    frozen_bytes = (directory / 'freeze.json').read_bytes()
    assert hashlib.sha256(frozen_bytes).hexdigest() == digest
    frozen = json.loads(frozen_bytes)
    paths = set()
    for row in frozen['files']:
        name = row['path']
        relative = Path(name)
        assert not relative.is_absolute() and '..' not in relative.parts
        assert name not in paths
        paths.add(name)
        path = directory / relative
        assert path.is_file() and not path.is_symlink()
        actual = path.read_bytes()
        assert len(actual) == row['bytes']
        assert hashlib.sha256(actual).hexdigest() == row['sha256'], name
    assert len(paths) == count
    assert {str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file()} == paths | {'freeze.json'}


def main():
    note = README.read_text()
    for disclosure in (
        'first/freeze.json',
        'quantum-use-contrast/freeze.json',
        'does not identify an exact model build or a checked Git source revision',
        'It never executes recorded commands.',
        'supplies no general source/runtime proof, guarantee admission or release claim.',
    ):
        assert disclosure in note
    check_inventory(STUDY, FREEZE, 163)
    check_inventory(CONTRAST, CONTRAST_FREEZE, 12)
    source = json.loads((STUDY / 'first-sources.json').read_text())
    observations = json.loads((STUDY / 'observations-first.json').read_text())
    analysis = json.loads((STUDY / 'analysis-first.json').read_text())
    assert len(source['cases']) == 19 and len(source['files']) == 43
    assert observations['record_count'] == analysis['commands'] == 38
    assert observations['sources_unchanged'] and analysis['all_original_sources_unchanged']
    assert observations['binaries_before'] == observations['binaries_after']
    assert len(analysis['policy_gap_acceptances']) == 8
    assert analysis['false_pure_refusals']['commands'] == 18
    assert analysis['body_replacement']['caller_sources_identical']
    assert analysis['preserved_wrong_prediction']['actual_code'] == 'unsupported'
    contrast = json.loads((CONTRAST / 'observations.json').read_text())
    assert [(r['case'], r['exit']) for r in contrast['records']] == [('ordinary', 0), ('closed-quantum', 1)]
    context = json.loads((CONTRAST / 'context-before.json').read_text())
    assert contrast['sources_unchanged'] and context['binaries_before'] == contrast['binaries_after']
    assert (CONTRAST / 'ordinary/main.qli').read_bytes() == (CONTRAST / 'closed-quantum/main.qli').read_bytes()
    print('Public-effect history: 163 original files/38 checks and a separate 12-file/2-check quantum-use contrast unchanged; no command executed.')


if __name__ == '__main__':
    main()
