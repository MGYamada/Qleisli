#!/usr/bin/env python3
"""Compare retained, bounded observations; this is not source preservation proof.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--before', type=Path, required=True)
    parser.add_argument('--after', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    before = json.loads((args.before / 'commands.json').read_text())
    after = {r['label']: r for r in json.loads((args.after / 'commands.json').read_text())}
    observations = []
    for record in before:
        label = record['label']
        actual = after[label]
        assert record['exit_code'] == actual['exit_code'] == 0, label
        if label in ('build', 'observer-build') or label.endswith('-proposal'):
            # Build output and emit-proposal output-directory paths are not
            # stable observations. Compare actual proposal bytes below.
            continue
        for stream in ('stdout', 'stderr'):
            expected_bytes = (args.before / record[stream]).read_bytes()
            actual_bytes = (args.after / actual[stream]).read_bytes()
            assert expected_bytes == actual_bytes, (label, stream)
        observations.append(label)
    here = Path(__file__).resolve().parent
    extra = json.loads((here / 'additional-study/before.json').read_text())
    for record in extra:
        label = 'additional-' + record['case']
        actual = after[label]
        assert record['exit_code'] == actual['exit_code'] == 0, label
        for stream in ('stdout', 'stderr'):
            assert record[stream].encode() == (args.after / actual[stream]).read_bytes(), (label, stream)
        observations.append(label)
    proposals = []
    for record in json.loads((args.before / 'proposals.json').read_text()):
        expected_bytes = (args.before / record['file']).read_bytes()
        actual_bytes = (args.after / record['file']).read_bytes()
        assert hashlib.sha256(expected_bytes).hexdigest() == record['sha256'], record['label']
        assert expected_bytes == actual_bytes, record['label']
        proposals.append(record)
    result = dict(
        observation_count=len(observations), observations=observations,
        proposal_count=len(proposals), proposals=proposals,
        compared='Exact exit status, stdout and stderr; actual proposal bytes, without normalization.',
        excluded='Build logs and proposal-writing stdout contain checkout/output paths; all commands must succeed.',
    )
    rendered = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end='')


if __name__ == '__main__':
    main()
