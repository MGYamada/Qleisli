#!/usr/bin/env python3
"""Compare retained bounded observations, without executing recorded commands.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--before', type=Path, required=True)
    p.add_argument('--after', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    before, after = args.before.resolve(), args.after.resolve()
    records = [{r['label']: r for r in json.loads((d / 'commands.json').read_text())} for d in [before, after]]
    labels = {k for k in records[0] if k.endswith('-observer') or k.endswith('-check')}
    if labels != {k for k in records[1] if k.endswith('-observer') or k.endswith('-check')} or len(labels) != 34:
        raise ValueError('expected the same 22 observer and 12 check observations')
    comparisons = []
    for label in sorted(labels):
        b, a = records[0][label], records[1][label]
        equal = b['exit_code'] == a['exit_code'] and all((before / b[k]).read_bytes() == (after / a[k]).read_bytes() for k in ['stdout', 'stderr'])
        comparisons.append(dict(label=label, equal_exit_stdout_stderr=equal))
    tables = [{r['name']: r for r in json.loads((d / 'proposals.json').read_text())} for d in [before, after]]
    if tables[0].keys() != tables[1].keys() or len(tables[0]) != 8:
        raise ValueError('expected the same eight proposals')
    proposals = []
    for name in tables[0]:
        b, a = tables[0][name], tables[1][name]
        same = b['exit_code'] == a['exit_code'] == 0 and b['source_sha256'] == a['source_sha256']
        b_bytes = (before / b['output']).read_bytes() if b['exit_code'] == 0 else None
        a_bytes = (after / a['output']).read_bytes() if a['exit_code'] == 0 else None
        proposals.append(dict(name=name, before_exit=b['exit_code'], after_exit=a['exit_code'], equal_proposal_bytes=same and b_bytes == a_bytes, before_sha256=hashlib.sha256(b_bytes).hexdigest() if b_bytes is not None else None, after_sha256=hashlib.sha256(a_bytes).hexdigest() if a_bytes is not None else None))
    result = dict(baseline='44e23e4', scope='22 syntax/profile cases; 12 source checks; eight proposals. Source check success uses the explicitly selected native kernel; proposal comparison alone grants no acceptance or source-preservation proof.', observations=comparisons, proposals=proposals)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    ok = all(x['equal_exit_stdout_stderr'] for x in comparisons) and all(x['equal_proposal_bytes'] for x in proposals)
    print(f'{sum(x["equal_exit_stdout_stderr"] for x in comparisons)}/34 identical observations; {sum(x["equal_proposal_bytes"] for x in proposals)}/8 identical proposals')
    raise SystemExit(0 if ok else 1)


if __name__ == '__main__':
    main()
