"""Summarize actual fixed-driver logs; never execute commands from records.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""

import json
from pathlib import Path
import re

here = Path(__file__).resolve().parent
summary = {}
for directory in sorted(here.glob('validation-*')):
    record = directory / 'result.json'
    if not record.is_file():
        continue
    result = json.loads(record.read_text())
    expected = 4 if result['mode'].startswith('msrv-all') else (
        3 if '-all' in result['mode'] else 5)
    commands = result['commands']
    termination = result.get('termination')
    failed = any(c['exit_code'] or c.get('timed_out') for c in commands)
    status = ('incomplete-harness-timeout' if termination else 'failed' if failed
              else 'passed' if len(commands) == expected and result['sources_stable']
              else 'incomplete')
    results = []
    for command in commands:
        if 'test' not in command['argv']:
            continue
        stdout = (directory / command['stdout']).read_text()
        rows = [tuple(map(int, row)) for row in re.findall(
            r'test result: (?:ok|FAILED)\. (\d+) passed; (\d+) failed; (\d+) ignored',
            stdout)]
        results.append({'command': command['argv'], 'exit_code': command['exit_code'],
            'reported_groups': len(rows), 'passed': sum(r[0] for r in rows),
            'failed': sum(r[1] for r in rows), 'ignored': sum(r[2] for r in rows)})
    summary[directory.name] = {'status': status, 'executed_commands': len(commands),
        'expected_commands': expected, 'results': results,
        'sources_stable': result['sources_stable'], 'termination': termination}
output = here / 'summary-current.json'
retry = 0
while output.exists():
    retry += 1
    output = here / f'summary-retry-{retry:02d}.json'
output.write_text(json.dumps(summary, indent=2) + '\n')
print('Wrote', output.name)
for name, result in summary.items():
    print(name, result['status'], result['results'])
