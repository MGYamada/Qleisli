#!/usr/bin/env python3
"""Fixed record checks; no commands are selected from evidence metadata.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""

import datetime
import json
from pathlib import Path
import subprocess
import sys
import time


root = Path(__file__).resolve().parent
repo = root.parents[3]
output = root / 'record-validation'
output.mkdir()
commands = [
    ['python3', 'scripts/check_constitution.py', '--base-ref',
     'faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2'],
    ['python3', 'scripts/check_authoring_sessions.py'],
    ['python3', 'scripts/test_check_authoring_sessions.py'],
    ['python3', 'scripts/check_editions.py'],
    ['python3', 'scripts/check_docs.py'],
]
rows = []
for index, command in enumerate(commands):
    start = time.monotonic()
    result = subprocess.run(command, cwd=repo, capture_output=True, timeout=60)
    stem = f'{index:02d}'
    (output / f'{stem}.stdout.txt').write_bytes(result.stdout)
    (output / f'{stem}.stderr.txt').write_bytes(result.stderr)
    rows.append({'command': command, 'exit_code': result.returncode,
                 'seconds': time.monotonic() - start,
                 'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                 'stdout': f'{stem}.stdout.txt', 'stderr': f'{stem}.stderr.txt'})
    print(command[1], result.returncode, flush=True)
(output / 'commands.json').write_text(json.dumps(rows, indent=2) + '\n')
sys.exit(int(any(row['exit_code'] for row in rows)))
