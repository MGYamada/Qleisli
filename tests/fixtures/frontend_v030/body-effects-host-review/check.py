"""Fixed non-runtime checks for the diagnostic review packet.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""

import json
from pathlib import Path
import subprocess
import time

here = Path(__file__).resolve().parent
repo = here.parents[3]
out = here / 'checks'
out.mkdir()
commands = [
    ['python3', 'scripts/check_constitution.py', '--base-ref',
     'faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2'],
    ['python3', 'scripts/check_verification_inventory.py'],
    ['python3', 'scripts/check_production_coverage.py'],
    ['python3', 'scripts/check_authoring_sessions.py'],
    ['python3', 'scripts/check_editions.py'],
    ['python3', 'scripts/check_docs.py'],
    ['/private/tmp/qleisli-mdbook-0.5.4-bin/mdbook', '--version'],
    ['/private/tmp/qleisli-mdbook-0.5.4-bin/mdbook', 'build', 'docs'],
    ['python3', 'scripts/check_book.py'],
    ['cargo', 'fmt', '--all', '--', '--check'],
    ['git', 'diff', '--check'],
]
rows = []
for i, argv in enumerate(commands):
    start = time.monotonic()
    with (out / f'{i}.stdout.txt').open('wb') as stdout, (out / f'{i}.stderr.txt').open('wb') as stderr:
        result = subprocess.run(argv, cwd=repo, stdout=stdout, stderr=stderr, timeout=120)
    row = {'argv': argv, 'exit_code': result.returncode, 'seconds': time.monotonic() - start,
           'stdout': f'{i}.stdout.txt', 'stderr': f'{i}.stderr.txt'}
    rows.append(row)
    (out / 'result.json').write_text(json.dumps({'commands': rows,
        'scope': 'Identity/continuity, reviewed metadata, editions, source records, docs and formatting. No fresh Lean replay or release certificate.'}, indent=2) + '\n')
    print(json.dumps(row), flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
