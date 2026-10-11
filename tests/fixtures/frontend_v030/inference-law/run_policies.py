#!/usr/bin/env python3
"""Record current diagnostic-maintenance policy checks without changing evidence."""
import hashlib
import json
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OUT = HERE / 'policy-final'
OUT.mkdir(exist_ok=False)
paths = [ROOT / p for p in (
    'tests/fixtures/verification_v022/inventory.json',
    'tests/fixtures/verification_v029/coverage.json',
    'src/frontend/sized/check.rs', 'tests/inference_law.rs',
    'scripts/check_verification_inventory.py', 'scripts/check_production_coverage.py',
    'scripts/check_authoring_sessions.py', 'scripts/check_constitution.py')]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


inputs = {str(p.relative_to(ROOT)): digest(p) for p in paths}
(OUT / 'inputs-before.json').write_text(json.dumps(inputs, indent=2) + '\n')
commands = [['python3', f'scripts/{script}'] for script in (
    'check_verification_inventory.py', 'check_production_coverage.py',
    'check_authoring_sessions.py')]
commands.append(['python3', 'scripts/check_constitution.py', '--base-ref',
                 '8a6a7167f0abd359fb8cac695033778cbca6203f'])
rows = []
for i, argv in enumerate(commands):
    start = time.monotonic()
    result = subprocess.run(argv, cwd=ROOT, capture_output=True, timeout=180)
    (OUT / f'{i}.stdout.txt').write_bytes(result.stdout)
    (OUT / f'{i}.stderr.txt').write_bytes(result.stderr)
    rows.append({'argv': argv, 'exit_code': result.returncode,
                 'seconds': time.monotonic() - start})
    print(argv, result.returncode, flush=True)
    if result.returncode:
        print(result.stdout.decode(), result.stderr.decode())
        break
after = {p: digest(ROOT / p) for p in inputs}
(OUT / 'inputs-after.json').write_text(json.dumps(after, indent=2) + '\n')
(OUT / 'driver.py.txt').write_bytes(Path(__file__).read_bytes())
passed = inputs == after and len(rows) == len(commands) and all(
    row['exit_code'] == 0 for row in rows)
(OUT / 'result.json').write_text(json.dumps({
    'inputs_stable': inputs == after, 'commands': rows, 'passed': passed}, indent=2) + '\n')
raise SystemExit(0 if passed else 1)
