#!/usr/bin/env python3
"""Compare actual text diagnostics with the unchanged JSON study inputs."""
import hashlib
import json
import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
STUDY = ROOT / 'tests/fixtures/authoring_sessions/inference-law-v030'
OUT = HERE / 'text-checks'
OUT.mkdir(exist_ok=False)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


inputs = {str(p.relative_to(ROOT)): digest(p)
          for p in (STUDY / 'attempt-01').rglob('*') if p.is_file()}
rows = []
native = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
for old in json.loads((STUDY / 'after-repair/result.json').read_text())['observations']:
    label = old['label']
    argv = [arg for arg in old['argv'] if arg != '--format=json']
    cli = Path(argv[0])
    log = OUT / f'{label}.native.jsonl'
    log.touch(exist_ok=False)
    env = os.environ.copy()
    env.update(QLEISLI_STUDY_NATIVE_LOG=str(log), QLEISLI_STUDY_NATIVE=str(native),
               QLEISLI_KERNEL=str(native), QLEISLI_HIERARCHY_KERNEL=str(native))
    before = [digest(cli), digest(native)]
    result = subprocess.run(argv, cwd=ROOT, env=env, capture_output=True, timeout=90)
    (OUT / f'{label}.stdout.txt').write_bytes(result.stdout)
    (OUT / f'{label}.stderr.txt').write_bytes(result.stderr)
    json_result = json.loads((STUDY / 'after-repair' / old['stdout']).read_text())
    same = result.returncode == old['exit_code']
    for diagnostic in json_result['diagnostics']:
        location = diagnostic['primary']
        text = (f"{location['module']}:{location['start']}..{location['end']}: "
                f"{diagnostic['code']}: {diagnostic['message']}")
        same &= text in (result.stdout + result.stderr).decode()
    calls = len(log.read_text().splitlines())
    same &= calls == old['native_invocations']
    same &= before == [digest(cli), digest(native)]
    rows.append({'label': label, 'argv': argv, 'exit_code': result.returncode,
                 'native_invocations': calls, 'cli_sha256': before[0],
                 'kernel_sha256': before[1], 'matches_json': same})
    assert same, label
assert inputs == {p: digest(ROOT / p) for p in inputs}
(OUT / 'driver.py.txt').write_bytes(Path(__file__).read_bytes())
(OUT / 'result.json').write_text(json.dumps({'inputs': inputs, 'inputs_stable': True,
    'all_24_match_json': len(rows) == 24, 'observations': rows}, indent=2) + '\n')
print('PASS: 24 actual text results match JSON status, diagnostics, spans and native counts')
