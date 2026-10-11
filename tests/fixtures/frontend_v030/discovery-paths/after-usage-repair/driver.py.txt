#!/usr/bin/env python3
"""Informed discovery/usage experiment; not a zero-prior authoring benchmark."""
import argparse
import hashlib
import json
import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
STUDY = ROOT / 'tests/fixtures/authoring_sessions/inference-law-v030'
CLI = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
NATIVE = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
parser = argparse.ArgumentParser()
parser.add_argument('--record', required=True)
args = parser.parse_args()
out = HERE / args.record
out.mkdir(exist_ok=False)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


probes = [[], ['--help'], ['help'], ['help', 'ecosystem'], ['qlt'], ['qdb'],
          ['qcp'], ['qlippy'], ['--format=json', 'qlt'], ['interop', 'qlt'],
          ['sized', 'qlt'], ['--format=json', 'help', 'ecosystem'],
          ['--help', '--format=json'], ['help', 'ecosystem', '--entry=main::f'],
          ['nonsense', '--entry=main::f', '--format=json']]
for row in json.loads((STUDY / 'after-repair/result.json').read_text())['observations']:
    if row['label'] in {'natural-missing-both', 'operation-missing', 'call-missing-operation'}:
        probes.append(row['argv'][1:])
inputs = {str(p.relative_to(ROOT)): digest(p) for p in (STUDY / 'attempt-01').rglob('*')
          if p.is_file()}
inputs['tests/fixtures/authoring_sessions/inference-law-v030/native-log.py'] = digest(
    STUDY / 'native-log.py')
rows = []
for i, argv in enumerate(probes):
    log = out / f'{i}.native.jsonl'
    log.touch(exist_ok=False)
    env = os.environ.copy()
    env.update(QLEISLI_KERNEL=str(STUDY / 'native-log.py'),
               QLEISLI_HIERARCHY_KERNEL=str(STUDY / 'native-log.py'),
               QLEISLI_STUDY_NATIVE_LOG=str(log), QLEISLI_STUDY_NATIVE=str(NATIVE))
    before = [digest(CLI), digest(NATIVE)]
    result = subprocess.run([str(CLI), *argv], cwd=ROOT, env=env,
                            capture_output=True, timeout=90)
    (out / f'{i}.stdout.txt').write_bytes(result.stdout)
    (out / f'{i}.stderr.txt').write_bytes(result.stderr)
    calls = len(log.read_text().splitlines())
    rows.append({'argv': [str(CLI), *argv], 'exit_code': result.returncode,
                 'native_invocations': calls, 'cli_sha256': before[0],
                 'kernel_sha256': before[1]})
    assert before == [digest(CLI), digest(NATIVE)]
    assert calls == 0, argv
assert inputs == {p: digest(ROOT / p) for p in inputs}
(out / 'driver.py.txt').write_bytes(Path(__file__).read_bytes())
(out / 'result.json').write_text(json.dumps({'inputs': inputs, 'inputs_stable': True,
    'scope': '15 help/usage probes and 3 unchanged explicit-binding source rejections; informed study',
    'observations': rows}, indent=2) + '\n')
print(f'{args.record}: {len(rows)} observations, zero native invocations')
