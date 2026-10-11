#!/usr/bin/env python3
"""Retain bounded actual CLI observations; do not fake native decisions."""

import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

root = Path(__file__).resolve().parent
repo = root.parents[3]
phase = sys.argv[1]
binary = Path(sys.argv[2]).resolve()
attempt = sys.argv[3] if len(sys.argv) > 3 else 'attempt-01'
native = repo / 'lean-kernel/.lake/build/bin/qleisli-kernel'
wrapper = root.parent / 'body-effects-v030/native-log.py'
records = root / phase
records.mkdir()
source_map = {str(p.relative_to(repo)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in sorted((repo / 'src').rglob('*.rs'))}
identity = {'binary': str(binary),
            'binary_sha256': hashlib.sha256(binary.read_bytes()).hexdigest(),
            'native_sha256': hashlib.sha256(native.read_bytes()).hexdigest(),
            'source_files': source_map,
            'source_binding_note': 'Binary observation; source maps alone are not compilation attestation.'}
(records / 'identity.json').write_text(json.dumps(identity, indent=2) + '\n')
session_file = root / 'session.json'
session = json.loads(session_file.read_text())
target = next(item for item in session['attempts'] if item['id'] == attempt)
for source in sorted((root / attempt).iterdir()):
    for output in ['text', 'json']:
        name = source.name + '-' + output
        log = records / (name + '.native.jsonl')
        log.touch()
        argv = [str(binary), 'check']
        if source.name.startswith('host-'):
            argv += ['--entry=main::entry', f'--module=main={source / "main.qli"}',
                     '--operation=U=main::provider']
        else:
            argv += [str(source)]
        if output == 'json':
            argv += ['--format=json']
        env = dict(os.environ, QLEISLI_KERNEL=str(wrapper),
                   QLEISLI_STUDY_NATIVE=str(native), QLEISLI_STUDY_NATIVE_LOG=str(log))
        start = time.monotonic()
        result = subprocess.run(argv, env=env, capture_output=True, timeout=30)
        (records / (name + '.stdout.txt')).write_bytes(result.stdout)
        (records / (name + '.stderr.txt')).write_bytes(result.stderr)
        observation = {'command': argv, 'exit_code': result.returncode,
                       'stderr': result.stderr.decode(),
                       'native_invocations': len(log.read_text().splitlines()),
                       'seconds': time.monotonic() - start,
                       'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                       'timestamp_note': 'Clock after completion; not authenticated provenance.'}
        if output == 'json':
            observation['stdout'] = json.loads(result.stdout)
        else:
            observation['transcript'] = result.stdout.decode() + result.stderr.decode()
        path = records / (name + '.json')
        path.write_text(json.dumps(observation, indent=2) + '\n')
        target['observations'].append(str(path.relative_to(root)))
        session_file.write_text(json.dumps(session, indent=2) + '\n')
        print(name, result.returncode, observation['native_invocations'],
              observation['stdout']['diagnostics'][0]['code'] if output == 'json' and result.returncode else '')
assert identity['binary_sha256'] == hashlib.sha256(binary.read_bytes()).hexdigest()
assert source_map == {str(p.relative_to(repo)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in sorted((repo / 'src').rglob('*.rs'))}
