# Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""Capture the frozen first sources; observations are not semantic proofs."""
import hashlib, json, os, subprocess, sys
from datetime import datetime, timezone
from pathlib import Path

root = Path(__file__).resolve().parent
cli, kernel = map(lambda x: Path(x).resolve(), sys.argv[1:])
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
packet = json.loads((root / 'context.json').read_text())
frozen = {x['path']: x['sha256'] for x in packet['files']}
def unchanged():
    assert all(digest(root / p) == h for p, h in frozen.items())
unchanged()
identity = {'cli': str(cli), 'cli_sha256': digest(cli), 'kernel': str(kernel),
            'kernel_sha256': digest(kernel), 'context_sha256': digest(root / 'context.json'),
            'observer_sha256': digest(Path(__file__)), 'scope': 'Observed files, not a build attestation.'}
(root / 'identity.json').write_text(json.dumps(identity) + '\n')
for name, action in [('restored-contract','run'), ('phase-contract-rejected','check'),
                     ('phase-reference-observed','run')]:
    command = [str(cli), action, 'attempt-01/' + name, '--format=json']
    result = subprocess.run(command, cwd=root, env=dict(os.environ, QLEISLI_KERNEL=str(kernel)),
                            text=True, capture_output=True, timeout=60)
    record = {'command': command, 'cwd': str(root), 'exit_code': result.returncode,
              'recorded_utc': datetime.now(timezone.utc).isoformat(),
              'transcript': result.stdout, 'stderr': result.stderr,
              'stream_note': 'transcript is verbatim stdout; stderr is separate; identity.json records the selected kernel environment.'}
    (root / (name + '.json')).write_text(json.dumps(record) + '\n')
    print(name, result.returncode, result.stdout, result.stderr, flush=True)
    unchanged()
assert digest(cli) == identity['cli_sha256'] and digest(kernel) == identity['kernel_sha256']
