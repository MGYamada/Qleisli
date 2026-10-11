"""Run two fixed record/doc guards, never commands read from stored records."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import time

ROOT = Path(__file__).resolve().parent.parent
REPO = Path('/Users/masa/git/Qleisli')
OUT = ROOT / 'record-check'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_frozen():
    frozen = json.loads((ROOT / 'files-before.json').read_text())['files']
    for name, expected in frozen.items():
        if digest(ROOT / name) != expected['sha256']:
            raise RuntimeError(f'preserved first record changed: {name}')
    return frozen


def main():
    frozen = check_frozen()
    # These argument lists are authored constants, not loaded command metadata.
    commands = (
        ('authoring', ['python3', 'scripts/check_authoring_sessions.py']),
        ('docs', ['python3', 'scripts/check_docs.py']),
    )
    results = []
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    for label, argv in commands:
        start = time.monotonic()
        proc = subprocess.run(argv, cwd=REPO, env=env, capture_output=True,
                              timeout=90, check=False)
        stdout = OUT / f'{label}.stdout.txt'
        stderr = OUT / f'{label}.stderr.txt'
        stdout.open('xb').write(proc.stdout)
        stderr.open('xb').write(proc.stderr)
        event = {
            'argv': argv, 'cwd': str(REPO), 'exit_code': proc.returncode,
            'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'seconds': time.monotonic() - start,
            'stdout': {'path': stdout.name, 'sha256': digest(stdout)},
            'stderr': {'path': stderr.name, 'sha256': digest(stderr)},
            'scope': 'Record/doc integrity only; no recorded command executed, '
                     'no Cargo/Lean build, replay, functional oracle or proof.',
        }
        (OUT / f'{label}.json').open('x').write(json.dumps(event, indent=2) + '\n')
        print(proc.stdout.decode(), end='')
        print(proc.stderr.decode(), end='')
        print(label, 'actual exit', proc.returncode)
        results.append(event)
        check_frozen()
    summary = {'commands': results, 'frozen_first_files_unchanged': True,
               'frozen_file_count': len(frozen), 'records_only': True}
    (OUT / 'results.json').open('x').write(json.dumps(summary, indent=2) + '\n')
    return int(any(event['exit_code'] for event in results))


if __name__ == '__main__':
    raise SystemExit(main())
