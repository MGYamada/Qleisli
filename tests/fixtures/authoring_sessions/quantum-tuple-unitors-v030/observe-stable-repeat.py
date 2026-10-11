"""Append explicit repeated observations; never overwrite the first run."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import time

root = Path(__file__).resolve().parents[4]
p = Path(__file__).resolve().parent
out = p / 'stable-repeat'
out.mkdir(exist_ok=True)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def save(name, value):
    path = out / name
    assert not path.exists(), path
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')

original = json.loads((p / 'identity-before.json').read_text())
first = json.loads((p / 'first-files.json').read_text())['files']
cli = Path(original['binary']['path'])
kernel = Path(original['kernel']['path'])
expected = 'f9b3d297bf751e79510b51d949f8129c2f0cab1113d62526a7c579a9d382b34c'
assert sha(cli) == expected
assert sha(kernel) == original['kernel']['sha256']
for f, h in first.items():
    assert sha(p / f) == h, f
sources = {f: sha(root / f) for f in original['current_source_sha256']}
assert sources == original['current_source_sha256']
provenance = root / 'tests/fixtures/frontend_v030/type-pattern-classification'
before = {
    'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'binary_sha256': sha(cli), 'kernel_sha256': sha(kernel),
    'current_source_sha256': sources,
    'build_records': {str((provenance / f).relative_to(root)): sha(provenance / f)
                      for f in ['commands.json', 'sources.json', 'result.json']},
    'scope': 'Root identifies its final actual MSRV1.85 cargo test as the shared CLI replacement. These records preserve its actual commands and selected inputs; no exhaustive dependency/build attestation is inferred. No build is performed by this observer.',
}
save('identity-before.json', before)
env = {'QLEISLI_KERNEL': str(kernel), 'QLEISLI_HIERARCHY_KERNEL': str(kernel)}
rows = []
for case in json.loads((p / 'expectations.json').read_text())['cases']:
    name = case['name']
    directory = p / 'attempt-01' / name
    for route in ['selected', 'finite']:
        command = [str(cli), '--format=json', 'check']
        if route == 'selected':
            command += ['--entry=main::f', '--module=main=' + str(directory / 'main.qli'),
                        '--ir-profile=hierarchy', '--lean-kernel=' + str(kernel)]
        else:
            command += [str(directory)]
        binary_before = sha(cli)
        assert binary_before == expected
        date = datetime.datetime.now(datetime.timezone.utc).isoformat()
        start = time.monotonic()
        run = subprocess.run(command, cwd=root, env=dict(os.environ, **env),
                             capture_output=True, timeout=60)
        record = {
            'command': command, 'working_directory': str(root), 'environment': env,
            'exit_code': run.returncode, 'recorded_utc': date,
            'timestamp_note': 'Clock observation immediately before this command.',
            'elapsed_seconds': time.monotonic() - start,
            'stdout_text': run.stdout.decode(), 'stderr': run.stderr.decode(),
            'source_sha256': sha(directory / 'main.qli'),
            'manifest_sha256': sha(directory / 'Qargo.toml'),
            'binary_sha256_before': binary_before, 'binary_sha256_after': sha(cli),
            'kernel_sha256': sha(kernel),
        }
        record['stdout'] = json.loads(record['stdout_text'])
        save(f'{name}-{route}.json', record)
        assert record['binary_sha256_after'] == expected
        rows.append({'case': name, 'route': route, 'exit_code': run.returncode,
                     'diagnostics': record['stdout'].get('diagnostics', [])})
for f, h in first.items():
    assert sha(p / f) == h
assert {f: sha(root / f) for f in sources} == sources
assert sha(cli) == expected
assert sha(kernel) == original['kernel']['sha256']
save('identity-after.json', {'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                            'binary_sha256': sha(cli), 'kernel_sha256': sha(kernel),
                            'first_files_unchanged': True, 'production_sources_unchanged': True,
                            'binary_stable': True, 'observations': len(rows)})
save('summary.json', {'observations': rows, 'count': len(rows),
                     'scope': 'Repeated44 unchanged first-source checks under stable explicitly identified CLI. Open functions are not executed.'})
print(json.dumps({'observations':len(rows),'selected_success':sum(r['route']=='selected' and r['exit_code']==0 for r in rows),'finite_success':sum(r['route']=='finite' and r['exit_code']==0 for r in rows),'binary_stable':True}))
