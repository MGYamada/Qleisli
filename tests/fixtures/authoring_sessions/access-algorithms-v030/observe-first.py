from pathlib import Path
import datetime
import hashlib
import json
import os
import signal
import subprocess
import time

root = Path(__file__).resolve().parent
work = Path('/private/tmp/qleisli-516-provider-followup')
cli = Path('/private/tmp/qleisli-beta-qmatch-bounded-v5.wxZviN/target/debug/qleisli')
kernel = work / 'lean-kernel/.lake/build/bin/qleisli-kernel'
manifest = json.loads((root / 'manifest.json').read_text())
for item in manifest['files']:
    assert hashlib.sha256((root / item['path']).read_bytes()).hexdigest() == item['sha256'], item['path']
output = root / 'observations-first'
output.mkdir(exist_ok=False)
identity = {
    'cli': str(cli), 'cli_sha256': hashlib.sha256(cli.read_bytes()).hexdigest(),
    'kernel': str(kernel), 'kernel_sha256': hashlib.sha256(kernel.read_bytes()).hexdigest(),
    'observer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'manifest_sha256': hashlib.sha256((root / 'manifest.json').read_bytes()).hexdigest(),
    'git_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=work, text=True).strip(),
    'dirty_diff_sha256': hashlib.sha256(subprocess.check_output(['git', 'diff', '--binary'], cwd=work)).hexdigest(),
}
(output / 'identity.json').write_text(json.dumps(identity, indent=2) + '\n')
environment = dict(os.environ, QLEISLI_KERNEL=str(kernel))
for case in ('add_k', 'equals', 'grover', 'qpe_prefix', 'walk'):
    for variant in ('access', 'explicit'):
        project = root / 'attempt-01' / f'{case}-{variant}'
        commands = {
            'project-check': [str(cli), 'check', str(project), '--format=json'],
            'selected-check': [str(cli), 'check', '--entry=main::probe',
                               '--module=main=' + str(project / 'main.qli'),
                               '--ir-profile=raw', '--format=json'],
            'project-run': [str(cli), 'run', str(project), '--format=json'],
        }
        for mode, command in commands.items():
            started = datetime.datetime.now(datetime.timezone.utc).isoformat()
            begin = time.monotonic()
            child = subprocess.Popen(command, cwd=work, env=environment,
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                     text=True, start_new_session=True)
            timeout = False
            try:
                stdout, stderr = child.communicate(timeout=90)
            except subprocess.TimeoutExpired:
                timeout = True
                os.killpg(child.pid, signal.SIGTERM)
                stdout, stderr = child.communicate()
            record = {
                'command': command, 'recorded_utc': started,
                'exit_code': child.returncode, 'timeout': timeout,
                'seconds': time.monotonic() - begin,
                'source_sha256': hashlib.sha256((project / 'main.qli').read_bytes()).hexdigest(),
                'raw_stdout': stdout, 'raw_stderr': stderr,
            }
            path = output / f'{case}-{variant}-{mode}.json'
            with path.open('x') as stream:
                json.dump(record, stream, indent=2)
                stream.write('\n')
            try:
                value = json.loads(stdout)
                detail = value.get('diagnostics') or value.get('result', {})
            except ValueError:
                detail = stderr
            print(case, variant, mode, child.returncode, str(detail)[:350], flush=True)
assert hashlib.sha256(cli.read_bytes()).hexdigest() == identity['cli_sha256']
assert hashlib.sha256(kernel.read_bytes()).hexdigest() == identity['kernel_sha256']
for item in manifest['files']:
    assert hashlib.sha256((root / item['path']).read_bytes()).hexdigest() == item['sha256'], item['path']
