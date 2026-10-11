import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

root = Path('/private/tmp/qleisli-predicate-corpus-fixed')
out = Path('/private/tmp/qleisli-predicate-corpus-fixed-replay')
out.mkdir(exist_ok=True)
binary = Path('/private/tmp/qleisli-ordinary-types-before-20261005/target/debug/qleisli')
kernel = Path('/Users/masa/git/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel')
cases = ['quantum_katas/grover2', 'qualtran/and_phase', 'qualtran/reflection2',
         'pennylane_demos/vqe_excitation', 'pennylane_demos/phase_lock',
         'quantum_katas/deutsch_jozsa3']
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
identity = {'source_commit': '18f55693e31585dde67eeddeb064e77c138f9a57',
            'snapshot': str(root), 'binary': str(binary), 'binary_sha256': sha(binary),
            'kernel': str(kernel), 'kernel_sha256': sha(kernel),
            'driver_sha256': sha(root/'scripts/check_input_corpus.py'), 'cases': cases,
            'scope': 'Existing affected corpus cases, non-exhaustive semantic probes; no new maximum case.'}
(out/'session.json').write_text(json.dumps(identity, indent=2)+'\n')
env = dict(os.environ, QLEISLI_KERNEL=str(kernel))

def run(case):
    label = case.replace('/', '-')
    argv = ['python3', 'scripts/check_input_corpus.py', str(binary), '--case', case,
            '--report', str(out/(label+'.json'))]
    start = time.monotonic()
    result = subprocess.run(argv, cwd=root, env=env, capture_output=True)
    (out/(label+'.stdout')).write_bytes(result.stdout)
    (out/(label+'.stderr')).write_bytes(result.stderr)
    record = {'case': case, 'argv': argv, 'cwd': str(root), 'exit_code': result.returncode,
              'seconds': time.monotonic()-start, 'stdout': label+'.stdout', 'stderr': label+'.stderr'}
    (out/(label+'.command.json')).write_text(json.dumps(record, indent=2)+'\n')
    return record

records = []
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
    for result in pool.map(run, cases):
        records.append(result)
        print(json.dumps(result), flush=True)
assert sha(binary) == identity['binary_sha256'] and sha(kernel) == identity['kernel_sha256']
(out/'commands.json').write_text(json.dumps(records, indent=2)+'\n')
raise SystemExit(any(r['exit_code'] for r in records))
