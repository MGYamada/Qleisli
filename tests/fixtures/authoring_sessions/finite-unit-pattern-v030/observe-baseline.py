#!/usr/bin/env python3
"""Observe frozen informed sources with existing executables, without building.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
identity = json.loads((HERE/'identity-before.json').read_text())
binary, kernel = (Path(identity[key]['path']) for key in ('binary','kernel'))
assert sha(binary) == identity['binary']['sha256']
assert sha(kernel) == identity['kernel']['sha256']
projects = json.loads((HERE/'projects.json').read_text())
for project in projects:
    directory=HERE/project['path']
    assert sha(directory/'main.qli') == project['source_sha256']
    assert sha(directory/'Qargo.toml') == project['manifest_sha256']
(HERE/'observations').mkdir(exist_ok=True)
results=[]
for project in projects:
    command=[str(binary),'check',str(HERE/project['path']),'--format=json']
    started=time.monotonic()
    result=subprocess.run(command,cwd=ROOT,capture_output=True,timeout=45,
        env=os.environ|{'QLEISLI_KERNEL':str(kernel)})
    parsed=json.loads(result.stdout)
    observation=dict(command=command,cwd=str(ROOT),exit_code=result.returncode,
        recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        elapsed_seconds=time.monotonic()-started,stdout=parsed,
        stdout_raw=result.stdout.decode(),stderr=result.stderr.decode(),
        source_sha256=project['source_sha256'],manifest_sha256=project['manifest_sha256'],
        binary_sha256=identity['binary']['sha256'],kernel_sha256=identity['kernel']['sha256'])
    (HERE/project['observation']).write_text(json.dumps(observation,indent=2)+'\n')
    diagnostics=parsed.get('diagnostics',[])
    row=dict(category=project['category'],name=project['name'],exit_code=result.returncode,
        diagnostic_codes=[d['code'] for d in diagnostics],observation=project['observation'])
    results.append(row)
    print(project['category'],project['name'],result.returncode,row['diagnostic_codes'],flush=True)
for project in projects:
    directory=HERE/project['path']
    assert sha(directory/'main.qli') == project['source_sha256']
    assert sha(directory/'Qargo.toml') == project['manifest_sha256']
after={p:sha(ROOT/p) for p in identity['current_source_sha256']}
assert after==identity['current_source_sha256']
assert sha(binary)==identity['binary']['sha256'] and sha(kernel)==identity['kernel']['sha256']
(HERE/'baseline-summary.json').write_text(json.dumps(dict(status='observed',results=results,
    sources_and_executables_unchanged=True,current_source_sha256_after=after,
    scope='Nineteen fixed small check commands using the recorded existing binary. Rejections retained as actual diagnostics; source success is not a preservation theorem.'),indent=2)+'\n')
