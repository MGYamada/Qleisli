"""Record one fixed existing small corpus oracle run, preserving first failures.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
The oracle and mathematical references are read without modification.
"""
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
CLI = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
NATIVE = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
EXPECTED_CLI = '4c58a0b51360b99433ea75259967875c40d0caf872e2dc2981616c08d9c7db50'
EXPECTED_NATIVE = '39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85'
ORACLE = ROOT / 'scripts/check_input_corpus.py'
ALLOWED = ('qualtran/less_than2', 'pennylane_demos/vqe_excitation')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def stamp():
    return datetime.now(timezone.utc).isoformat()


def write(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def main():
    assert len(sys.argv) == 2 and sys.argv[1] in ALLOWED
    name = sys.argv[1]
    output = BASE / 'independent-oracle' / name.replace('/', '-')
    assert not output.exists(), 'refuse overwrite first run'
    assert digest(CLI) == EXPECTED_CLI and digest(NATIVE) == EXPECTED_NATIVE
    spec = importlib.util.spec_from_file_location('fixed_oracle', ORACLE)
    oracle = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(oracle)
    manifest = oracle.check_manifest()
    case = next(c for c in manifest['cases'] if c['id'] == name)
    assert case['qubits'] in (4, 5)
    faults = [f for f in json.loads((ROOT / 'corpus/semantic_faults/manifest.json').read_text())['cases'] if f['reference'] == name]
    negatives = oracle.current_negatives()

    def binding():
        return {'oracle_input_binding': oracle.input_binding([case], faults, negatives, CLI),
                'native_sha256': digest(NATIVE),
                'shared_qargo_sha256': digest(ROOT / 'corpus/Qargo.toml'),
                'original_projects': {p.relative_to(ROOT).as_posix(): digest(p)
                                      for project in ALLOWED
                                      for p in sorted((ROOT / 'corpus' / project).rglob('*')) if p.is_file()}}

    output.mkdir(parents=True)
    report = output / 'report.json'
    argv = [sys.executable, '-B', str(ORACLE), str(CLI), '--case', name, '--exhaustive', '--report', str(report)]
    before = binding()
    started = stamp()
    context = {'format': 'qleisli.coherent-basis-independent-oracle-context', 'version': 1,
               'created_utc': started, 'case': case, 'argv': argv, 'cwd': str(ROOT),
               'binary': {'path': str(CLI), 'sha256': EXPECTED_CLI},
               'native': {'path': str(NATIVE), 'sha256': EXPECTED_NATIVE},
               'bindings_before': before,
               'declared_scope': 'One existing 4/5-qubit corpus case. The unchanged runner also checks its four small curated rejection cases. Exhaustive X/Y interference uses one extra reference/control qubit; no all-corpus or maximum-sized run, build or new mathematical oracle.'}
    write(output / 'context-before.json', context)
    environment = os.environ.copy()
    environment['QLEISLI_KERNEL'] = str(NATIVE)
    began = time.monotonic()
    failure = None
    try:
        completed = subprocess.run(argv, cwd=ROOT, env=environment, capture_output=True, timeout=1800)
        stdout, stderr, code = completed.stdout, completed.stderr, completed.returncode
    except subprocess.TimeoutExpired as error:
        stdout, stderr, code = error.stdout or b'', error.stderr or b'', None
        failure = {'kind': 'TimeoutExpired', 'seconds': 1800}
    elapsed = time.monotonic() - began
    (output / 'stdout.txt').write_bytes(stdout)
    (output / 'stderr.txt').write_bytes(stderr)
    after = binding()
    identities_equal = before == after and digest(CLI) == EXPECTED_CLI and digest(NATIVE) == EXPECTED_NATIVE
    parsed = json.loads(report.read_text()) if report.exists() else None
    event = {'format': 'qleisli.coherent-basis-independent-oracle-observation', 'version': 1,
             'started_utc': started, 'ended_utc': stamp(), 'seconds': elapsed,
             'argv': argv, 'cwd': str(ROOT), 'exit_code': code, 'exception': failure,
             'binary': context['binary'], 'native': context['native'],
             'bindings_before': before, 'bindings_after': after,
             'identities_unchanged': identities_equal,
             'raw_stdout': {'path': 'stdout.txt', 'sha256': digest(output / 'stdout.txt')},
             'raw_stderr': {'path': 'stderr.txt', 'sha256': digest(output / 'stderr.txt')},
             'report_sha256': digest(report) if report.exists() else None,
             'oracle_status': parsed.get('status') if parsed else None,
             'scope': 'Actual unchanged mathematical oracle at its recorded floating-point tolerance, exhaustive finite complex-entry and controlled-phase probes. Explicit native selection bytes are identified; no native child count, Lean replay, universal source-preservation theorem, guarantee admission, exact arithmetic proof, external qlippy or release certification is inferred.'}
    write(output / 'observation.json', event)
    print(json.dumps({'case': name, 'exit_code': code, 'oracle_status': event['oracle_status'],
                      'identities_unchanged': identities_equal, 'seconds': elapsed,
                      'cases': parsed.get('cases') if parsed else None,
                      'failures': parsed.get('failures') if parsed else None,
                      'observation_sha256': digest(output / 'observation.json')}, indent=2))
    return 0 if code == 0 and identities_equal and parsed and parsed['status'] == 'passed' else 1


if __name__ == '__main__':
    sys.exit(main())
