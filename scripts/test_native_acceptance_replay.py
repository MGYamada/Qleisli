#!/usr/bin/env python3
"""Replay the retained 799 original pairs through native AcceptedProgram.

No new corpus generation or legacy verifier invocation. A successful process
must have created the new native handle; crashes/transport failures never count
as semantic rejection. The original files and decisions remain immutable.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import base64
from concurrent.futures import ThreadPoolExecutor
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'tests/fixtures/verification_v029/equivalence'
BASELINE_SHA = '3b5f3bf8d5d7311114b302bfe78e3eb0ec76ef4700af6b8fe4cf339bf6d1c699'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def decision(returncode, output, stderr, empty_input):
    if returncode == 0 and output == 'accepted\n' and not stderr:
        return True, 'native'
    if returncode == 1 and any(
        output == f'error\t{code}\n'
        and stderr == f'{code}: Lean native checker rejected the artifact/request; no fallback\n'
        for code in ('invalid_ir', 'contract', 'format', 'limit')):
        return False, 'native'
    if (empty_input and returncode == 1 and output == 'error\tlimit\n'
            and stderr == 'limit: proposal files must contain 1..16777216 bytes\n'):
        return False, 'proposal-bound'
    raise ValueError('crash, transport failure or unexpected runner response')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kernel', type=Path, default=ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel')
    parser.add_argument('--runner', type=Path, default=ROOT/'target/debug/examples/native_acceptance')
    parser.add_argument('--record', type=Path, required=True)
    args = parser.parse_args()
    kernel, runner = args.kernel.resolve(), args.runner.resolve()
    if digest(BASE/'results.json') != BASELINE_SHA:
        raise ValueError('original decision record changed')
    baseline = json.loads((BASE/'results.json').read_bytes())
    if digest(BASE/'inputs.jsonl.gz') != baseline['inputs_sha256']:
        raise ValueError('original input archive changed')
    with gzip.open(BASE/'inputs.jsonl.gz', 'rt') as source:
        inputs = [json.loads(line) for line in source]
    observations = baseline['observations']
    if len(inputs) != 799 or len(observations) != 799:
        raise ValueError('original 799 pairs required')
    sources = sorted({p for base in ['src', 'lean-kernel'] for p in (ROOT/base).rglob('*')
                      if p.suffix in {'.rs', '.lean'} and '.lake' not in p.parts}
                     | {ROOT/'examples/native_acceptance.rs', Path(__file__).resolve(),
                        ROOT/'lean-kernel/lean-toolchain', ROOT/'Cargo.toml', ROOT/'Cargo.lock'})
    binding = {str(p.relative_to(ROOT)): digest(p) for p in sources}
    binaries = {'kernel': digest(kernel), 'runner': digest(runner)}
    args.record.mkdir(parents=True, exist_ok=False)
    with tempfile.TemporaryDirectory(prefix='qleisli-native-replay-') as directory:
        directory = Path(directory)

        def run(pair):
            i, row, old = pair
            if row['name'] != old['name'] or old['rust']['accepted'] != old['lean']['accepted']:
                raise ValueError('unaligned original decisions')
            artifact = base64.b64decode(row['artifact'], validate=True)
            artifact_path = directory/f'{i}.qirf'
            artifact_path.write_bytes(artifact)
            command = [str(runner), str(kernel), str(artifact_path)]
            if hashlib.sha256(artifact).hexdigest() != old['artifact_sha256']:
                raise ValueError('artifact identity differs')
            if row['request'] is not None:
                request = base64.b64decode(row['request'], validate=True)
                if hashlib.sha256(request).hexdigest() != old['request_sha256']:
                    raise ValueError('request identity differs')
                request_path = directory/f'{i}.request'
                request_path.write_bytes(request)
                command.append(str(request_path))
            elif old['request_sha256'] is not None:
                raise ValueError('request presence differs')
            result = subprocess.run(command, capture_output=True, timeout=70, check=False)
            output = result.stdout.decode('utf-8', errors='strict')
            stderr = result.stderr.decode('utf-8', errors='replace')
            try:
                accepted, origin = decision(result.returncode, output, stderr,
                                            not artifact or row['request'] == '')
                matched = accepted == old['lean']['accepted']
            except ValueError:
                accepted, origin, matched = None, 'failure', False
            expected = old['lean']['accepted']
            return dict(index=i, name=row['name'], expected=expected, accepted=accepted,
                        matched=matched, origin=origin,
                        returncode=result.returncode, response=output,
                        stderr=stderr[:2048])

        with ThreadPoolExecutor(max_workers=4) as pool:
            rows = list(pool.map(run, [(i, row, observations[i]) for i, row in enumerate(inputs)]))
    if binding != {str(p.relative_to(ROOT)): digest(p) for p in sources}:
        raise ValueError('sources changed during replay')
    if binaries != {'kernel': digest(kernel), 'runner': digest(runner)}:
        raise ValueError('binaries changed during replay')
    failures = [row for row in rows if not row['matched']]
    report = dict(format='qleisli.native-acceptance-replay', version=1,
                  status='failed' if failures else 'passed', baseline_sha256=BASELINE_SHA,
                  source_sha256=binding, binary_sha256=binaries,
                  summary=dict(pairs=len(rows), accepted=sum(row['accepted'] is True for row in rows),
                               rejected=sum(row['accepted'] is False for row in rows),
                               proposal_bound_rejections=sum(row['origin'] == 'proposal-bound' for row in rows),
                               failures=len(failures)), observations=rows)
    (args.record/'results.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report['summary']))
    return 1 if failures else 0


if __name__ == '__main__':
    raise SystemExit(main())
