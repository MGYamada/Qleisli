#!/usr/bin/env python3
"""Small Rust-source Fourier factoring, fresh native binding and complex probes.

The original source graph and candidate are compared independently with the DFT.
This checks the bounded producer translation; it is not a general frontend proof.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

from test_sized_qft import probes

ROOT = Path(__file__).resolve().parents[1]


def run(command, env):
    result = subprocess.run(command, cwd=ROOT, env=os.environ | env, capture_output=True,
                            text=True, timeout=120)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return dict(command=command, stdout=result.stdout, stderr=result.stderr)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kernel', type=Path, default=ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel')
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    commands, semantic, artifacts = [], {}, {}
    with tempfile.TemporaryDirectory(prefix='qleisli-rust-fourier-') as temporary:
        directory = Path(temporary)
        commands.append(run(['cargo', 'test', '--lib', 'actual_source_fourier_factoring', '--', '--nocapture'],
                            {'QLEISLI_FOURIER_PROPOSALS': temporary}))
        cases = []
        for width in (1, 2, 3):
            for kind in ('original', 'candidate', 'delayed-original', 'delayed-candidate'):
                name = f'{kind}-{width}'
                payload = (directory/f'{name}.json').read_bytes()
                graph = json.loads(payload)
                semantic[name] = probes(graph, width)
                assert semantic[name]['maximum_error'] < 1e-12, (name, semantic[name])
                artifacts[name] = dict(sha256=hashlib.sha256(payload).hexdigest(),
                                       definitions=len(graph['definitions']))
                request_name = ''
                if kind.endswith('candidate'):
                    request_name = f'{kind}-request-{width}.json'
                    header = graph['definitions'][graph['entry']['implementation']]['interface']
                    request = dict(format='qleisli.hierarchy-request', version=1,
                        profile='qpe-dyadic8-v1', kind='equation', effect='unitary',
                        interface=header, entry=0,
                        meanings=[dict(interface=header,body=dict(tag='qft',width=width))])
                    (directory/request_name).write_text(json.dumps(request))
                cases.append(f'{name}|{request_name}|ok\n')
        (directory/'cases.txt').write_text(''.join(cases))
        commands.append(run(['cargo','test','--test','sized_corpus','check_source_fourier_contracts',
                             '--','--ignored','--nocapture'],
                            {'QLEISLI_HIERARCHY_KERNEL':str(args.kernel.resolve()),
                             'QLEISLI_SIZED_QFT':temporary}))
    report = dict(format='qleisli.rust-fourier-factoring-validation',version=1,status='pass',
        widths=[1,2,3],phase_sensitive=True,frontend_adequacy_proved=False,
        kernel_sha256=hashlib.sha256(args.kernel.read_bytes()).hexdigest(),
        implementation_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in
            ('src/frontend/sized/fourier.rs','src/frontend/sized/lower.rs',
             'corpus/sized/qualtran_qft/fourier.qli',
             'tests/fixtures/sized_clients/delayed_fourier.qli',
             'scripts/test_rust_fourier_factoring.py')},
        artifacts=artifacts,semantic=semantic,commands=commands)
    if args.record:
        args.record.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(status='pass',artifacts=len(artifacts),widths=report['widths'],
                         maximum_complex_error=max(p['maximum_error'] for p in semantic.values()))))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
