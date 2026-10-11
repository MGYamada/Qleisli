#!/usr/bin/env python3
"""Check the experimental native/reference bridge in a fresh temporary module root.

Uses the existing pinned Lean project and build products, not a second toolchain
or acceptance path. Temporary oleans are removed even on failure.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
SOURCE = Path(__file__).resolve().parent
WRAPPER = '''import os,subprocess,sys
env=dict(os.environ)
env['LEAN_PATH']=sys.argv[1]+os.pathsep+env.get('LEAN_PATH','')
sys.exit(subprocess.run(sys.argv[2:],env=env).returncode)
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path, required=True)
    args = parser.parse_args()
    paths = [SOURCE / name for name in ('ReferenceEquality.lean', 'NativeCoefficient.lean', 'ComponentChecks.lean', 'check_proof.py')]
    paths += [ROOT / name for name in ('lean-kernel/QleisliKernel/Raw/InstrumentEquality.lean',
        'lean/Qleisli/Exact.lean', 'lean/Qleisli/Semantics/Exact.lean',
        'lean/Qleisli/RawInstrumentDenotation.lean', 'lean/Qleisli/Semantics/RawInstrument.lean',
        'lean/Qleisli/Semantics/Instrument.lean', 'lean/lean-toolchain', 'lean/lake-manifest.json')]
    def identities():
        return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    before = identities()
    report = dict(format=1, status='running', recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        source_sha256=before, commands=[],
        scope='Actual streamed native coefficient comparison refines the independent complex instrument on arbitrary finite external references. No source/artifact/type gate, guarantee admission or full QS/PR/RS proof.')
    def run(command):
        started = time.monotonic()
        result = subprocess.run(command, cwd=ROOT / 'lean', capture_output=True, text=True, timeout=180)
        report['commands'].append(dict(command=command, cwd=str(ROOT / 'lean'), exit_code=result.returncode,
            stdout=result.stdout, stderr=result.stderr, seconds=time.monotonic()-started))
        args.record.write_text(json.dumps(report, indent=2)+'\n')
        if result.returncode:
            raise RuntimeError(result.stdout+result.stderr)
        return result.stdout
    try:
        run(['lake', 'build', 'Qleisli.Exact', 'Qleisli.RawInstrumentDenotation'])
        with tempfile.TemporaryDirectory(prefix='qleisli-instrument-proofs-') as directory:
            project = Path(directory)
            for name in ('ReferenceEquality', 'NativeCoefficient'):
                run(['lake', 'env', sys.executable, '-c', WRAPPER, directory, 'lean',
                    '-DwarningAsError=true', '--root='+str(SOURCE),
                    '-o', str(project / (name+'.olean')), str(SOURCE / (name+'.lean'))])
            audit = project / 'Audit.lean'
            audit.write_text('import NativeCoefficient\n'+''.join(
                '#print axioms Qleisli.Experiments.InstrumentCoefficient.'+name+'\n'
                for name in ('prepare_reference', 'coefficient_meaning', 'compare_meaning', 'compare_instrument')))
            axioms = run(['lake', 'env', sys.executable, '-c', WRAPPER, directory, 'lean',
                '-DwarningAsError=true', '--root='+directory, str(audit)])
            report['axiom_output'] = axioms
            lists = re.findall(r'depends on axioms: \[(.*?)\]', axioms, re.S)
            assert len(lists) == 4, 'missing theorem axiom output'
            allowed = {'propext', 'Classical.choice', 'Quot.sound'}
            assert all({name.strip() for name in names.split(',')} <= allowed for names in lists), 'unexpected axiom'
            run(['lake', 'env', 'lean', '-DwarningAsError=true', str(SOURCE / 'ComponentChecks.lean')])
        assert before == identities(), 'proof sources changed during checking'
        report['toolchain'] = run(['lake', 'env', 'lean', '--version']).strip()
        report['status'] = 'passed'
    except (AssertionError, OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        report.update(status='failed', error=str(error))
    args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(report['status'])
    if report['status'] != 'passed':
        print(report.get('error', 'failed'), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
