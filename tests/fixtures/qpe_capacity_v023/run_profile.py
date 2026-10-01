#!/usr/bin/env python3
"""Profile small saved Rust proposals with the unchanged native QPE checker.

Inputs are exports named n1-m{2,3}-{textbook,delayed}-{payload,request,candidate}.json.
The actual service and public Rust finite adapter determine acceptance. Individual
Lean stages run under the same 2M cap only to locate cost; their sum is diagnostic.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
CASES = [f'n1-m{m}-{kind}' for m in (2, 3) for kind in ('textbook', 'delayed')]
RUST = r'''use qleisli::interchange::hierarchical::Kernel;
use std::{fs, path::Path};
fn main() {
    let args: Vec<_> = std::env::args().collect();
    let directory = Path::new(&args[1]);
    let kernel = Kernel::new(&args[2]);
    for m in [2, 3] {
        for variant in ["textbook", "delayed"] {
            let name = format!("n1-m{m}-{variant}");
            std::env::set_var("QLEISLI_PROFILE_CASE", &name);
            let payload = fs::read(directory.join(format!("{name}-payload.json"))).unwrap();
            let request = fs::read(directory.join(format!("{name}-request.json"))).unwrap();
            let candidate = fs::read(directory.join(format!("{name}-candidate.json"))).unwrap();
            match kernel.check_qpe_instrument(&payload, &request, &candidate) {
                Ok(checked) => {
                    let p = checked.instrument().reconstruction();
                    println!("{name}|ok|{}|{}|{}", p.structural_work(), p.exact_work(), p.leaves().len());
                }
                Err(error) => println!("{name}|error|{}", error.code),
            }
        }
    }
}'''
CAPTURE = '''#!/usr/bin/env python3
import os, subprocess, sys
from pathlib import Path
payload = sys.stdin.buffer.read()
assert payload[:4] == b'QLQ1'
Path(os.environ['QLEISLI_PROFILE_OUTPUT'], os.environ['QLEISLI_PROFILE_CASE']+'.bin').write_bytes(payload)
run = subprocess.run([KERNEL, *sys.argv[1:]], input=payload, capture_output=True, timeout=60)
sys.stdout.buffer.write(run.stdout)
sys.stderr.buffer.write(run.stderr)
raise SystemExit(run.returncode)
'''


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def invoke(argv, cwd, environment, commands):
    result = subprocess.run(argv, cwd=cwd, env=environment, capture_output=True,
                            text=True, timeout=240)
    commands.append(dict(argv=list(map(str, argv)), exit_code=result.returncode))
    assert result.returncode == 0, result.stdout + result.stderr
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input_directory', type=Path)
    parser.add_argument('--record', required=True, type=Path)
    parser.add_argument('--producer-commit', required=True)
    parser.add_argument('--producer-state', choices=('committed', 'working-tree'), default='committed')
    parser.add_argument('--expect', choices=('before', 'accepted'), required=True)
    parser.add_argument('--kernel', type=Path,
                        default=ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel')
    parser.add_argument('--cargo-target', type=Path)
    parser.add_argument('--baseline-directory', type=Path)
    args = parser.parse_args()
    directory, kernel = args.input_directory.resolve(), args.kernel.resolve()
    producer_commit = subprocess.check_output(
        ['git', 'rev-parse', '--verify', args.producer_commit+'^{commit}'], cwd=ROOT,
        text=True).strip()
    commands = []
    with tempfile.TemporaryDirectory(prefix='qleisli-qpe-profile-') as temporary:
        project = Path(temporary)
        environment = os.environ | {'QLEISLI_PROFILE_OUTPUT': str(project)}
        target = args.cargo_target or project/'target'
        environment['CARGO_TARGET_DIR'] = str(target)
        (project/'Cargo.toml').write_text('[package]\nname = "qpe_profile_capture"\n'
            'version = "0.0.0"\nedition = "2021"\n[dependencies]\n'
            f'qleisli = {{ path = {json.dumps(str(ROOT))} }}\n')
        (project/'src').mkdir()
        (project/'src/main.rs').write_text(RUST)
        capture = project/'capture.py'
        capture.write_text(CAPTURE.replace('import os,', f'KERNEL = {json.dumps(str(kernel))}\nimport os,'))
        capture.chmod(0o755)
        receipts = invoke(['cargo', 'run', '--offline', '--manifest-path',
            str(project/'Cargo.toml'), '--', str(directory), str(capture)], project,
            environment, commands)
        reconstructed = {name: fields for name, *fields in
                         (line.split('|') for line in receipts.splitlines())}
        assert reconstructed.keys() == set(CASES)
        (project/'lean-toolchain').write_text((ROOT/'lean-kernel/lean-toolchain').read_text())
        (project/'lakefile.toml').write_text('name = "qpe_capacity_profile"\n'
            'version = "0.0.0"\ndefaultTargets = ["qpe-capacity-profile"]\n'
            '[[require]]\nname = "qleisli_kernel"\n'
            f'path = {json.dumps(str(ROOT/"lean-kernel"))}\n'
            '[[lean_exe]]\nname = "qpe-capacity-profile"\nroot = "Profile"\n')
        shutil.copyfile(Path(__file__).with_name('Profile.lean'), project/'Profile.lean')
        invoke(['lake', 'build'], project, environment, commands)
        native = project/'.lake/build/bin/qpe-capacity-profile'
        output = invoke([str(native), *[str(project/(name+'.bin')) for name in CASES]],
                        project, environment, commands)
        stages = {}
        for line in output.splitlines():
            path, stage, *fields = line.split('|')
            stages.setdefault(Path(path).stem, {}).setdefault(stage, []).append(fields)
        cases = {}
        for name, data in stages.items():
            cost = lambda stage: int(data[stage][0][1])
            preparation, readout = cost('preparation-isolated'), cost('readout-isolated')
            conditional = list(map(int, data['conditional'][0][1:]))
            schedule = cost('schedule-isolated')
            charges = dict(root=int(data['root-charge'][0][0]),
                schedule=int(data['schedule-work-charge'][0][0]),
                instrument=int(data['instrument-charge'][0][0]))
            root_total = conditional[0] + charges['root'] + cost('provider-isolated') + schedule
            diagnostic_total = root_total + charges['instrument'] + preparation + readout
            assert root_total == cost('actual-qpe-root')
            assert schedule == charges['schedule'] + cost('parts-isolated') + cost('inverse-isolated') + cost('trace-isolated')
            accepted = data['actual-instrument'][0][0] == 'ok'
            expected = args.expect == 'accepted' or '-m2-' in name
            assert accepted == expected, (name, data['actual-instrument'])
            assert (reconstructed[name][0] == 'ok') == accepted
            service = dict(status='accepted' if accepted else 'limit')
            if accepted:
                structural, exact, leaves = map(int, reconstructed[name][1:])
                assert structural == diagnostic_total <= 2000000
                assert structural == cost('actual-instrument')
                service.update(structural_work=structural, exact_work=exact,
                    finite_equations=leaves, provider_finite_pairs=int(data['actual-instrument'][0][3]),
                    hadamard_roles=int(data['actual-instrument'][0][4]))
            else:
                assert reconstructed[name] == ['error', 'limit']
            request = json.loads((directory/(name+'-request.json')).read_text())
            provider = json.dumps(request['provider'], sort_keys=True, separators=(',', ':')).encode()
            cases[name] = dict(service=service, graph_counts=list(map(int, data['graph'][0])),
                conditional=dict(total=conditional[0], contract_typing=conditional[1],
                    node_typing=conditional[2], preparation=conditional[3], finite_obligations=conditional[4]),
                charges=charges, provider=cost('provider-isolated'), schedule=schedule,
                powers=cost('parts-isolated'), inverse_fourier=cost('inverse-isolated'),
                trace=cost('trace-isolated'), preparation=preparation, readout=readout,
                isolated_diagnostic_total=diagnostic_total, diagnostic_budget_margin=2000000-diagnostic_total,
                provider_request_sha256=hashlib.sha256(provider).hexdigest(),
                bridge_sha256=digest(project/(name+'.bin')),
                input_sha256={suffix: digest(directory/(name+'-'+suffix+'.json'))
                              for suffix in ('payload', 'request', 'candidate', 'precursor')})
            if args.baseline_directory:
                baseline = args.baseline_directory
                before = json.loads((baseline/(name+'-payload.json')).read_text())['circuit']
                after = json.loads((directory/(name+'-payload.json')).read_text())['circuit']
                before_root = before['definitions'][before['entry']['implementation']]['interface']
                after_root = after['definitions'][after['entry']['implementation']]['interface']
                before_provider = json.loads((baseline/(name+'-request.json')).read_text())['provider']
                assert before_root == after_root and before_provider == request['provider']
                cases[name]['same_full_source_root_interface'] = True
                cases[name]['same_independent_provider_request'] = True
        modules = ['QpeInstrument', 'QpeRoot', 'QpeSchedule', 'Conditional', 'ContractTyping',
                   'NodeTyping', 'CircuitTrace', 'RoutedPower', 'FourierRoot', 'Root', 'Preparation', 'Readout']
        pins = [f'lean-kernel/QleisliKernel/Hierarchical/{m}.lean' for m in modules]
        pins += ['lean-kernel/Protocol.lean', 'lean-kernel/Main.lean',
                 'src/frontend/sized/lower.rs', 'src/frontend/sized/fourier.rs',
                 'src/frontend/sized/qpe.rs', 'src/interchange/hierarchical.rs',
                 'tests/sized_source.rs',
                 'tests/fixtures/sized_clients/delayed_fourier.qli',
                 'corpus/sized/measured_qpe/measurement.qli',
                 'corpus/sized/qualtran_qpe/estimation.qli',
                 'corpus/sized/qualtran_qft/fourier.qli']
        report = dict(format='qleisli.named-qpe-capacity-profile', version=1,
            recorded_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
            producer_base_commit=producer_commit, producer_state=args.producer_state,
            profile=args.expect, aggregate_budget=2000000,
            quantum_widths=[3, 4], source_preservation_proved=False, production_authority_transferred=False,
            isolated_diagnostic='Separate inspectors use the existing 2M ceiling; their sum is not an accepted receipt.',
            kernel_sha256=digest(kernel), profile_binary_sha256=digest(native),
            profile_source_sha256=digest(Path(__file__).with_name('Profile.lean')),
            script_sha256=digest(Path(__file__)), current_source_sha256={p: digest(ROOT/p) for p in pins},
            commands=commands, cases=cases)
        if args.producer_state == 'committed':
            producer_paths = ['src/frontend/sized/'+name+'.rs' for name in ('lower', 'fourier', 'qpe')]
            report['original_producer_source_sha256'] = {
                p: hashlib.sha256(subprocess.check_output(
                    ['git', 'show', producer_commit+':'+p], cwd=ROOT)).hexdigest()
                for p in producer_paths}
    args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({name: case['service'] for name, case in cases.items()}))


if __name__ == '__main__':
    main()
