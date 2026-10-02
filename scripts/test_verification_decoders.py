#!/usr/bin/env python3
"""VM-27 lossless decoder correspondence across original fields and constructors.
Test-only views run the actual Lean readers, independently of acceptance.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

import test_lean_observation as observing

ROOT = Path(__file__).resolve().parents[1]
VIEW = ROOT / 'tests/fixtures/verification_v027/DecoderView.lean'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def atoms(tree):
    if tree['tag'] in ('unit', 'bit'):
        return [tree]
    children = [tree['left'], tree['right']] if tree['tag'] == 'pair' else tree['fields']
    return [dict(tag='tuple', arity=len(children))] + [a for child in children for a in atoms(child)]


def qirf_view(value):
    result = {key: copy.deepcopy(value[key]) for key in ('programs', 'sources', 'root', 'root_interface')}
    if result['root_interface'] is not None:
        result['root_interface'] = {key: atoms(tree) for key, tree in result['root_interface'].items()}
    result['evidence'] = []
    for entry in value['evidence']:
        target = dict(tag='circuit', program=entry['specification']) if entry.get('tag', 'circuit') == 'circuit' else entry['meaning']
        result['evidence'].append(dict(signature=atoms(entry['signature']), implementation=entry['implementation'],
                                      target=target, identity=entry['identity']))
    return result


def qirf_cases():
    cases = []
    seen = set()
    for case in observing.cases():
        program = case['artifact']['program']
        if 'accepted' in program or sum(p['shape']['bits'] for p in program['quantum_inputs']) > 3:
            continue
        def tags(operations):
            for op in operations:
                seen.add(op['tag'])
                if op['tag'] == 'classical_branch':
                    tags(op['then_ops']); tags(op['else_ops'])
        tags(program['operations'])
        for version in (1, 2):
            artifact = dict(format='qleisli.finite-ir', version=version,
                profile='finite-v0' if version == 1 else 'finite-meaning-v1', sources=[],
                programs=[program], evidence=[], root=0, root_interface=None)
            cases.append((case['name'] + f'-v{version}', artifact))
    assert len(seen) == 19, seen
    fixture = ROOT / 'tests/fixtures/verification_v022/finite'
    for path in sorted(fixture.glob('*.qirf')):
        cases.append((path.name, json.loads(path.read_bytes())))
    sample = copy.deepcopy(cases[0][1])
    sample['root_interface'] = dict(input=dict(tag='pair', left=dict(tag='unit'), right=dict(tag='bit')),
        output=dict(tag='tuple', fields=[dict(tag='bit'), dict(tag='unit'), dict(tag='bit')]))
    sample['sources'] = [dict(path='a\\b\"c.qli', text='phase(\u03c0)\n\t\u0000'), dict(path='b.qli', text='second')]
    identity = dict(implementation='impl\u03bb', specification='spec\"', sources=[1, 0])
    for version in (1, 2):
        sample.update(version=version, profile='finite-v0' if version == 1 else 'finite-meaning-v1',
            evidence=[dict(signature=sample['root_interface']['input'], implementation=0, specification=0, identity=identity)])
        if version == 2: sample['evidence'][0]['tag'] = 'circuit'
        cases.append((f'shapes-identity-v{version}', copy.deepcopy(sample)))
    for tag in ('phase8', 'permutation'):
        sample['evidence'] = [dict(tag='meaning', signature=dict(tag='bit'), implementation=0,
                                  meaning=dict(tag=tag, table=[1, 0]), identity=identity)]
        cases.append((f'meaning-{tag}', copy.deepcopy(sample)))
    return cases, seen


def hierarchy_cases():
    basis = [dict(tag='tuple', arity=3), dict(tag='unit'), dict(tag='bit'), dict(tag='bits', width=0)]
    side = dict(quantum=[dict(owner=4294967295, basis=basis, axes=[37, 11])],
                classical=[dict(value=23, basis=[dict(tag='bits', width=2)])])
    interface = dict(inputs=side, outputs=dict(quantum=[dict(owner=31, basis=basis, axes=[11, 37])],
                                            classical=[dict(value=29, basis=[dict(tag='bits', width=2)])]))
    mapping = dict(owners=[1, 0], axes=[2, 0, 1], classical=[4, 3])
    structural = [dict(tag=tag, **(dict(width=3, position=1) if i < 2 else {})) for i, tag in enumerate(
        ('take_bit', 'put_bit', 'split_tuple', 'join_tuple', 'bit_to_bits', 'bits_to_bit',
         'pack_unit', 'unpack_unit', 'pack_empty_bits', 'unpack_empty_bits'))]
    bodies = [dict(tag='leaf', program='\u03bb\u0000\nraw'), dict(tag='sequence', children=[0, 0]), dict(tag='tensor', left=0, right=1),
        dict(tag='call', definition=2, input_map=mapping, output_map=dict(mapping, axes=[1, 0, 2])),
        dict(tag='repeat', count=7, definition=3), dict(tag='inverse', definition=4),
        dict(tag='control', definition=5, polarity=False), dict(tag='rewire', permutation=mapping),
        dict(tag='dyadic_phase', target=31, j=5, k=7), dict(tag='computed', compute=1, use=2, logical=0, encoding=0),
        dict(tag='observe_z', input=17, output=19), dict(tag='init0', output=41)]
    bodies += [dict(tag='structural', operation=op) for op in structural]
    meanings = [dict(tag='identity'), dict(tag='finite', description='\u03c0\u0000matrix'), dict(tag='sequence', children=[0, 1]),
        dict(tag='tensor', left=1, right=2), dict(tag='inverse', child=3), dict(tag='control', child=4, polarity=True),
        dict(tag='power', child=5, count=13), dict(tag='rewire', permutation=mapping), dict(tag='phase', j=3, k=5),
        dict(tag='qft', width=3), dict(tag='qpe_instrument', target=2, precision=3, provider_meaning=0)]
    meanings += [dict(tag='structural', operation=op) for op in structural]
    encodings = [dict(tag='identity'), dict(tag='tensor', left=0, right=0),
        dict(tag='rewire', child=1, permutation=mapping), dict(tag='zero_scratch', scratch_bits=2, compute=3)]
    rules = ('finite', 'sequence', 'tensor', 'inverse', 'control', 'repeat', 'associativity',
             'rewire', 'structural', 'phase', 'computed', 'conjugation')
    artifact = dict(format='qleisli.hierarchical-ir', version=1, profile='qpe-dyadic8-v1',
        definitions=[dict(interface=interface, effect=('unitary', 'iso', 'observe')[i % 3], body=b) for i, b in enumerate(bodies)],
        meanings=[dict(interface=interface, body=b) for b in meanings],
        encodings=[dict(logical=side, physical=interface['outputs'], body=b) for b in encodings],
        proofs=[dict(kind='equation' if i % 2 else 'instrument', rule=dict(tag=rule), premises=[] if i == 0 else [i-1],
            implementation=i, meaning=i, input_encoding=0, output_encoding=3,
            witness=dict(template_version=9, parameters=[0, 7, 4294967295],
                references=[dict(table=table, index=0) for table in ('definition', 'meaning', 'encoding')]))
            for i, rule in enumerate(rules)], entry=dict(implementation=len(bodies)-1, proof=len(rules)-1))
    # Include both polarities and nonempty proof-table references, with no cycle.
    artifact['proofs'][-1]['witness']['references'].append(dict(table='proof', index=0))
    changed = copy.deepcopy(artifact)
    changed['definitions'][6]['body']['polarity'] = True
    changed['meanings'][5]['body']['polarity'] = False
    changed['definitions'][4]['body']['count'] = 0
    changed['meanings'][6]['body']['count'] = 0
    return [('all-fields', artifact), ('polarity-zero-repeat', changed)]


def hierarchy_view(artifact):
    result = {key: copy.deepcopy(artifact[key]) for key in ('definitions', 'meanings', 'encodings', 'proofs', 'entry')}
    for d in result['definitions']:
        if d['body']['tag'] == 'leaf': d['body']['program'] = list(d['body']['program'].encode())
    for m in result['meanings']:
        if m['body']['tag'] == 'finite': m['body']['description'] = list(m['body']['description'].encode())
    return result


def run_command(command, cwd, log, env=None):
    result = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True, timeout=240)
    log.append(dict(command=command, exit_code=result.returncode, stdout=result.stdout, stderr=result.stderr))
    assert result.returncode == 0, log[-1]
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    log = []
    cases, constructors = qirf_cases()
    requests = [dict(kind='qirf', text=json.dumps(value, separators=(',', ':'))) for _, value in cases]
    expected = [qirf_view(value) for _, value in cases]
    names = [name for name, _ in cases]
    faults = []
    good = requests[0]['text']
    faults += [('duplicate-field', good.replace('{', '{"root":0,', 1)), ('leading-zero', good.replace('"root":0', '"root":00')),
               ('trailing', good+'false')]
    for name, text in faults:
        requests.append(dict(kind='qirf', text=text)); expected.append(None); names.append(name)
    for name, change in [('u32-owner', lambda p:p['quantum_inputs'][0].update(token=2**32)),
                         ('u8-shape', lambda p:p['quantum_inputs'][0]['shape'].update(bits=256)),
                         ('unknown-operation-field', lambda p:p['operations'][0].update(future=True))]:
        value = copy.deepcopy(cases[0][1]); change(value['programs'][0])
        requests.append(dict(kind='qirf', text=json.dumps(value))); expected.append(None); names.append(name)
    example = copy.deepcopy(cases[0][1])
    def raw_fault(name, operation):
        value = copy.deepcopy(example); value['programs'][0]['operations'] = [operation]
        requests.append(dict(kind='qirf', text=json.dumps(value))); expected.append(None); names.append(name)
    for field,value in [('target',2**32),('control',2**32),('permutation',65536),('phase',256),('evidence',2**32)]:
        action = dict(tag='hadamard',target=value) if field=='target' else (
            dict(tag='contract',indices=[0],evidence=value,adjoint=False) if field=='evidence' else
            dict(tag='monomial',indices=[0],permutation=[value if field=='permutation' else 0],phases=[value if field=='phase' else 0]))
        controls = [dict(index=value,when_one=False)] if field=='control' else []
        raw_fault('wire-bound-'+field,dict(tag='apply_unitary',input=0,output=1,steps=[dict(controls=controls,action=action)]))
    raw_fault('wire-bound-computed-function',dict(tag='certified_compute',source=0,source_out=1,
        ancilla_wires=[1],function=[65536],use_steps=[],logical_steps=[]))
    for tag,table in [('permutation',[65536]),('phase8',[256])]:
        value = copy.deepcopy(example); value.update(version=2,profile='finite-meaning-v1',
            evidence=[dict(tag='meaning',signature=dict(tag='bit'),implementation=0,meaning=dict(tag=tag,table=table),
                identity=dict(implementation='x',specification='y',sources=[]))])
        requests.append(dict(kind='qirf',text=json.dumps(value))); expected.append(None); names.append('wire-bound-meaning-'+tag)
    with tempfile.TemporaryDirectory(prefix='qleisli-decoder-audit-') as directory:
        project = Path(directory)
        for name, artifact in hierarchy_cases():
            (project/f'{name}.qirh').write_text(json.dumps(artifact))
        run_command(['cargo', 'test', '--lib', 'original_json_fields_survive_the_actual_rust_bridge', '--', '--ignored'],
                    ROOT, log, os.environ | {'QLEISLI_DECODER_AUDIT': str(project)})
        run_command(['cargo','test','--lib','every_frozen_raw_operation_and_action_preserves_its_fields'],
                    ROOT,log,os.environ | {'QLEISLI_DECODER_AUDIT':str(project)})
        for path in sorted(project.glob('*.raw.json')):
            operation = json.loads(path.read_bytes())
            version = 1 if '.v1.' in path.name else 2
            value = copy.deepcopy(example)
            value.update(version=version,profile='finite-v0' if version==1 else 'finite-meaning-v1')
            value['programs'][0]['operations']=[operation]
            requests.append(dict(kind='qirf',text=json.dumps(value))); expected.append(qirf_view(value)); names.append(path.name)
        for name, artifact in hierarchy_cases():
            original = (project/f'{name}.bridge').read_bytes()
            requests.append(dict(kind='hierarchy', bytes=list(original))); expected.append(hierarchy_view(artifact)); names.append(name)
            for suffix, data in [('truncated', original[:-1]), ('trailing', original+b'\x00')]:
                requests.append(dict(kind='hierarchy', bytes=list(data))); expected.append(None); names.append(name+'-'+suffix)
        (project/'lean-toolchain').write_text((ROOT/'lean-kernel/lean-toolchain').read_text())
        (project/'lakefile.toml').write_text('name="decoder_audit"\nversion="0.0.0"\ndefaultTargets=["decoder-audit"]\n'
            '[[require]]\nname="qleisli_kernel"\npath='+json.dumps(str(ROOT/'lean-kernel'))+'\n'
            '[[lean_exe]]\nname="decoder-audit"\nroot="Main"\n')
        (project/'Main.lean').write_bytes(VIEW.read_bytes())
        run_command(['lake', 'build'], project, log)
        binary = project/'.lake/build/bin/decoder-audit'
        payload = ''.join(json.dumps(value, separators=(',', ':'))+'\n' for value in requests)
        result = subprocess.run([str(binary)], input=payload, text=True, capture_output=True, timeout=120)
        assert result.returncode == 0, result.stderr
        outputs = [json.loads(line) for line in result.stdout.splitlines()]
        assert len(outputs) == len(expected)
        if args.record:
            failures=[]
            for name,value,wanted,request in zip(names,outputs,expected,requests):
                actual=copy.deepcopy(value.get('ok'))
                order=actual.pop('order',None) if isinstance(actual,dict) else None
                invalid_order=wanted is not None and order is not None and sorted(order)!=list(range(sum(
                    len(wanted[key]) for key in ('definitions','meanings','encodings','proofs'))))
                if (wanted is None and 'error' not in value) or (wanted is not None and
                        (actual!=wanted or invalid_order)):
                    failures.append(dict(name=name,input=request,actual=value,expected=wanted))
            if failures:
                args.record.write_text(json.dumps(dict(status='failed',failures=failures,
                    decoder_sha256=digest(VIEW),commands=log),indent=2)+'\n')
        for name, value, wanted in zip(names, outputs, expected):
            if wanted is None:
                assert 'error' in value, (name, value)
            else:
                actual = value['ok']
                if 'order' in actual:
                    order = actual.pop('order')
                    assert sorted(order) == list(range(sum(len(wanted[key]) for key in ('definitions','meanings','encodings','proofs'))))
                assert actual == wanted, (name, actual, wanted)
        report = dict(format='qleisli.vm27-decoder-correspondence', version=1, status='passed',
            cases=len(expected), raw_constructors=sorted(constructors), hierarchy_definitions=13,
            hierarchy_meanings=12, encodings=4, structural_constructors=10, enabled_rules=12,
            scope='lossless actual-reader field comparison; not a universal parser/compiler proof',
            production_authority='Rust', max_semantic_qubits=3,
            wire_range_regressions=[dict(name=name,input=request) for name,request in zip(names,requests)
                if name.startswith('wire-bound-')],
            source_sha256={str(path.relative_to(ROOT)):digest(path) for path in [VIEW, Path(__file__),
                ROOT/'src/interchange/hierarchical/bridge.rs', ROOT/'lean-kernel/Protocol/Hierarchical.lean',
                ROOT/'lean-kernel/Protocol/Qirf.lean', ROOT/'lean-kernel/Protocol/Observation.lean', ROOT/'lean-kernel/Protocol/Raw.lean']},
            binary_sha256=digest(binary), input_sha256=hashlib.sha256(payload.encode()).hexdigest(),
            output_sha256=hashlib.sha256(result.stdout.encode()).hexdigest(), commands=log)
        if args.record: args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(f'Passed {len(expected)} lossless decoder cases; all 19 raw and selected hierarchy variants.')


if __name__ == '__main__':
    main()
