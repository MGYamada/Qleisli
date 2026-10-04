#!/usr/bin/env python3
"""Independent native VM-27 request tests, without the Rust matrix reader.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Original QIRF leaf reconstruction and request equality both run natively.
"""
import copy
import json
from pathlib import Path
import struct
import subprocess
import tomllib

ROOT = Path(__file__).resolve().parents[1]
PRODUCT_VERSION = tomllib.loads((ROOT / 'Cargo.toml').read_text())['package']['version']
BINARY = ROOT / "lean-kernel/.lake/build/bin/qleisli-kernel"


def words(*values):
    return struct.pack("<" + "I" * len(values), *values)


def block(data):
    return words(len(data)) + data


def packet(actual, required, program=None):
    if program is None:
        program = (ROOT / "tests/fixtures/verification_v022/finite/h.v2.qirf").read_bytes()
    # Boundaries come from the original fixture, never a checker/extractor.
    envelope = json.loads(program)
    raw = envelope['programs'][envelope['root']]
    def atoms(tree):
        if tree['tag'] == 'unit': return [0], 1
        if tree['tag'] == 'bit': return [1], 1
        children = [tree['left'], tree['right']] if tree['tag'] == 'pair' else tree['fields']
        converted = [atoms(child) for child in children]
        return [3, len(children), *(v for values, _ in converted for v in values)], 1 + sum(n for _, n in converted)
    encoded, count = atoms(envelope['root_interface']['input'])
    port = raw['quantum_inputs'][0]
    side = words(1, port['token'], count, *encoded, len(port['wires']), *port['wires'], 0)
    output_wires = port['wires']
    if raw['operations'] and raw['operations'][-1]['tag'] == 'classical_branch':
        output_wires = raw['operations'][-1]['quantum_phis'][0]['output_wires']
    output = words(1, raw['quantum_outputs'][0], count, *encoded, len(output_wires), *output_wires, 0)
    interface = side + output
    definition = interface + words(0, 0) + block(program)
    meaning = interface + words(1) + block(actual)
    input_encoding = side + side + words(0)
    output_encoding = output + output + words(0)
    proof = words(0, 0, 0, 0, 0, 0, 1, 1, 0, 0)
    hierarchy = (b"QLH1" + words(1) + definition + words(1) + meaning +
                 words(2) + input_encoding + output_encoding + words(1) + proof +
                 words(0, 0, 5, 0, 1, 2, 3, 4))
    requested = interface + words(1) + block(required)
    return (b"QLR1" + block(hierarchy) + words(0, 0) + interface +
            words(1) + requested + words(0, 1, 0, 0, 0, 1, 0))


def main():
    matrix = json.loads((ROOT / "tests/fixtures/verification_v022/finite/h.matrix.json").read_bytes())
    encode = lambda value: json.dumps(value, separators=(",", ":")).encode()
    good = encode(matrix)
    phase = copy.deepcopy(matrix)
    for entry in phase["entries"]:
        for coefficient in entry:
            coefficient["numerator"] = str(-int(coefficient["numerator"]))
    malformed = copy.deepcopy(matrix)
    malformed["entries"][0][0]["numerator"] = "00"
    noncanonical = copy.deepcopy(matrix)
    noncanonical["entries"][0][1]["numerator"] = "2"
    noncanonical["entries"][0][1]["denominator_bits"] += 1
    cases = [
        ("exact", good, good, "pending"),
        ("phase", good, encode(phase), "contract"),
        ("invalid-actual", encode(malformed), good, "format"),
        ("invalid-required", good, encode(malformed), "format"),
        ("noncanonical", good, encode(noncanonical), "format"),
        ("duplicate-required", good, good.replace(b'{', b'{"version":1,', 1), "format"),
        ("utf8-required", good, b"\xff", "format"),
        ("trailing-required", good, good + b"false", "format"),
    ]
    for name, actual, required, expected in cases:
        result = subprocess.run([str(BINARY), "--hierarchy-request-pending", PRODUCT_VERSION],
                                input=packet(actual, required), capture_output=True, timeout=30)
        lines = result.stdout.decode().splitlines()
        assert lines[:1] == ["qleisli.hierarchy-request-pending 3"], (name, result)
        if expected == "pending":
            assert result.returncode == 0 and lines[1] == "pending", (name, lines)
            assert 36 < int(lines[3]) <= 10_000_000, (name, lines)
            assert lines[4:] == ["1", "0", "1", "0"], (name, lines)
        else:
            assert result.returncode == 1 and lines[1:] == ["error", expected], (name, lines)
    finite = ROOT / 'tests/fixtures/verification_v022/finite'
    native_cases = []
    for name in ('h','t','unit_phase','toffoli','raw_qif_unit','raw_computed_target'):
        description = (finite / f'{name}.matrix.json').read_bytes()
        for version in (1, 2):
            program = (finite / f'{name}.v{version}.qirf').read_bytes()
            native_cases.append((f'{name}-v{version}', program, description, 'pending'))
            native_cases.append((f'{name}-v{version}-phase', program,
                                 (finite / f'{name}.wrong-phase.json').read_bytes(), 'contract'))
    h = json.loads((finite / 'h.v2.qirf').read_bytes())
    def mutation(name, change, expected='format'):
        value = copy.deepcopy(h)
        change(value)
        native_cases.append((name, encode(value), good, expected))
    mutation('wrong-operation', lambda p:p['programs'][0]['operations'][0].update(gate='x'), 'contract')
    mutation('owner-reuse', lambda p:p['programs'][0]['operations'][0].update(output=0))
    mutation('effect-observe', lambda p:p['programs'][0].update(declared_effect='observe'), 'contract')
    mutation('unused-program', lambda p:p['programs'].append(copy.deepcopy(p['programs'][0])))
    mutation('source-unused', lambda p:p.update(sources=[dict(path='unused.qli',text='')]))
    mutation('source-duplicate', lambda p:p.update(sources=[dict(path='x',text=''),dict(path='x',text='')]))
    mutation('producer-flag', lambda p:p.update(checked=True))
    mutation('interface-shape', lambda p:p['root_interface'].update(output=dict(tag='unit')), 'contract')
    # Closed selection must not hide a bad owner in the unselected arm.
    branch = copy.deepcopy(h['programs'][0])
    gate = copy.deepcopy(branch['operations'][0])
    other = dict(gate,output=2)
    branch['operations'] = [dict(tag='classical_const',value=True,output=10),
        dict(tag='classical_branch',condition=10,then_ops=[gate],else_ops=[other],
             quantum_phis=[dict(then_token=1,else_token=2,output=3,output_wires=[19])],classical_phis=[])]
    branch['quantum_outputs'] = [3]
    closed = copy.deepcopy(h); closed['programs'] = [branch]
    native_cases.append(('closed-branch',encode(closed),good,'pending'))
    broken = copy.deepcopy(closed); broken['programs'][0]['operations'][1]['else_ops'][0]['output'] = 0
    native_cases.append(('unselected-invalid-arm',encode(broken),good,'format'))
    # Original QIRF IDs are deliberately not topological.
    root = copy.deepcopy(h['programs'][0])
    root['operations'] = [dict(tag='apply_unitary',input=0,output=1,
        steps=[dict(controls=[],action=dict(tag='contract',indices=[0],evidence=0,adjoint=False))])]
    identity = dict(implementation='h',specification='h',sources=[0])
    for version in (1, 2):
        graph = copy.deepcopy(h); graph.update(version=version,
            profile='finite-v0' if version==1 else 'finite-meaning-v1',
            programs=[root,h['programs'][0],h['programs'][0]],sources=[dict(path='fixture.qli',text='h(q)')],
            evidence=[dict(signature=dict(tag='bit'),implementation=1,specification=2,identity=identity)])
        if version == 2: graph['evidence'][0]['tag']='circuit'
        native_cases.append((f'circuit-graph-v{version}',encode(graph),good,'pending'))
        unused = copy.deepcopy(graph); unused['sources'].append(dict(path='unused.qli',text=''))
        native_cases.append((f'unused-source-v{version}',encode(unused),good,'format'))
        cycle = copy.deepcopy(graph); cycle['evidence'][0]['implementation']=0
        native_cases.append((f'cycle-v{version}',encode(cycle),good,'format'))
        fault = copy.deepcopy(graph); fault['programs'][2]['operations'][0]['gate']='x'
        native_cases.append((f'false-receipt-v{version}',encode(fault),good,'contract'))
        bad_source = copy.deepcopy(graph); bad_source['evidence'][0]['identity']['sources']=[99999]
        native_cases.append((f'identity-source-v{version}',encode(bad_source),good,'format'))
    t = json.loads((finite / 't.v2.qirf').read_bytes())
    tdesc = (finite / 't.matrix.json').read_bytes()
    middle = copy.deepcopy(root); middle['operations'][0]['steps'][0]['action']['evidence']=1
    meaning = copy.deepcopy(t); meaning.update(programs=[root,middle,t['programs'][0]],
        evidence=[dict(tag='meaning',signature=dict(tag='bit'),implementation=i,
                       meaning=dict(tag='phase8',table=[0,1]),identity=dict(identity,sources=[])) for i in (1,2)])
    native_cases.append(('meaning-nontopological',encode(meaning),tdesc,'pending'))
    wrong = copy.deepcopy(meaning); wrong['evidence'][1]['meaning']['table']=[0,2]
    native_cases.append(('false-meaning',encode(wrong),tdesc,'contract'))
    adjoint = copy.deepcopy(meaning)
    adjoint['programs'][0]['operations'][0]['steps'][0]['action']['adjoint']=True
    adjoint_matrix = json.loads(tdesc)
    for entry in adjoint_matrix['entries']:
        for coefficient in entry[2:]: coefficient['numerator']=str(-int(coefficient['numerator']))
    native_cases.append(('meaning-adjoint',encode(adjoint),encode(adjoint_matrix),'pending'))
    permutation = copy.deepcopy(h)
    x = copy.deepcopy(h['programs'][0]); x['operations'][0]['gate']='x'
    permutation.update(programs=[root,x],evidence=[dict(tag='meaning',signature=dict(tag='bit'),implementation=1,
        meaning=dict(tag='permutation',table=[1,0]),identity=dict(identity,sources=[]))])
    x_matrix = copy.deepcopy(matrix)
    x_matrix['entries']=[[dict(numerator=str(int(k in (1,2) and j==0)),denominator_bits=0)
                           for j in range(4)] for k in range(4)]
    native_cases.append(('meaning-permutation',encode(permutation),encode(x_matrix),'pending'))
    for name, program, description, expected in native_cases:
        result = subprocess.run([str(BINARY), '--hierarchy-request-pending', PRODUCT_VERSION],
            input=packet(description, description, program), capture_output=True, timeout=30)
        lines = result.stdout.decode().splitlines()
        assert lines[0] == 'qleisli.hierarchy-request-pending 3', (name, result)
        if expected == 'pending':
            assert result.returncode == 0 and lines[1] == 'pending', (name, lines)
            assert 0 < int(lines[3]) <= 10_000_000, (name, lines)
        else:
            assert result.returncode == 1 and lines[1:] == ['error',expected], (name, lines)
    # Text-only decoder faults retain a separately valid enclosing boundary.
    for name, program in [('duplicate',encode(h).replace(b'{',b'{"version":2,',1)),
                          ('leading-zero',encode(h).replace(b'"root":0',b'"root":00')),
                          ('trailing',encode(h)+b'false'),('invalid-utf8',b'\xff')]:
        original = packet(good, good)
        old = (finite / 'h.v2.qirf').read_bytes()
        original = original.replace(block(old),block(program))
        # The QLR enclosing block length changes with the exact nested bytes.
        old_size = struct.unpack_from('<I',original,4)[0]
        original = original[:4]+words(old_size+len(program)-len(old))+original[8:]
        result = subprocess.run([str(BINARY),'--hierarchy-request-pending',PRODUCT_VERSION],input=original,
                                capture_output=True,timeout=30)
        assert result.returncode == 1 and result.stdout.decode().splitlines()[1:] == ['error','format'], (name,result)
    print(f'Passed {len(cases)+len(native_cases)+4} native QIRF/request cases; Rust checker not invoked.')


if __name__ == "__main__":
    main()
