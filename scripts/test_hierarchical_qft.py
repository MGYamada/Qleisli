#!/usr/bin/env python3
"""Actual QFT hierarchy authoring and independent Fourier diagnostics.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
No algorithm name or floating-point oracle issues acceptance evidence.
"""
import argparse
import cmath
import copy
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def text(value):
    return json.dumps(value, separators=(',', ':'), sort_keys=True)


def port(owner, axes, bit=False):
    axes = list(axes)
    return dict(owner=owner, axes=axes,
                basis=[dict(tag='bit') if bit else dict(tag='bits', width=len(axes))])


def side(ports):
    return dict(quantum=ports, classical=[])


def wires(ports):
    return [axis for p in ports for axis in p['axes']]


def hadamard_program(owner, output, axis):
    return text(dict(format='qleisli.finite-ir', version=2, profile='finite-meaning-v1',
        sources=[], evidence=[], root=0,
        root_interface=dict(input=dict(tag='bit'), output=dict(tag='bit')),
        programs=[dict(quantum_inputs=[dict(token=owner, wires=[axis], shape=dict(bits=1))],
            quantum_outputs=[output], classical_inputs=[], classical_outputs=[],
            declared_effect='unitary',
            operations=[dict(tag='gate', gate='h', input=owner, output=output)])]))


def hadamard_matrix():
    entries = []
    for sign in [1, 1, 1, -1]:
        entries.append([dict(numerator=str(sign if i == 1 else 0),
                             denominator_bits=1 if i == 1 else 0) for i in range(4)])
    return text(dict(format='qleisli.finite-matrix', version=1, domain='zeta8-dyadic-v1',
                     rows=2, cols=2, entries=entries))


class Circuit:
    def __init__(self):
        self.definitions, self.meanings, self.encodings, self.proofs = [], [], [], []
        self.cache = {}
        self.encoding_cache = {}

    def encoding(self, ports):
        value = side(ports)
        key = text(value)
        if key not in self.encoding_cache:
            self.encoding_cache[key] = len(self.encodings)
            self.encodings.append(dict(logical=value, physical=value, body=dict(tag='identity')))
        return self.encoding_cache[key]

    def add(self, before, after, body, meaning, rule, premises=()):
        header = dict(inputs=side(before), outputs=side(after))
        key = text([header, body, meaning, rule, list(premises)])
        if key in self.cache:
            return self.cache[key]
        index = len(self.definitions)
        self.cache[key] = index
        self.definitions.append(dict(interface=header, effect='unitary', body=body))
        self.meanings.append(dict(interface=header, body=meaning))
        self.proofs.append(dict(kind='equation', rule=dict(tag=rule), premises=list(premises),
            implementation=index, meaning=index, input_encoding=self.encoding(before),
            output_encoding=self.encoding(after),
            witness=dict(template_version=1, parameters=[], references=[])))
        return index

    def ends(self, index):
        h = self.definitions[index]['interface']
        return h['inputs']['quantum'], h['outputs']['quantum']

    def rewire(self, before, after, owners=None, axes=None):
        owners = list(range(len(before))) if owners is None else owners
        axes = list(range(len(wires(before)))) if axes is None else axes
        body = dict(tag='rewire', permutation=dict(owners=owners, axes=axes, classical=[]))
        return self.add(before, after, body, body, 'rewire')

    def identity(self, ports):
        return self.rewire(ports, ports)

    def structural(self, before, after, tag, width, position):
        body = dict(tag='structural', operation=dict(tag=tag, width=width, position=position))
        return self.add(before, after, body, body, 'structural')

    def sequence(self, children):
        for first, second in zip(children, children[1:]):
            assert self.ends(first)[1] == self.ends(second)[0]
        body = dict(tag='sequence', children=children)
        return self.add(self.ends(children[0])[0], self.ends(children[-1])[1],
                        body, body, 'sequence', children)

    def tensor(self, first, second):
        a, b = self.ends(first)
        c, d = self.ends(second)
        body = dict(tag='tensor', left=first, right=second)
        return self.add(a+c, b+d, body, body, 'tensor', [first, second])

    def h(self, p):
        output = port(5, p['axes'], True)
        leaf = self.add([p], [output],
            dict(tag='leaf', program=hadamard_program(p['owner'], 5, p['axes'][0])),
            dict(tag='finite', description=hadamard_matrix()), 'finite')
        return self.sequence([leaf, self.rewire([output], [p])])

    def lifted(self, width, target, control=None, swap_bits=False):
        register = [port(0, range(width))]
        t = port(1, [target], True)
        rest = port(2, [x for x in range(width) if x != target])
        take = self.structural(register, [t, rest], 'take_bit', width, target)
        put = self.structural([t, rest], register, 'put_bit', width, target)
        if control is None:
            middle = self.tensor(self.h(t), self.identity([rest]))
        else:
            c = port(3, [control], True)
            residual = port(4, [x for x in rest['axes'] if x != control])
            position = rest['axes'].index(control)
            split = self.structural([rest], [c, residual], 'take_bit', width-1, position)
            join = self.structural([c, residual], [rest], 'put_bit', width-1, position)
            before, after = [t, c, residual], [c, t, residual]
            swap = [1, 0, *range(2, width)]
            if swap_bits:
                action = [self.rewire(before, before, [1, 0, 2], swap)]
            else:
                phase = self.add([t], [t], dict(tag='dyadic_phase', target=1, j=1, k=target-control+1),
                                 dict(tag='phase', j=1, k=target-control+1), 'phase')
                controlled = self.add([c, t], [c, t], dict(tag='control', definition=phase, polarity=True),
                                     dict(tag='control', child=phase, polarity=True), 'control', [phase])
                action = [self.rewire(before, after, [1, 0, 2], swap),
                          self.tensor(controlled, self.identity([residual])),
                          self.rewire(after, before, [1, 0, 2], swap)]
            middle = self.sequence([self.tensor(self.identity([t]), split), *action,
                                    self.tensor(self.identity([t]), join)])
        return self.sequence([take, middle, put])

    def qft(self, width):
        stages = []
        for target in reversed(range(width)):
            stages.append(self.lifted(width, target))
            for control in reversed(range(target)):
                stages.append(self.lifted(width, target, control))
        for low in range(width//2):
            stages.append(self.lifted(width, width-1-low, low, swap_bits=True))
        entry = self.sequence(stages)
        return dict(format='qleisli.hierarchical-ir', version=1, profile='qpe-dyadic8-v1',
            definitions=self.definitions, meanings=self.meanings, encodings=self.encodings,
            proofs=self.proofs, entry=dict(implementation=entry, proof=entry))


class SharedGradientCircuit(Circuit):
    """Keep recursive register boundaries and share phase gradients across stages.

    At fixed precision N, G_r multiplies |x> by exp(2*pi*i*x/2**N).
    A width-w QFT stage controls G_(w-1)**(2**(N-w)). This is an
    untrusted producer equation, checked diagnostically against the direct DFT;
    the kernel checks only the actual composition and its declared meaning.
    """
    def register(self, width):
        return port(200+width, range(width))

    def boundary(self, width):
        register = self.register(width)
        high = port(100+width-1, [width-1], True)
        rest = self.register(width-1)
        take = self.structural([register], [high,rest], 'take_bit', width, width-1)
        put = self.structural([high,rest], [register], 'put_bit', width, width-1)
        return high, rest, take, put

    def gradient(self, width):
        if width == 0:
            return self.identity([self.register(0)])
        high, _, take, put = self.boundary(width)
        exponent = self.precision-width+1
        phase = self.add([high], [high],
            dict(tag='dyadic_phase',target=high['owner'],j=1,k=exponent),
            dict(tag='phase',j=1,k=exponent), 'phase')
        return self.sequence([take, self.tensor(phase,self.gradient(width-1)), put])

    def recursive(self, width):
        if width == 0:
            return self.identity([self.register(0)])
        high, rest, take, put = self.boundary(width)
        stages = [take,self.tensor(self.h(high), self.identity([rest]))]
        if width > 1:
            gradient = self.gradient(width-1)
            count = 1 << (self.precision-width)
            if count > 1:
                gradient = self.add([rest],[rest],
                    dict(tag='repeat',definition=gradient,count=count),
                    dict(tag='power',child=gradient,count=count),'repeat',[gradient])
            stages.append(self.add([high,rest],[high,rest],
                dict(tag='control',definition=gradient,polarity=True),
                dict(tag='control',child=gradient,polarity=True),'control',[gradient]))
        stages += [self.tensor(self.identity([high]),self.recursive(width-1)),put]
        return self.sequence(stages)

    def qft(self, width):
        self.precision = width
        outer = [port(0,range(width))]
        inner = [self.register(width)]
        stages = [self.rewire(outer,inner),self.recursive(width),self.rewire(inner,outer)]
        for low in range(width//2):
            stages.append(self.lifted(width,width-1-low,low,swap_bits=True))
        entry = self.sequence(stages)
        return dict(format='qleisli.hierarchical-ir',version=1,profile='qpe-dyadic8-v1',
            definitions=self.definitions,meanings=self.meanings,encodings=self.encodings,
            proofs=self.proofs,entry=dict(implementation=entry,proof=entry))


def execute(artifact, index, amplitude):
    """Diagnostic interpretation of actual bodies, without reading proof/meaning tables."""
    d = artifact['definitions'][index]
    body, tag = d['body'], d['body']['tag']
    before = d['interface']['inputs']['quantum']
    after = d['interface']['outputs']['quantum']
    assert len(amplitude) == 1 << len(wires(before))
    if tag == 'leaf':
        packet = json.loads(body['program'])
        operations = packet['programs'][packet['root']]['operations']
        assert len(operations) == 1 and operations[0]['tag'] == 'gate' and len(amplitude) == 2
        if operations[0]['gate'] == 'h':
            a,b = amplitude
            return [(a+b)/math.sqrt(2), (a-b)/math.sqrt(2)]
        assert operations[0]['gate'] == 'x'
        return list(reversed(amplitude))
    if tag in ('rewire', 'structural'):
        source = wires(before)
        axes = (body['permutation']['axes'] if tag == 'rewire'
                else [source.index(w) for w in wires(after)])
        result = [0j]*len(amplitude)
        for original, value in enumerate(amplitude):
            output = sum(((original >> axis) & 1) << i for i,axis in enumerate(axes))
            result[output] = value
        return result
    if tag == 'sequence':
        for child in body['children']:
            amplitude = execute(artifact, child, amplitude)
        return amplitude
    if tag == 'repeat':
        for _ in range(body['count']):
            amplitude = execute(artifact, body['definition'], amplitude)
        return amplitude
    if tag == 'tensor':
        child = artifact['definitions'][body['left']]
        low = 1 << len(wires(child['interface']['inputs']['quantum']))
        high = len(amplitude)//low
        middle = []
        for i in range(high):
            middle.extend(execute(artifact, body['left'], amplitude[i*low:(i+1)*low]))
        result = [0j]*len(amplitude)
        for i in range(low):
            column = execute(artifact, body['right'], middle[i::low])
            result[i::low] = column
        return result
    if tag == 'control':
        result = list(amplitude)
        bit = int(body['polarity'])
        result[bit::2] = execute(artifact, body['definition'], amplitude[bit::2])
        return result
    if tag == 'dyadic_phase':
        axis = sum(len(p['axes']) for p in before[:next(i for i,p in enumerate(before)
                                                      if p['owner'] == body['target'])])
        phase = cmath.exp(2j*math.pi*body['j']/(1 << body['k']))
        return [value*phase if (i >> axis)&1 else value for i,value in enumerate(amplitude)]
    raise AssertionError(tag)


def fourier(amplitude):
    """Direct mathematical formula, independent of circuit/stage generation."""
    size = len(amplitude)
    return [sum(value*cmath.exp(2j*math.pi*x*y/size) for x,value in enumerate(amplitude))/math.sqrt(size)
            for y in range(size)]


def semantic_probes(artifacts):
    reports = []
    for width, artifact in artifacts.items():
        size = 1 << width
        basis = range(size) if width <= 4 else [0,1,3,(size//4)+1,size//2,size-1]
        vectors = [[complex(i == x) for i in range(size)] for x in basis]
        # Two columns of a normalized joint state with a reference bit. They
        # are retained as complex amplitudes rather than measured probabilities.
        columns = [[complex(((i+2*r)%7)-3, ((3*i+r)%5)-2) for i in range(size)] for r in range(2)]
        norm = math.sqrt(sum(abs(x)**2 for col in columns for x in col))
        vectors += [[x/norm for x in col] for col in columns]
        errors = []
        for vector in vectors:
            observed = execute(artifact, artifact['entry']['implementation'], vector)
            errors.append(max(abs(a-b) for a,b in zip(observed, fourier(vector))))
        assert max(errors) < 1e-10, (width, errors)
        faults = []
        for fault in ['wrong-h', 'wrong-phase', 'missing-reversal', 'wrong-polarity', 'wrong-repeat']:
            bad = copy.deepcopy(artifact)
            matched = False
            for index, definition in enumerate(bad['definitions']):
                b = definition['body']
                if fault == 'wrong-h' and b['tag'] == 'leaf':
                    packet = json.loads(b['program'])
                    packet['programs'][packet['root']]['operations'][0]['gate'] = 'x'
                    b['program'] = text(packet)
                    matched = True
                elif fault == 'wrong-phase' and b['tag'] == 'dyadic_phase':
                    b['j'] = 2
                    bad['meanings'][index]['body']['j'] = 2
                    matched = True
                elif fault == 'wrong-polarity' and b['tag'] == 'control':
                    b['polarity'] = False
                    bad['meanings'][index]['body']['polarity'] = False
                    matched = True
                elif fault == 'wrong-repeat' and b['tag'] == 'repeat':
                    b['count'] -= 1
                    bad['meanings'][index]['body']['count'] -= 1
                    matched = True
                elif fault == 'missing-reversal' and b['tag'] == 'rewire' and (
                        definition['interface']['inputs'] == definition['interface']['outputs'] and
                        b['permutation']['owners'] == [1,0,2]):
                    b['permutation']['owners'] = [0,1,2]
                    b['permutation']['axes'] = list(range(width))
                    bad['meanings'][index]['body'] = copy.deepcopy(b)
                    matched = True
                if matched:
                    break
            if matched:
                differences = [max(abs(a-b) for a,b in zip(
                    execute(bad,bad['entry']['implementation'],v),fourier(v))) for v in vectors]
                assert max(differences) > 1e-5, (width,fault,differences)
                faults.append(fault)
        reports.append(dict(width=width,vectors=len(vectors),maximum_error=max(errors),detected_faults=faults))
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    parser.add_argument('--construction', choices=['lifted','shared-gradient'], default='lifted')
    args = parser.parse_args()
    shared = args.construction == 'shared-gradient'
    builder = SharedGradientCircuit if shared else Circuit
    artifacts = {n: builder().qft(n) for n in (range(1,9) if shared else [1,2,3,4,8])}
    semantic = semantic_probes(artifacts)
    kernel = ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel'
    with tempfile.TemporaryDirectory(prefix='qleisli-qft-hierarchy-') as directory:
        for width, artifact in artifacts.items():
            Path(directory, f'qft-{width}.json').write_text(text(artifact))
            header = dict(inputs=side([port(0,range(width))]),outputs=side([port(0,range(width))]))
            request = dict(format='qleisli.hierarchy-request', version=1, profile='qpe-dyadic8-v1',
                kind='equation',effect='unitary',interface=header,entry=0,
                meanings=[dict(interface=header,body=dict(tag='qft',width=width))])
            Path(directory,f'qft-request-{width}.json').write_text(text(request))
        for fault in ['layout','empty-owner','h','phase'] + (['repeat'] if shared else []):
            bad = copy.deepcopy(artifacts[1 if fault == 'empty-owner' else (3 if fault == 'repeat' else 2)])
            for d in bad['definitions']:
                b = d['body']
                if fault == 'layout' and b['tag'] == 'structural' and b['operation']['tag'] == 'take_bit':
                    b['operation']['position'] = 1-b['operation']['position']
                    break
                if fault == 'empty-owner' and b['tag'] == 'structural' and b['operation']['tag'] == 'take_bit':
                    outputs = d['interface']['outputs']['quantum']
                    outputs[1]['owner'] = outputs[0]['owner']
                    break
                if fault == 'h' and b['tag'] == 'leaf':
                    packet = json.loads(b['program'])
                    packet['programs'][packet['root']]['operations'][0]['gate'] = 'x'
                    b['program'] = text(packet)
                    break
                if fault == 'phase' and b['tag'] == 'dyadic_phase':
                    b['j'] = 2
                    break
                if fault == 'repeat' and b['tag'] == 'repeat':
                    b['count'] -= 1
                    break
            Path(directory,f'invalid-{fault}.json').write_text(text(bad))
        env = os.environ.copy()
        env['QLEISLI_HIERARCHY_KERNEL'] = str(kernel)
        env['QLEISLI_QFT_FIXTURES'] = directory
        env['QLEISLI_QFT_CONSTRUCTION'] = args.construction
        result = subprocess.run(['cargo', 'test', '--test', 'qft_hierarchy', 'inspect_authored_qft_hierarchies', '--', '--ignored', '--nocapture'],
                                cwd=ROOT, env=env, capture_output=True, text=True, timeout=120)
    observed = [line.split('|')[1:] for line in result.stdout.splitlines() if line.startswith('QFT|')]
    assert [int(row[0]) for row in observed] == list(artifacts), result.stdout+result.stderr
    report = dict(format='qleisli.qft-hierarchy-authoring', version=1,
        construction=args.construction,
        kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest(),
        status=('partial-profile' if any(row[1] == 'limit' for row in observed) else 'checked-structure')
               if result.returncode == 0 else 'error', results=observed,
        semantic_probes=semantic,
        native_faults=[line.split('|')[1:] for line in result.stdout.splitlines() if line.startswith('FAULT|')],
        artifact_sha256={str(n): hashlib.sha256(text(a).encode()).hexdigest() for n,a in artifacts.items()},
        definition_counts={str(n): len(a['definitions']) for n,a in artifacts.items()},
        stdout=result.stdout, stderr=result.stderr)
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('stdout','stderr')}))
    return result.returncode


if __name__ == '__main__':
    raise SystemExit(main())
