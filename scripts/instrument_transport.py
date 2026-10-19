"""Untrusted private transport for the initialization/readout component checks.
No Boolean result from this adapter is a whole-instrument evidence handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import struct
import subprocess
from pathlib import Path
import tomllib
from native_packet import envelope, parse_reply


ROOT = Path(__file__).resolve().parents[1]
PRODUCT_VERSION = tomllib.loads((ROOT / 'Cargo.toml').read_text())['package']['version']


class Writer:
    def __init__(self, magic):
        self.data = bytearray(magic)

    def word(self, n):
        if type(n) is not int or not 0 <= n < 2**32:
            raise ValueError('private instrument transport u32 range')
        self.data.extend(struct.pack('<I', n))

    def array(self, values, write):
        self.word(len(values))
        for value in values:
            write(value)

    def basis(self, atoms):
        def atom(value):
            tag = value['tag']
            self.word({'unit': 0, 'bit': 1, 'bits': 2, 'tuple': 3}[tag])
            if tag in ('bits', 'tuple'):
                self.word(value['width' if tag == 'bits' else 'arity'])
        self.array(atoms, atom)

    def side(self, value):
        def quantum(p):
            self.word(p['owner']); self.basis(p['basis']); self.array(p['axes'], self.word)
        def classical(p):
            self.word(p['value']); self.basis(p['basis'])
        self.array(value['quantum'], quantum)
        self.array(value['classical'], classical)

    def definition(self, value):
        self.side(value['interface']['inputs']); self.side(value['interface']['outputs'])
        self.word({'unitary': 0, 'iso': 1, 'observe': 2}[value['effect']])
        body = value['body']
        if body['tag'] == 'init0':
            self.word(12); self.word(body['output'])
        elif body['tag'] == 'observe_z':
            self.word(11); self.word(body['input']); self.word(body['output'])
        else:
            raise ValueError('unsupported component body; no silent substitution')


def encode_preparation(request, packet, budget=2000000):
    writer = Writer(b'QLZ1')
    writer.side(request['inputs'])
    writer.side(dict(quantum=request['fresh'], classical=[]))
    writer.array(packet['initializations'], writer.definition)
    writer.side(packet['outputs'])
    writer.word(budget)
    return bytes(writer.data)


def encode_readout(request, packet, budget=2000000):
    writer = Writer(b'QLM1')
    writer.side(request['inputs']); writer.array(request['owners'], writer.word); writer.word(request['result'])
    writer.array(packet['measurements'], writer.definition); writer.array(packet['pack'], writer.word)
    writer.side(packet['outputs']); writer.word(budget)
    return bytes(writer.data)


def inspect(kernel, kind, payload, *, edition):
    if kind not in ('preparation', 'readout'):
        raise ValueError('unknown component')
    return inspect_envelope(kernel, kind, envelope(edition, payload), edition=edition)


def inspect_envelope(kernel, kind, packet, *, edition):
    """Send explicit outer bytes, including deliberately malformed test inputs."""
    if kind not in ('preparation', 'readout'):
        raise ValueError('unknown component')
    run = subprocess.run([str(kernel), f'--{kind}-check', PRODUCT_VERSION], input=packet,
                         capture_output=True, timeout=60)
    reply = parse_reply(run.stdout, edition=edition, product=PRODUCT_VERSION,
                        mode=f'--{kind}-check', scope='inspection')
    if reply.claim == 'checked' and run.returncode == 0 and len(reply.payload) == 1:
        work = int(reply.payload[0])
        if not 0 <= work <= 2000000:
            raise ValueError('component work out of range')
        return dict(status='checked', work=work)
    if reply.error is not None and run.returncode == 1:
        return dict(status=reply.error)
    raise ValueError('inconsistent component response')
