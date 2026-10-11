"""Untrusted private transport for the initialization/readout component checks.
No Boolean result from this adapter is a whole-instrument evidence handle.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import struct
import subprocess


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


def inspect(kernel, kind, payload):
    if kind not in ('preparation', 'readout'):
        raise ValueError('unknown component')
    run = subprocess.run([str(kernel), f'--{kind}-check'], input=payload,
                         capture_output=True, timeout=60)
    fields = run.stdout.decode('ascii').splitlines()
    if len(fields) != 3 or fields[0] != f'qleisli.{kind}-result 1':
        raise ValueError('malformed component response')
    if fields[1] == 'checked' and run.returncode == 0 and fields[2].isascii() and fields[2].isdecimal():
        work = int(fields[2])
        if not 0 <= work <= 2000000:
            raise ValueError('component work out of range')
        return dict(status='checked', work=work)
    if fields[1] == 'error' and run.returncode == 1 and fields[2] in ('format', 'limit', 'contract', 'invalid_ir'):
        return dict(status=fields[2])
    raise ValueError('inconsistent component response')
