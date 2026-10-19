"""QLV3 framing for explicitly selected native test/packaging contexts.
This adapter supplies data only, never acceptance or an execution handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
from dataclasses import dataclass
import struct


def envelope(edition, original, graph=b'', caller=b'', indices=()):
    if edition != '2026':
        raise ValueError('select the supported constitutional edition explicitly: 2026')
    scope = 2 if caller else 1 if graph else 0
    if not original or (caller and not graph) or (indices and not caller):
        raise ValueError('incomplete native envelope')
    if len(indices) > 100000 or len(graph) + len(caller) > 64 << 20:
        raise ValueError('native view limits')
    size = 28 + len(original) + len(graph) + len(caller) + 4 * len(indices)
    if size > 64 << 20:
        raise ValueError('native envelope limit')
    return (b'QLV3' + struct.pack('<6I', 2026, scope, len(original), len(graph), len(caller), len(indices))
            + original + graph + caller + b''.join(struct.pack('<I', i) for i in indices))


MODES = {
    '--qirf-native': ('accepted', ('inspection', 'execution', 'caller')),
    '--qirf-contract': ('accepted', ('inspection', 'execution', 'caller')),
    '--hierarchy-pending': ('pending', ('inspection', 'execution')),
    '--hierarchy-request-pending': ('pending', ('inspection', 'execution')),
    '--hierarchy-fourier-pending': ('pending', ('inspection', 'execution')),
    '--instrument-pending': ('pending', ('inspection', 'execution')),
    '--qpe-instrument-pending': ('pending', ('inspection', 'execution')),
    '--engineering-pure-check': ('engineering-checked', ('execution',)),
    '--engineering-pure-tensor-check': ('engineering-checked', ('execution',)),
    '--qirf-engineering-instrument-native': ('engineering-checked', ('execution',)),
    '--engineering-openqasm-check': ('engineering-checked', ('execution',)),
    '--readout-check': ('checked', ('inspection',)),
    '--preparation-check': ('checked', ('inspection',)),
}
ERRORS = frozenset(('format', 'limit', 'contract', 'invalid_ir', 'decoded_view', 'version', 'edition'))


@dataclass(frozen=True)
class Context:
    edition: str
    product: str
    mode: str
    scope: str


@dataclass(frozen=True)
class Reply:
    claim: str
    context: Context | None
    payload: tuple[str, ...]

    @property
    def error(self):
        return self.payload[0] if self.claim == 'error' else None


def parse_reply(output, *, edition, product, mode, scope):
    """Match the actual current context; each consumer must check its full payload.

    Errors assert no successful context. Old replies are never translated.
    """
    if edition != '2026' or not product or mode not in MODES or scope not in ('inspection', 'execution', 'caller'):
        raise ValueError('invalid explicit native invocation context')
    fields = output.decode('ascii').split('\n')
    if fields[:1] != ['qleisli.native-result 3']:
        raise ValueError('unknown native response protocol')
    if len(fields) == 4 and fields[1] == 'error' and fields[2] in ERRORS and fields[3] == '':
        return Reply('error', None, (fields[2],))
    claim, scopes = MODES[mode]
    if (len(fields) < 8 or fields[-1] != '' or scope not in scopes
            or fields[1:6] != [claim, edition, product, mode, scope]):
        raise ValueError('native reply context disagrees with the invocation')
    payload = tuple(fields[6:-1])
    if any(not value.isascii() or not value.isdecimal() or len(value) > 10
           or len(value) > 1 and value.startswith('0') for value in payload):
        raise ValueError('noncanonical native payload integer')
    return Reply(claim, Context(edition, product, mode, scope), payload)
