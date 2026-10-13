"""QLV2 framing for explicit native inspection and comparison harnesses.
This adapter supplies data only, never acceptance or an execution handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import struct


def envelope(original, graph=b'', caller=b'', indices=()):
    scope = 2 if caller else 1 if graph else 0
    if not original or (caller and not graph) or (indices and not caller):
        raise ValueError('incomplete native envelope')
    if len(indices) > 100000 or len(graph) + len(caller) > 64 << 20:
        raise ValueError('native view limits')
    size = 24 + len(original) + len(graph) + len(caller) + 4 * len(indices)
    if size > 64 << 20:
        raise ValueError('native envelope limit')
    return (b'QLV2' + struct.pack('<5I', scope, len(original), len(graph), len(caller), len(indices))
            + original + graph + caller + b''.join(struct.pack('<I', i) for i in indices))


def inspection_lines(output):
    """Assert the new scope before reusing per-profile field assertions."""
    lines = output.decode('ascii').splitlines()
    if len(lines) >= 2 and lines[1] in ('accepted', 'pending'):
        assert len(lines) >= 3 and lines[2] == 'inspection', lines
        return lines[:2] + lines[3:]
    return lines
