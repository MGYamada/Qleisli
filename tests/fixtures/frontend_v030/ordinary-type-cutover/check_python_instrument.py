#!/usr/bin/env python3
"""Bounded canonical-source producer checks, without Cargo or new artifacts."""
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / 'scripts'))
from compile_sized_corpus import SourceError
from test_sized_instrument import sources, compile_instrument, qpe, components, probes, source_rejections


def main():
    modules = sources()
    kernel = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
    expected_kernel = json.loads((ROOT / 'tests/fixtures/frontend_v030/ordinary-types-independent/after/validation.json').read_text())['executables'][str(kernel)]
    assert hashlib.sha256(kernel.read_bytes()).hexdigest() == expected_kernel
    proposal = qpe(modules, 1, 1, 1, 3)
    validity = components(proposal, kernel)
    action = probes(proposal, 1, 1, 1, 3, 'qpe')
    assert action['maximum_error'] < 1e-10, action
    rejected = source_rejections(modules)
    assert '-> Bits<n>' in modules['readout']
    obsolete = modules | {'readout': modules['readout'].replace('-> Bits<n>', '-> CBits<n>')}
    try:
        compile_instrument(obsolete, 'readout::measure_bits', {'n': 1})
    except SourceError:
        pass
    else:
        raise AssertionError('obsolete classical type spelling was accepted')
    print(json.dumps({'scope': 'Small two-qubit Python source proposal, independent numerical QPE action and actual native preparation/readout component checks. Hierarchy graph acceptance, whole-instrument/source preservation and full Python/Rust bridge replay are not claimed.', 'source_sha256': {k: hashlib.sha256(v.encode()).hexdigest() for k, v in modules.items()}, 'kernel_sha256': expected_kernel, 'components': validity, 'semantics': action, 'negative_sources': rejected, 'obsolete_classical_spelling_rejected': True}, indent=2))


if __name__ == '__main__':
    main()
