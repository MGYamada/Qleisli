#!/usr/bin/env python3
"""Observe only the existing VM22 source_comparisons function; never its main.

The main entrypoint invokes Cargo and has no --source-only option. This driver
keeps the existing source function and frozen-byte comparisons intact, adding
only bounded records of its calls and any mismatch bytes. It never captures
or overwrites the historical VM22 fixtures.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts'))
import test_verification_baseline as baseline

BINARY = Path('/private/tmp/qleisli-ordinary-types-after-20261005/target/debug/qleisli')
KERNEL = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
INDEPENDENT = ROOT / 'tests/fixtures/frontend_v030/ordinary-types-independent'
sha = lambda value: hashlib.sha256(value).hexdigest()


def current_inputs():
    inputs = {p.relative_to(ROOT).as_posix(): sha(p.read_bytes())
              for p in (ROOT / 'src').rglob('*.rs')}
    inputs.update({p.relative_to(ROOT).as_posix(): sha(p.read_bytes())
                   for p in (ROOT / 'stdlib').rglob('*') if p.is_file()})
    for directory in ['corpus/quantum_katas/swap2', 'corpus/quantum_katas/fredkin3',
                      'corpus/qualtran/xor_constant2', 'corpus/qualtran/bitwise_not2',
                      'corpus/pennylane_demos/rx_quarter', 'corpus/pennylane_demos/phase_kickback1',
                      'examples/bell', 'examples/feedback'] + ['corpus/negative/' + p for p in
                          ['duplicate_owner', 'measured_owner', 'measurement_adjoint', 'dirty_auxiliary']]:
        for p in (ROOT / directory).glob('*'):
            if p.is_file() and (p.suffix == '.qli' or p.name == 'Qargo.toml'):
                inputs[p.relative_to(ROOT).as_posix()] = sha(p.read_bytes())
    for name in ['scripts/test_verification_baseline.py', 'scripts/check_verification_inventory.py',
                 'tests/compile.rs', 'tests/operation_parameters.rs']:
        inputs[name] = sha((ROOT / name).read_bytes())
    for p in (ROOT / 'tests/fixtures/verification_v022/source').glob('*.qirf'):
        inputs[p.relative_to(ROOT).as_posix()] = sha(p.read_bytes())
    return dict(sorted(inputs.items()))


def main():
    built = json.loads((INDEPENDENT / 'after-source.json').read_text())
    executables = json.loads((INDEPENDENT / 'after/validation.json').read_text())['executables']
    for path in [BINARY, KERNEL]:
        assert sha(path.read_bytes()) == executables[str(path)], path
    comment_deltas = {}
    for name, digest in built['files'].items():
        if not name.endswith('.rs') and not name.startswith('stdlib/'):
            continue
        current = (ROOT / name).read_bytes()
        if sha(current) == digest:
            continue
        assert name in ['src/lib.rs', 'src/frontend/types.rs'], name
        original = (Path(built['snapshot']) / name).read_bytes()
        assert sha(original) == digest
        # The two specifically reviewed module documentation edits are the only
        # allowed delta; this is not a generic semantics-erasing comparison.
        ordinary = lambda data: [line for line in data.splitlines() if not line.startswith(b'//!')]
        assert ordinary(original) == ordinary(current), name
        comment_deltas[name] = {'built': digest, 'current': sha(current), 'kind': 'module documentation comments only'}
    pre = current_inputs()
    calls = []
    comparisons = []
    real_run = subprocess.run
    real_frozen = baseline.frozen

    def observed_run(argv, *args, **kwargs):
        assert Path(str(argv[0])).resolve() == BINARY.resolve(), argv
        start = time.monotonic()
        result = real_run(argv, *args, **kwargs)
        row = {'argv': [str(v) for v in argv], 'cwd': str(kwargs.get('cwd', ROOT)),
               'exit_code': result.returncode, 'seconds': time.monotonic() - start}
        for label in ['stdout', 'stderr']:
            stream = kwargs[label]
            stream.flush(); position = stream.tell(); stream.seek(0)
            data = stream.read(1_048_577); stream.seek(position)
            assert len(data) <= 1_048_576, label
            name = f'call-{len(calls)+1:02d}.{label}.txt'
            (HERE / name).write_bytes(data)
            row[label] = name
            row[label + '_sha256'] = sha(data)
        calls.append(row)
        return result

    def observed_frozen(name, data, capture):
        assert capture is False
        expected = baseline.FIXTURES / name
        row = {'path': str(expected.relative_to(ROOT)), 'expected_sha256': sha(expected.read_bytes()),
               'actual_sha256': sha(data), 'identical': expected.read_bytes() == data}
        if not row['identical']:
            retained = 'mismatch-' + Path(name).name
            (HERE / retained).write_bytes(data)
            row['actual_bytes'] = retained
        comparisons.append(row)
        return real_frozen(name, data, capture)

    old_kernel = os.environ.get('QLEISLI_KERNEL')
    os.environ['QLEISLI_KERNEL'] = str(KERNEL)
    baseline.subprocess.run = observed_run
    baseline.frozen = observed_frozen
    decisions = None
    error = None
    start = time.monotonic()
    try:
        decisions = baseline.source_comparisons(BINARY, False)
    except Exception as caught:
        error = {'type': type(caught).__name__, 'message': str(caught)}
    finally:
        baseline.subprocess.run = real_run
        baseline.frozen = real_frozen
        if old_kernel is None:
            os.environ.pop('QLEISLI_KERNEL', None)
        else:
            os.environ['QLEISLI_KERNEL'] = old_kernel
    post = current_inputs()
    assert pre == post, 'inputs changed during selected-function run'
    for path in [BINARY, KERNEL]:
        assert sha(path.read_bytes()) == executables[str(path)]
    record = {'scope': __doc__, 'selected_function': 'test_verification_baseline.source_comparisons(binary, False)',
              'full_script_success_claimed': False, 'capture': False, 'driver_argv': sys.argv,
              'cwd': str(ROOT), 'source_before': pre, 'source_after': post, 'comment_only_deltas': comment_deltas,
              'binary': str(BINARY), 'binary_sha256': executables[str(BINARY)],
              'kernel': str(KERNEL), 'kernel_sha256': executables[str(KERNEL)],
              'compiled_source_manifest_sha256': sha((INDEPENDENT / 'after-source.json').read_bytes()),
              'calls': calls, 'artifact_comparisons': comparisons, 'decisions': decisions,
              'error': error, 'seconds': time.monotonic() - start,
              'result': 'passed' if error is None else 'failed-preserved'}
    (HERE / 'result.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({'result': record['result'], 'process_calls': len(calls),
                      'artifact_comparisons': len(comparisons), 'error': error}))
    return 0 if error is None else 1


if __name__ == '__main__':
    raise SystemExit(main())
