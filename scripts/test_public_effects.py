#!/usr/bin/env python3
"""Check current public-effect policy on 19 current translations of first-study projects.

Commands and expectations below are new, explicit regressions. Historical argv,
observer code, predictions and output records are never loaded or executed.
This bounded CLI check is not a source/runtime proof or process attestation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
from current_source_fixtures import current_source_project
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
STUDY = ROOT / 'tests/fixtures/authoring_sessions/public-effects-v030/first'
ORIGINAL = STUDY / 'original'
FREEZE_SHA256 = '7751de012818e1ca02a6997161a12a2eb100c33a22112922649beb9ed5a58258'

# Category, declaration name, and asserted bound, derived from the original
# sources and current public contract rather than historical outcomes.
CASES = {
    'discard-isometry': ('false-pure', 'f', 'Isometry'),
    'discard-unitary': ('false-pure', 'f', 'Unitary'),
    'hidden-measure-isometry': ('false-pure', 'f', 'Isometry'),
    'hidden-measure-unitary': ('false-pure', 'f', 'Unitary'),
    'reset-isometry': ('false-pure', 'g', 'Isometry'),
    'reset-unitary': ('false-pure', 'g', 'Unitary'),
    'transitive-discard-unitary': ('false-pure', 'f', 'Unitary'),
    'transitive-hidden-measure-unitary': ('false-pure', 'f', 'Unitary'),
    'transitive-reset-isometry': ('false-pure', 'g', 'Isometry'),
    'missing-public-quantum-effect': ('missing-public', 'g', None),
    'missing-public-closed-quantum-effect': ('missing-public', 'f', None),
    'external-missing-public-effect': ('missing-public', 'f', None),
    'external-identity-unitary': ('external-boundary', 'g', 'Unitary'),
    'external-reset-unitary': ('external-boundary', 'g', 'Unitary'),
    'private-inference-control': ('positive', None, None),
    'public-classical-inference-control': ('positive', None, None),
    'same-module-precision': ('positive', None, None),
    'external-identity-observe': ('positive', None, None),
    'external-reset-observe': ('reset-profile', None, None),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def identity(path):
    data = path.read_bytes()
    return len(data), hashlib.sha256(data).hexdigest()


def originals():
    # Only the inert inventory and original .qli/manifests are read. No saved
    # command, observer program or diagnostic is an input to this regression.
    frozen = (STUDY / 'freeze.json').read_bytes()
    require(hashlib.sha256(frozen).hexdigest() == FREEZE_SHA256,
            'first-study inventory identity changed')
    expected = {}
    for row in json.loads(frozen)['files']:
        relative = Path(row['path'])
        if relative.parts and relative.parts[0] == 'original':
            require(not relative.is_absolute() and '..' not in relative.parts,
                    'invalid original inventory path')
            require(row['path'] not in expected, 'duplicate original path')
            expected[row['path']] = (row['bytes'], row['sha256'])
    actual = {}
    require({p.name for p in ORIGINAL.iterdir()} == set(CASES),
            'original project set differs from the 19 reviewed cases')
    for path in ORIGINAL.rglob('*'):
        require(not path.is_symlink(), f'original symlink: {path}')
        if path.is_file():
            require(path.name == 'Qargo.toml' or path.suffix == '.qli',
                    f'unexpected original input: {path}')
            actual[str(path.relative_to(STUDY))] = identity(path)
    require(len(actual) == 43 and actual == expected,
            'original source/manifest bytes differ from the frozen 43 inputs')
    return actual


def expected(case, selected):
    category, name, bound = CASES[case]
    if category == 'missing-public':
        message = (f'public quantum function `{name}` requires an explicit '
                   '`unitary`, `isometry` or `observe` effect annotation')
        return 'effect', (message,)
    if category in ('false-pure', 'external-boundary'):
        return 'effect', (
            f'body effect `Observe` exceeds asserted `{bound}` effect of `{name}`',
            '"externally unitary" is not supported',
        )
    if category == 'reset-profile' and selected:
        return 'unsupported', (
            'selected concrete preparation does not support discard',
        )
    return 'ok', ()


def commands(compiler, kernel, case):
    project = current_source_project(ORIGINAL / case)
    common = [str(compiler), 'check']
    # A directory loads its ordinary schema-2 manifest; selected input instead
    # names all selected current modules explicitly and always requests the Raw route.
    yield 'finite-text', common + [str(project), f'--lean-kernel={kernel}']
    selected = common + ['--entry=main::main', '--ir-profile=raw', '--format=json',
                         f'--lean-kernel={kernel}']
    selected += [f'--module={path.stem}={path}'
                 for path in sorted(project.glob('*.qli'))]
    yield 'selected-raw-json', selected


def check_result(case, route, process, kernel):
    selected = route == 'selected-raw-json'
    code, fragments = expected(case, selected)
    require(process.returncode == (0 if code == 'ok' else 1),
            f'expected {code}, got exit {process.returncode}')
    stdout = process.stdout.decode('utf-8')
    stderr = process.stderr.decode('utf-8')
    if selected:
        require(not stderr, 'JSON command wrote stderr')
        document = json.loads(stdout)
        require(document.get('format') == 'qleisli.result'
                and document.get('version') == 1
                and document.get('command') == 'check'
                and document.get('outcome') == ('ok' if code == 'ok' else 'error'),
                'invalid selected check result envelope')
        diagnostics = document.get('diagnostics')
        if code == 'ok':
            require(diagnostics == [], 'successful check has diagnostics')
            result = document['result']
            require(result.get('status') == 'checked'
                    and result.get('entry') == 'main::main'
                    and result.get('ir_profile') == 'raw'
                    and result.get('source_check_scope') == 'all-supplied-module-declarations'
                    and result.get('native_check_scope') == 'selected-specialization'
                    and result.get('checker_path') == str(kernel)
                    and result.get('source_preservation_verified') is False,
                    'selected success lacks its actual bounded native scope')
            return code
        require(document.get('result') is None and isinstance(diagnostics, list)
                and len(diagnostics) == 1, 'refusal lacks one diagnostic/null result')
        diagnostic = diagnostics[0]
        require(diagnostic.get('code') == code and diagnostic.get('severity') == 'error',
                f'expected {code} error diagnostic')
        primary = diagnostic.get('primary')
        module = ('library' if case in ('external-missing-public-effect',
                                       'external-reset-observe') else 'main')
        require(isinstance(primary, dict) and primary.get('module') == module
                and primary.get('path') == str(current_source_project(ORIGINAL / case) / f'{module}.qli')
                and type(primary.get('start')) is int and type(primary.get('end')) is int
                and 0 <= primary['start'] < primary['end'],
                'diagnostic lost its selected current module/path/byte span')
        message = diagnostic.get('message', '')
    elif code == 'ok':
        require(not stderr and stdout.startswith('checked source: ')
                and 'native checks: IR structure, ownership, interface, classical scope and decoded execution view;' in stdout
                and f'checker: {kernel}\n' in stdout
                and 'source preservation: not proved\n' in stdout,
                'finite success lacks its actual native checking scope')
        return code
    else:
        require(not stdout and ': effect: ' in stderr,
                'finite refusal must be an effect diagnostic on stderr')
        message = stderr
    require(all(fragment in message for fragment in fragments),
            f'{code} diagnostic omits the public-effect/profile reason')
    return code


def raw_mismatch(case, route, error, stdout, stderr):
    print(f'{case} / {route}: {error}', file=sys.stderr, flush=True)
    for label, data in (('stdout', stdout), ('stderr', stderr)):
        sys.stderr.buffer.write(f'--- actual {label} ---\n'.encode())
        sys.stderr.buffer.write(data)
        if data and not data.endswith(b'\n'):
            sys.stderr.buffer.write(b'\n')
    sys.stderr.buffer.flush()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('compiler', type=Path, help='explicit already-built qleisli executable')
    parser.add_argument('--lean-kernel', type=Path,
                        help='already-built native checker (otherwise QLEISLI_KERNEL)')
    args = parser.parse_args()
    compiler = args.compiler.resolve(strict=True)
    selected_kernel = args.lean_kernel or os.environ.get('QLEISLI_KERNEL')
    require(selected_kernel, 'select --lean-kernel or QLEISLI_KERNEL; no fallback/build')
    kernel = Path(selected_kernel).resolve(strict=True)
    for executable in (compiler, kernel):
        require(executable.is_file() and os.access(executable, os.X_OK),
                f'not an executable file: {executable}')
    before_sources = originals()
    before_binaries = {path: identity(path) for path in (compiler, kernel)}
    counts = Counter()
    mismatches = 0
    actual_checks = 0
    try:
        for case in CASES:
            for route, command in commands(compiler, kernel, case):
                actual_checks += 1
                try:
                    process = subprocess.run(command, cwd=ROOT, stdin=subprocess.DEVNULL,
                                             capture_output=True, timeout=60, check=False)
                    counts[check_result(case, route, process, kernel)] += 1
                except subprocess.TimeoutExpired as error:
                    mismatches += 1
                    raw_mismatch(case, route, '60-second timeout',
                                 error.stdout or b'', error.stderr or b'')
                except (ValueError, KeyError, TypeError, UnicodeError) as error:
                    mismatches += 1
                    raw_mismatch(case, route, error, process.stdout, process.stderr)
    finally:
        require(originals() == before_sources, 'original inputs changed during current checks')
        require({path: identity(path) for path in (compiler, kernel)} == before_binaries,
                'CLI/native-checker bytes changed during current checks')
    require(actual_checks == 38, 'current command count differs from 38')
    print(f'Public effects: {actual_checks} current checks; {counts["ok"]} accepted, '
          f'{counts["effect"]} effect refusals, {counts["unsupported"]} unsupported; '
          f'{mismatches} mismatches. Original 43 inputs and CLI/checker bytes unchanged.')
    if not mismatches:
        require(counts == Counter(ok=9, effect=28, unsupported=1), 'unexpected category totals')
        print('Eight policy-gap acceptances now refuse; 18 false-pure refusals retained. '
              'Same-module/private/classical and Observe-identity positives remain; '
              'selected reset remains unsupported. No historical command executed.')
    return 1 if mismatches else 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, OSError) as error:
        print(f'Public-effect regression failed: {error}', file=sys.stderr)
        sys.exit(1)
