#!/usr/bin/env python3
"""Fixed bounded validation; never execute commands from stored metadata.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
TARGET = Path('/private/tmp/qleisli-bounded-validation-target')
NATIVE = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
NATIVE_SHA256 = '39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85'
CONSTITUTION_SHA256 = '40777370ec860891991bc89ef283f01a5db9a6be5480143f2e09e6014407452b'
TARGETS = (
    'unit_patterns', 'runtime_parameter_patterns', 'frontend_types',
    'ordinary_types', 'body_effects', 'source_collection', 'shared_resolution',
    'sized_declarations', 'selected_source_cli', 'sized_source', 'project',
)
SKIPS = (
    'long_acyclic_import_chain_loads_on_a_small_stack',
    'deep_import_cycle_reports_the_back_edge_and_cycle_path',
)
FIXTURE_DIRECTORIES = (
    'tests/fixtures/authoring_sessions/runtime-parameter-pattern-v030',
    'tests/fixtures/authoring_sessions/finite-unit-pattern-v030',
    'tests/fixtures/authoring_sessions/body-effects-v030',
    'tests/fixtures/authoring_sessions/body-effects-host-review-v030',
    'tests/fixtures/authoring_sessions/mixed-boolean-v030',
    'tests/fixtures/authoring_sessions/selected-source-cli-v030/attempt-01',
    'tests/fixtures/authoring_sessions/common-source-collection-v030/attempt-01',
    'tests/fixtures/authoring_sessions/common-pattern-check-v030/attempt-01',
    'tests/fixtures/frontend_v030/ordinary-types-independent/sources',
    'tests/fixtures/frontend_v030/ordinary-type-cutover/current/frontend_v030/shared-resolution',
    'tests/fixtures/frontend_v030/ordinary-type-cutover/current/frontend_v030/sized-declarations-independent/sources',
    'tests/fixtures/frontend_v030/ordinary-type-cutover/current/frontend_v030/common-parser',
    'tests/fixtures/frontend_v030/ordinary-type-cutover/current/measured_clients',
    'tests/fixtures/frontend_v030/ordinary-type-cutover/current/sized_clients',
    'corpus/sized/measured_qpe', 'corpus/sized/qualtran_qpe',
    'corpus/sized/qualtran_qft',
)
FIXED_INPUTS = (
    'Cargo.toml', 'Cargo.lock', 'tests/Qargo.toml', 'CONSTITUTION.md',
    'GOVERNANCE.md', 'governance/README.md', 'governance/ratification-2026.json',
    'governance/guarantees.json', 'governance/guarantees/current-evidence.json',
    'governance/guarantees/initial-2026-admission.json',
    'governance/proposals/initial-guarantees.json',
    'governance/interpretations/initial-2026-adoption.json',
    'governance/interpretations/initial-2026-reviewed.txt',
    'governance/interpretations/exactness-2026-adoption.json',
    'governance/proposals/exactness-2026.md',
    'lean-kernel/lean-toolchain', 'lean-kernel/lakefile.toml',
    'lean-kernel/lake-manifest.json',
    'tests/fixtures/frontend_v030/common-pattern-design/contract-v2.md',
    'tests/fixtures/frontend_v030/common-pattern-design/revision-v2.json',
    'tests/fixtures/authoring_sessions/common-pattern-check-v030/first-files.json',
    'tests/fixtures/authoring_sessions/common-pattern-check-v030/files-before.json',
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    with path.open('x', encoding='utf-8') as stream:
        stream.write(json.dumps(value, indent=2) + '\n')


def source_inputs():
    paths = list((ROOT / 'src').rglob('*.rs'))
    paths += list((ROOT / 'tests/common').rglob('*.rs'))
    paths += [ROOT / 'tests' / (name + '.rs') for name in TARGETS]
    paths += [ROOT / name for name in FIXED_INPUTS]
    paths += [HERE / 'driver.py', HERE / 'README.md', HERE / 'selection.json']
    for directory in ('stdlib',) + FIXTURE_DIRECTORIES:
        base = ROOT / directory
        if not base.is_dir():
            raise FileNotFoundError(f'declared input directory is absent: {directory}')
        paths += [p for p in base.rglob('*') if p.is_file() and p.suffix in {'.qli', '.toml'}]
    paths += [p for p in (ROOT / 'lean-kernel').rglob('*.lean') if '.lake' not in p.parts]
    # This is explicitly a bounded declared map, not every all-target fixture.
    return {str(p.relative_to(ROOT)): sha(p) for p in sorted(set(paths))}


def source_digest(files):
    return hashlib.sha256(json.dumps(files, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def tool_commands(mode):
    cargo = ['/opt/homebrew/bin/cargo'] if mode == 'latest' else [
        '/opt/homebrew/bin/rustup', 'run', '1.85.0', 'cargo']
    rustc = ['/opt/homebrew/bin/rustc'] if mode == 'latest' else [
        '/opt/homebrew/bin/rustup', 'run', '1.85.0', 'rustc']
    harness = ['--nocapture', '--test-threads=2']
    integrations = cargo + ['test', '--locked', '--jobs=2']
    integrations += [arg for name in TARGETS for arg in ('--test', name)]
    integrations += ['--'] + harness + [arg for name in SKIPS for arg in ('--skip', name)]
    # These are authored commands, never read from selection.json or logs.
    return (
        ('cargo-version', cargo + ['--version']),
        ('rustc-version', rustc + ['--version']),
        ('format', cargo + ['fmt', '--all', '--', '--check']),
        ('check-all-targets', cargo + ['check', '--locked', '--all-targets', '--jobs=2']),
        ('shared-type-tests', cargo + ['test', '--locked', '--lib', '--jobs=2',
                                     'frontend::types::tests', '--'] + harness),
        ('focused-integration-tests', integrations),
        ('clippy-all-targets', cargo + ['clippy', '--locked', '--all-targets',
                                      '--jobs=2', '--', '-D', 'warnings']),
        ('rebuilt-cli', cargo + ['build', '--locked', '--bin', 'qleisli', '--jobs=2']),
    )


def environment():
    env = dict(os.environ)
    for name in ('RUSTC', 'RUSTDOC', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER',
                 'RUSTUP_TOOLCHAIN', 'RUSTFLAGS', 'CARGO_ENCODED_RUSTFLAGS', 'CARGO'):
        env.pop(name, None)
    env.update(CARGO_TARGET_DIR=str(TARGET), CARGO_INCREMENTAL='0',
               CARGO_PROFILE_DEV_DEBUG='0', CARGO_PROFILE_TEST_DEBUG='0',
               CARGO_BUILD_JOBS='2', RUST_TEST_THREADS='2',
               QLEISLI_KERNEL=str(NATIVE), QLEISLI_HIERARCHY_KERNEL=str(NATIVE),
               PYTHONDONTWRITEBYTECODE='1',
               PATH='/opt/homebrew/bin:' + env.get('PATH', ''))
    return env


def run(mode, attempt):
    out = HERE / (mode + '-' + attempt)
    out.mkdir(exist_ok=False)
    before = source_inputs()
    write_json(out / 'inputs-before.json', {'files': before, 'sha256': source_digest(before)})
    (out / 'executed-driver.py.txt').open('xb').write(Path(__file__).read_bytes())
    native_before = sha(NATIVE)
    if native_before != NATIVE_SHA256 or sha(ROOT / 'CONSTITUTION.md') != CONSTITUTION_SHA256:
        write_json(out / 'startup-failure.json', {
            'status': 'identity-mismatch', 'actual_native_sha256': native_before,
            'actual_constitution_sha256': sha(ROOT / 'CONSTITUTION.md'),
            'no_child_command_started': True})
        return 1
    commands = tool_commands(mode)
    write_json(out / 'planned-commands.json', {'status': 'planned-not-results',
                                             'commands': [argv for _, argv in commands]})
    env = environment()
    records = []
    failed = False
    for index, (label, argv) in enumerate(commands):
        prefix = f'{index:02d}-{label}'
        stdout, stderr = out / (prefix + '.stdout.txt'), out / (prefix + '.stderr.txt')
        print('Running fixed stage ' + label + ': ' + ' '.join(argv), flush=True)
        start = time.monotonic()
        exit_code, launch_error, timeout = None, None, False
        with stdout.open('xb') as output, stderr.open('xb') as errors:
            try:
                proc = subprocess.run(argv, cwd=ROOT, env=env, stdout=output,
                                      stderr=errors, timeout=1200, check=False)
                exit_code = proc.returncode
            except OSError as error:
                launch_error = repr(error)
            except subprocess.TimeoutExpired:
                timeout = True
        text = stdout.read_text(errors='replace')
        rows = [dict(status=status, passed=int(passed), failed=int(failures),
                     ignored=int(ignored), measured=int(measured), filtered=int(filtered))
                for status, passed, failures, ignored, measured, filtered in re.findall(
                    r'test result: (ok|FAILED)\. (\d+) passed; (\d+) failed; (\d+) ignored; '
                    r'(\d+) measured; (\d+) filtered out;', text)]
        postcondition = None
        expected = '1.98.1' if mode == 'latest' else '1.85.0'
        if exit_code == 0 and label in {'cargo-version', 'rustc-version'}:
            tool = 'cargo' if label == 'cargo-version' else 'rustc'
            if not re.match(re.escape(tool + ' ' + expected) + r'(?:\s|$)', text):
                postcondition = 'unexpected actual toolchain version'
        if exit_code == 0 and label.endswith('tests'):
            if not rows or sum(row['passed'] for row in rows) == 0:
                postcondition = 'no genuine passing test result reported'
            if label == 'focused-integration-tests' and len(rows) != len(TARGETS):
                postcondition = 'not all selected integration targets reported results'
        after = source_inputs()
        native_after = sha(NATIVE)
        identity_ok = after == before and native_after == native_before
        event = {
            'label': label, 'argv': argv, 'cwd': str(ROOT), 'exit_code': exit_code,
            'launch_error': launch_error, 'timed_out': timeout,
            'postcondition_error': postcondition, 'seconds': time.monotonic() - start,
            'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'stdout': {'path': stdout.name, 'sha256': sha(stdout), 'bytes': stdout.stat().st_size},
            'stderr': {'path': stderr.name, 'sha256': sha(stderr), 'bytes': stderr.stat().st_size},
            'actual_test_results': rows, 'source_input_digest_after': source_digest(after),
            'native_sha256_after': native_after, 'identities_unchanged': identity_ok,
        }
        write_json(out / (prefix + '.json'), event)
        records.append(event)
        print(json.dumps(event), flush=True)
        if launch_error or timeout or exit_code != 0 or postcondition or not identity_ok:
            failed = True
            break
    after = source_inputs()
    write_json(out / 'inputs-after.json', {'files': after, 'sha256': source_digest(after)})
    cli = TARGET / 'debug/qleisli'
    write_json(out / 'results.json', {
        'format': 'qleisli.common-pattern-bounded-validation', 'version': 1,
        'mode': mode, 'attempt': attempt, 'status': 'failed' if failed else 'passed',
        'records': records, 'remaining_stages_not_run': len(commands) - len(records),
        'source_files_before': len(before), 'source_inputs_unchanged': before == after,
        'native_sha256_before': native_before, 'native_sha256_after': sha(NATIVE),
        'cli_path': str(cli), 'cli_sha256_after': sha(cli) if cli.is_file() else None,
        'cli_rebuild_completed': any(event['label'] == 'rebuilt-cli' and
                                    event['exit_code'] == 0 and
                                    event['identities_unchanged'] for event in records),
        'scope': 'Actual bounded Rust checks with a declared incomplete input map. '
                 'No Lean build/replay, complete fixture closure, source preservation, '
                 'new native authority, guarantee discharge, full CI or release approval.',
    })
    return int(failed)


def main():
    if len(sys.argv) != 3 or sys.argv[1] not in {'latest', 'msrv'} or not re.fullmatch(
            r'attempt-[0-9]{2}', sys.argv[2]):
        raise SystemExit('usage: driver.py {latest|msrv} attempt-NN; execute only after root barrier')
    # Both modes share one target: reject simultaneous validation rather than
    # replacing the observer CLI while another mode or replay runs.
    with (HERE / 'validation-target.lock').open('a') as lock:
        try:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise SystemExit('another driver holds this validation target lock')
        return run(sys.argv[1], sys.argv[2])


if __name__ == '__main__':
    raise SystemExit(main())
