#!/usr/bin/env python3
"""Build only the reviewed private client, with unchanged root dependency lock.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
TARGET = Path('/private/tmp/qleisli-bounded-validation-target')
CLI = TARGET / 'debug/qleisli'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def save(path, value):
    with path.open('x') as stream:
        stream.write(json.dumps(value, indent=2) + '\n')

def main():
    out = HERE / 'build-attempt-01'
    out.mkdir(exist_ok=False)
    before = {str(p.relative_to(ROOT)): sha(p) for p in (ROOT / 'src').rglob('*.rs')}
    before['Cargo.lock'] = sha(ROOT / 'Cargo.lock')
    before['Cargo.toml'] = sha(ROOT / 'Cargo.toml')
    cli_before = sha(CLI)
    save(out / 'inputs-before.json', {'root_files': before, 'cli_sha256': cli_before,
        'client_main_sha256': sha(HERE / 'src/main.rs'), 'client_lock_sha256': sha(HERE / 'Cargo.lock'),
        'scope': 'Selected identities, not a complete build/runtime closure.'})
    (out / 'main.before.rs.txt').write_bytes((HERE / 'src/main.rs').read_bytes())
    env = dict(os.environ, CARGO_TARGET_DIR=str(TARGET), CARGO_INCREMENTAL='0',
        CARGO_PROFILE_DEV_DEBUG='0', CARGO_PROFILE_TEST_DEBUG='0', CARGO_BUILD_JOBS='2')
    commands = [
        ('00.rust-version', ['rustup', 'run', '1.85.0', 'rustc', '--version']),
        ('01.format-before', ['rustup', 'run', '1.85.0', 'rustfmt', '--edition', '2024', '--check', str(HERE / 'src/main.rs')]),
        ('02.format', ['rustup', 'run', '1.85.0', 'rustfmt', '--edition', '2024', str(HERE / 'src/main.rs')]),
        ('03.format-after', ['rustup', 'run', '1.85.0', 'rustfmt', '--edition', '2024', '--check', str(HERE / 'src/main.rs')]),
        ('04.clippy', ['rustup', 'run', '1.85.0', 'cargo', 'clippy', '--offline', '--locked', '--manifest-path', str(HERE / 'Cargo.toml'), '--', '-D', 'warnings']),
        ('05.build', ['rustup', 'run', '1.85.0', 'cargo', 'build', '--offline', '--locked', '--manifest-path', str(HERE / 'Cargo.toml')]),
    ]
    save(out / 'planned.json', {'fixed_commands': commands, 'recorded_commands_executed': False})
    records = []
    for name, argv in commands:
        started = datetime.datetime.now(datetime.timezone.utc).isoformat()
        with (out / (name + '.stdout.txt')).open('xb') as stdout, (out / (name + '.stderr.txt')).open('xb') as stderr:
            result = subprocess.run(argv, cwd=ROOT, env=env, stdout=stdout, stderr=stderr, timeout=180)
        row = dict(name=name, argv=argv, cwd=str(ROOT), started_utc=started, exit_code=result.returncode)
        records.append(row)
        save(out / (name + '.json'), row)
        print(name, 'actual exit', result.returncode, flush=True)
        # The first formatting observation is retained even when it requests
        # whitespace repair. Every later tool stage must actually succeed.
        if result.returncode and name != '01.format-before':
            save(out / 'failure.json', {'records': records, 'remaining_not_run': len(commands) - len(records)})
            return 1
    after = {name: sha(ROOT / name) for name in before}
    binary = TARGET / 'debug/qleisli-qft-native-gate-design'
    unchanged = before == after and cli_before == sha(CLI)
    (out / 'main.after.rs.txt').write_bytes((HERE / 'src/main.rs').read_bytes())
    save(out / 'result.json', {'records': records, 'root_inputs_and_cli_unchanged': unchanged,
        'root_input_count': len(before), 'client_main_sha256': sha(HERE / 'src/main.rs'),
        'client_lock_sha256': sha(HERE / 'Cargo.lock'), 'client_path': str(binary), 'client_sha256': sha(binary),
        'native_calls': 0, 'scope': 'Private client compilation/format/lint only; no QFT/native check or release attestation.'})
    return 0 if unchanged else 1

if __name__ == '__main__':
    raise SystemExit(main())
