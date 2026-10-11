#!/usr/bin/env python3
"""Fixed first-source capture; never execute recorded argv or predictions.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
REPO = Path('/Users/masa/git/Qleisli')
CLI = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
CLI_SHA256 = '4a5cc9e753268fd7b0b4972cf84dd1fd6338218bc0b104d71b8465fab89151cf'
NATIVE = REPO / 'lean-kernel/.lake/build/bin/qleisli-kernel'
NATIVE_SHA256 = '39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85'
WRAPPER = ROOT / 'native-log.py'
OUT = ROOT / 'before'
CASES = (
    'duplicate-static-natural', 'static-runtime-collision',
    'nested-runtime-duplicate', 'first-type-before-later-duplicate',
    'duplicate-before-empty-register', 'forward-operation-kind',
    'unused-invalid-sibling', 'valid-nested-unit-quantum',
    'duplicate-static-operation-unit',
    'symbolic-type-before-later-duplicate',
)
CONTRACTS = (
    'CONSTITUTION.md', 'GOVERNANCE.md', 'governance/README.md',
    'governance/ratification-2026.json', 'governance/guarantees.json',
    'governance/interpretations/initial-2026-reviewed.txt',
    'governance/interpretations/initial-2026-adoption.json',
    'governance/proposals/exactness-2026.md',
    'governance/interpretations/exactness-2026-adoption.json',
    'governance/proposals/initial-guarantees.json',
    'governance/guarantees/initial-2026-admission.json',
    'governance/guarantees/current-evidence.json',
    'docs/src/reference/authority.md', 'docs/src/reference/type-model.md',
    'docs/src/reference/source-text.md',
    'tests/fixtures/frontend_v030/common-parameter-declaration-design/candidate-01.md',
    'tests/fixtures/frontend_v030/common-parameter-declaration-design/contract-before-code.md',
    'tests/fixtures/frontend_v030/common-parameter-declaration-design/author-design.md',
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    with path.open('x', encoding='utf-8') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def identity():
    files = list((REPO / 'src').rglob('*.rs'))
    files += [p for p in (REPO / 'lean-kernel').rglob('*.lean') if '.lake' not in p.parts]
    files += [p for p in (REPO / 'stdlib').rglob('*')
              if p.is_file() and p.suffix in {'.qli', '.toml'}]
    files += [REPO / name for name in CONTRACTS + (
        'Cargo.toml', 'Cargo.lock', 'lean-kernel/lean-toolchain',
        'lean-kernel/lakefile.toml', 'lean-kernel/lake-manifest.json',
    )]
    return dict(cli_path=str(CLI), cli_sha256=sha(CLI), native_path=str(NATIVE),
                native_sha256=sha(NATIVE),
                files={str(p.relative_to(REPO)): sha(p) for p in sorted(set(files))})


def command(case, profile, presentation):
    """Authored fixed forms; planned-command JSON is never an executable input."""
    project = ROOT / 'attempt-01' / case
    if profile == 'finite':
        argv = [str(CLI), 'check', str(project)]
    else:
        argv = [str(CLI), 'check', '--entry=main::entry',
                '--module=main=' + str(project / 'main.qli'), '--ir-profile=auto']
    argv.append('--lean-kernel=' + str(WRAPPER))
    if presentation == 'json':
        argv.append('--format=json')
    return argv


def main():
    if len(sys.argv) != 1:
        raise SystemExit('usage: driver.py; root executes only after source/CLI freeze')
    OUT.mkdir(exist_ok=False)
    (OUT / 'executed-driver.py.txt').open('xb').write(Path(__file__).read_bytes())
    frozen = json.loads((ROOT / 'first-files.json').read_text())['files']
    prepared = json.loads((ROOT / 'identity-prepared.json').read_text())['identity']
    initial = identity()
    save(OUT / 'identity.before.json', dict(identity=initial,
         first_files_manifest_sha256=sha(ROOT / 'first-files.json'),
         recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
         python_executable=sys.executable, python_version=sys.version,
         scope='Current selected bytes only; no source-to-binary attestation or proof.'))

    def unchanged():
        for name, digest in frozen.items():
            if sha(ROOT / name) != digest:
                raise ValueError('First source/record/driver changed: ' + name)
        if identity() != prepared:
            raise ValueError('Source/CLI/native/contracts changed after preparation')

    try:
        if sys.version_info < (3, 11):
            raise ValueError('Python 3.11+ required')
        if initial['cli_sha256'] != CLI_SHA256 or initial['native_sha256'] != NATIVE_SHA256:
            raise ValueError('Selected CLI/native bytes differ from fixed baseline')
        unchanged()
    except (OSError, ValueError) as error:
        save(OUT / 'startup-failure.json', dict(child_commands_started=0, error=repr(error)))
        return 1
    session = json.loads((ROOT / 'session.before.json').read_text())
    if (ROOT / 'session.json').exists() or session['attempts'][0]['observations']:
        raise ValueError('First session must be unpublished and have no observations')
    rows, observations = [], []
    for case in CASES:
        for profile, presentation in (
            ('finite', 'text'), ('finite', 'json'),
            ('selected-auto', 'text'), ('selected-auto', 'json'),
        ):
            unchanged()
            name = f'{case}-{profile}-check-{presentation}'
            native_log = OUT / (name + '.native.jsonl')
            native_log.touch(exist_ok=False)
            argv = command(case, profile, presentation)
            env = dict(os.environ, QLEISLI_PARAMETER_NATIVE_LOG=str(native_log),
                       PYTHONDONTWRITEBYTECODE='1')
            env.pop('QLEISLI_KERNEL', None)
            env.pop('QLEISLI_HIERARCHY_KERNEL', None)
            stdout_path, stderr_path = OUT / (name + '.stdout.txt'), OUT / (name + '.stderr.txt')
            begin = time.monotonic()
            exit_code, launch_error, timed_out = None, None, False
            with stdout_path.open('xb') as output, stderr_path.open('xb') as errors:
                try:
                    result = subprocess.run(argv, cwd=REPO, env=env, stdout=output,
                                            stderr=errors, check=False, timeout=90)
                    exit_code = result.returncode
                except OSError as error:
                    launch_error = repr(error)
                except subprocess.TimeoutExpired:
                    timed_out = True
            stdout, stderr = stdout_path.read_bytes(), stderr_path.read_bytes()
            event = dict(command=argv, exit_code=exit_code,
                         seconds=time.monotonic() - begin,
                         recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                         timestamp_note='Clock after completion; not authenticated provenance.',
                         launch_error=launch_error, timed_out=timed_out,
                         native_invocations=len(native_log.read_text().splitlines()),
                         native_argv_log=native_log.name,
                         stdout_raw=stdout_path.name, stderr_raw=stderr_path.name,
                         stdout_sha256=sha(stdout_path), stderr_sha256=sha(stderr_path))
            transcript = stdout.decode(errors='replace') + stderr.decode(errors='replace')
            if presentation == 'json':
                try:
                    decoded = json.loads(stdout)
                except (ValueError, UnicodeDecodeError) as error:
                    event.update(transcript=transcript, json_parse_error=repr(error))
                else:
                    if isinstance(decoded, dict) and decoded.get('format') == 'qleisli.result':
                        event['stdout'] = decoded
                    else:
                        event.update(transcript=transcript, unexpected_parsed_stdout=decoded)
            else:
                event['transcript'] = transcript
            save(OUT / (name + '.json'), event)
            row = dict(case=case, profile=profile, presentation=presentation,
                       observation='before/' + name + '.json', exit_code=exit_code,
                       native_invocations=event['native_invocations'])
            rows.append(row)
            if launch_error or timed_out:
                save(OUT / 'incomplete.json', dict(rows=rows,
                     source_repairs=0, session_published=False,
                     reason='Actual launch failure/timeout retained; no child exit invented.'))
                return 1
            observations.append(row['observation'])
            unchanged()
            print(name, exit_code, event['native_invocations'], flush=True)
    session['attempts'][0]['observations'] = observations
    session['status'] = 'actual-first-observations-retained'
    save(ROOT / 'session.json', session)
    unchanged()
    save(OUT / 'summary.json', dict(rows=rows, actual_observation_count=len(rows),
         source_repairs=0, predictions_used_as_assertions=False,
         no_runtime_or_algorithm_oracle=True,
         native_consistency_is_not_source_preservation=True))
    save(OUT / 'identity.final.json', dict(identity=identity(), first_inputs_unchanged=True,
         actual_observation_count=len(rows),
         scope='Selected source/CLI/native/Cargo/stdlib/constitutional bytes remained unchanged.'))
    files = {str(p.relative_to(ROOT)): dict(sha256=sha(p), bytes=p.stat().st_size)
             for p in sorted(ROOT.rglob('*')) if p.is_file()}
    save(ROOT / 'files-before.json', dict(files=files, self_excluded='files-before.json'))
    print(json.dumps(dict(actual_observations=len(rows), native_calls=sum(
         row['native_invocations'] for row in rows), first_inputs_unchanged=True,
         retained_file_bytes=sum(item['bytes'] for item in files.values())), indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
