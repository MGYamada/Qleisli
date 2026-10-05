#!/usr/bin/env python3
"""Fixed bounded first observations, never execute recorded commands.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parent
REPO = Path('/Users/masa/git/Qleisli')
CLI = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
NATIVE = REPO / 'lean-kernel/.lake/build/bin/qleisli-kernel'
WRAPPER = ROOT / 'native-log.py'
OUT = ROOT / 'before'
CASES = [
    'nested-runtime-parameter', 'duplicate-runtime-parameter', 'legal-rebinding',
    'hidden-live-owner', 'duplicate-join-input', 'quantum-unit-wildcard',
    'empty-register-wildcard', 'unused-invalid-sibling',
]
CONTRACTS = [
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
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    with path.open('x', encoding='utf-8') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def identity():
    files = list((REPO / 'src').rglob('*.rs'))
    files += [path for path in (REPO / 'lean-kernel').rglob('*.lean')
              if '.lake' not in path.relative_to(REPO / 'lean-kernel').parts]
    files += [path for path in (REPO / 'stdlib').rglob('*')
              if path.is_file() and path.suffix in {'.qli', '.toml'}]
    files += [REPO / name for name in CONTRACTS + ['Cargo.toml', 'Cargo.lock',
              'lean-kernel/lean-toolchain', 'lean-kernel/lakefile.toml',
              'lean-kernel/lake-manifest.json']]
    return dict(cli_path=str(CLI), cli_sha256=sha(CLI), native_path=str(NATIVE),
                native_sha256=sha(NATIVE),
                files={str(path.relative_to(REPO)): sha(path) for path in sorted(set(files))})


def main():
    OUT.mkdir()
    inputs = {str(path.relative_to(ROOT)): sha(path) for path in sorted(ROOT.rglob('*'))
              if path.is_file() and OUT not in path.parents and path.name != 'session.json'}
    save(ROOT / 'first-files.json', dict(status='first-files-before-any-cli-observation', files=inputs))
    initial = identity()
    save(ROOT / 'identity-before.json', dict(initial,
         parent_reported_local_source_commit='b544cd2d96dcc94e0ef29b28e6b08979bca5d9b1',
         build_provenance='Already built fixed CLI; parent reports actual MSRV1.85 validation. No build or Git attestation performed here.',
         recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
         scope='Byte identity only; not source preservation, proof, authenticity or release approval.'))
    (OUT / 'executed-driver.py.txt').write_bytes(Path(__file__).read_bytes())
    session = json.loads((ROOT / 'session.json').read_text())
    assert not session['attempts'][0]['observations']
    observations = []
    rows = []

    def unchanged():
        assert all(sha(ROOT / name) == digest for name, digest in inputs.items()), 'first source/driver changed'
        assert identity() == initial, 'CLI/native/source/contract changed during study'

    unchanged()
    for case in CASES:
        project = ROOT / 'attempt-01' / case
        for profile, action, presentation in [
            ('finite', 'check', 'text'), ('finite', 'check', 'json'),
            ('selected-auto', 'check', 'text'), ('selected-auto', 'check', 'json'),
            ('selected-auto', 'emit-proposal', 'json'),
        ]:
            unchanged()
            name = f'{case}-{profile}-{action}-{presentation}'
            native_log = OUT / (name + '.native.jsonl')
            native_log.touch(exist_ok=False)
            if profile == 'finite':
                command = [str(CLI), action, str(project)]
            else:
                command = [str(CLI), action, '--entry=main::entry',
                           '--module=main=' + str(project / 'main.qli'), '--ir-profile=auto']
            proposal = OUT / (name + '.proposal.json')
            if action == 'emit-proposal':
                command.append('--output=' + str(proposal))
            else:
                command.append('--lean-kernel=' + str(WRAPPER))
            if presentation == 'json':
                command.append('--format=json')
            env = dict(os.environ, QLEISLI_PATTERN_NATIVE_LOG=str(native_log),
                       PYTHONDONTWRITEBYTECODE='1')
            env.pop('QLEISLI_KERNEL', None)
            env.pop('QLEISLI_HIERARCHY_KERNEL', None)
            start = time.monotonic()
            result = subprocess.run(command, cwd=REPO, env=env, capture_output=True, timeout=90)
            for suffix, data in [('stdout.txt', result.stdout), ('stderr.txt', result.stderr)]:
                with (OUT / (name + '.' + suffix)).open('xb') as stream:
                    stream.write(data)
            event = dict(command=command, exit_code=result.returncode,
                         seconds=time.monotonic()-start,
                         recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                         timestamp_note='Clock after completion; not authenticated provenance.',
                         native_invocations=len(native_log.read_text().splitlines()),
                         stdout_raw=name+'.stdout.txt', stderr_raw=name+'.stderr.txt',
                         stderr=result.stderr.decode(), proposal_emitted=proposal.exists())
            if presentation == 'json':
                try:
                    event['stdout'] = json.loads(result.stdout)
                except ValueError as error:
                    event['transcript'] = result.stdout.decode() + result.stderr.decode()
                    event['json_parse_error'] = str(error)
            else:
                event['transcript'] = result.stdout.decode() + result.stderr.decode()
            if proposal.exists():
                event.update(proposal_file=str(proposal.relative_to(ROOT)),
                             proposal_sha256=sha(proposal), proposal_bytes=proposal.stat().st_size,
                             proposal_authority='Untrusted producer result; not native acceptance or source preservation.')
            path = OUT / (name + '.json')
            save(path, event)
            observations.append(str(path.relative_to(ROOT)))
            rows.append(dict(case=case, profile=profile, action=action, presentation=presentation,
                             observation=str(path.relative_to(ROOT)), exit_code=result.returncode,
                             native_invocations=event['native_invocations'], proposal_emitted=proposal.exists()))
            unchanged()
            print(name, result.returncode, event['native_invocations'], proposal.exists(), flush=True)
    session['attempts'][0]['observations'] = observations
    # Append actual events to the active index; session.before.json remains exact.
    (ROOT / 'session.json').write_text(json.dumps(session, indent=2)+'\n')
    unchanged()
    save(OUT / 'summary.json', dict(rows=rows, source_repairs=0,
         captures_only=True, native_consistency_is_not_source_preservation=True))
    save(OUT / 'identity-final.json', dict(identity(),
         first_inputs_unchanged=True, actual_observation_count=len(rows),
         scope='Current source/CLI/native/Cargo/stdlib/constitutional byte identities remained unchanged.'))
    files = {str(path.relative_to(ROOT)): dict(sha256=sha(path), bytes=path.stat().st_size)
             for path in sorted(ROOT.rglob('*')) if path.is_file()}
    save(ROOT / 'files-before.json', dict(files=files, self_excluded='files-before.json'))
    print(json.dumps(dict(observations=len(rows), source_inputs=len(initial['files']),
         cli_sha256=initial['cli_sha256'], native_sha256=initial['native_sha256'],
         source_unchanged=True, total_record_bytes=sum(item['bytes'] for item in files.values())), indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
