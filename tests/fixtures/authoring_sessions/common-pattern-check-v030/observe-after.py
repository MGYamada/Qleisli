#!/usr/bin/env python3
"""Fixed 40-command after capture; recorded argv is never executed.

Keep the first study and its session/index unchanged. A caller must supply the
expected digest of the separately built current CLI. These byte checks are not
build attestation, source preservation, proof, authenticity or release approval.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
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
BEFORE = ROOT / 'before'
OUT = ROOT / 'after'
BASELINE_MAP = ROOT / 'files-before.json'
BASELINE_MAP_SHA256 = 'a8620894684e6cbd05b43225d41d108d7cdf9434a699b41b109eba85458f02d4'
CASES = [
    'nested-runtime-parameter', 'duplicate-runtime-parameter', 'legal-rebinding',
    'hidden-live-owner', 'duplicate-join-input', 'quantum-unit-wildcard',
    'empty-register-wildcard', 'unused-invalid-sibling',
]
ACTIONS = [
    ('finite', 'check', 'text'), ('finite', 'check', 'json'),
    ('selected-auto', 'check', 'text'), ('selected-auto', 'check', 'json'),
    ('selected-auto', 'emit-proposal', 'json'),
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
CHANGED_SOURCES = {
    'src/frontend/compile/lower/mod.rs':
        '890fccfc2dcf8762c6de3387a589925df5b267f53c642d0e6fc713ce1cc5ad9a',
    'src/frontend/mod.rs':
        '7302134df5900aba92f1dbaec3240382abb98b2160c5c3c3136e00bb814e3422',
    'src/frontend/sized/ast.rs':
        '42ddd4d545865611ba9bc7838ad6600e06879140cd4e689e89c8194891ed78eb',
    'src/frontend/sized/check.rs':
        '89b3cfb37250e672cefcc0c0ce6bb68aa868bcfad8f03776074f3bf607ed48da',
}
NEW_SOURCE = 'src/frontend/pattern.rs'
NEW_SOURCE_SHA256 = '5f9882d36769d4d3966108fb34ca6f743b17b78d4ed40595b4d82b28bacabede'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def file_identity(path):
    data = path.read_bytes()
    return dict(sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))


def save(path, value):
    with path.open('x', encoding='utf-8') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def current_identity():
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
                files={str(path.relative_to(REPO)): sha(path)
                       for path in sorted(set(files))})


def retained_session_files():
    return {str(path.relative_to(ROOT)): file_identity(path)
            for path in sorted(ROOT.rglob('*'))
            if path.is_file() and OUT not in path.parents}


def command_for(project, profile, action, presentation, proposal):
    # Authored from the original fixed driver, not read from event metadata.
    if profile == 'finite':
        command = [str(CLI), action, str(project)]
    else:
        command = [str(CLI), action, '--entry=main::entry',
                   '--module=main=' + str(project / 'main.qli'), '--ir-profile=auto']
    if action == 'emit-proposal':
        command.append('--output=' + str(proposal))
    else:
        command.append('--lean-kernel=' + str(WRAPPER))
    if presentation == 'json':
        command.append('--format=json')
    return command


def native_arguments(path):
    arguments = [json.loads(line) for line in path.read_text().splitlines()]
    require(all(isinstance(argv, list) and all(isinstance(arg, str) for arg in argv)
                for argv in arguments), 'native log must contain argv arrays')
    return arguments


def compare_output(before, after, before_proposal, after_proposal, action):
    if before == after:
        return True, False
    # This is the sole permitted normalization, only when raw output differs:
    # one command's exact --output target moved from before/ to after/.
    if action != 'emit-proposal':
        return False, False
    old = str(before_proposal).encode()
    new = str(after_proposal).encode()
    if old not in before or new not in after:
        return False, False
    normalized = after.replace(new, old)
    return normalized == before, normalized == before


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cli-sha256', required=True,
                        help='Digest of the separately built fixed current CLI')
    args = parser.parse_args()
    require(len(args.cli_sha256) == 64
            and all(c in '0123456789abcdef' for c in args.cli_sha256),
            'expected CLI SHA-256 must be 64 lower-case hexadecimal characters')
    require(sha(BASELINE_MAP) == BASELINE_MAP_SHA256, 'baseline map changed')
    baseline = json.loads(BASELINE_MAP.read_text())['files']
    require(len(baseline) == 191, 'expected exactly 191 frozen baseline files')
    for name, expected in baseline.items():
        require(file_identity(ROOT / name) == expected,
                'frozen baseline file changed: ' + name)
    historical = json.loads((ROOT / 'identity-before.json').read_text())
    require(len(historical['files']) == 234, 'expected 234 original input identities')
    require(args.cli_sha256 != historical['cli_sha256'],
            'the original baseline binary cannot be reused as the after CLI')
    initial = current_identity()
    require(initial['cli_sha256'] == args.cli_sha256, 'current CLI digest mismatch')
    require(initial['native_sha256'] == historical['native_sha256'], 'native changed')
    require(set(initial['files']) == set(historical['files']) | {NEW_SOURCE},
            'current input inventory must be the original 234 plus pattern.rs')
    for name, previous in historical['files'].items():
        require(initial['files'][name] == CHANGED_SOURCES.get(name, previous),
                'unexpected current input identity: ' + name)
    require(initial['files'][NEW_SOURCE] == NEW_SOURCE_SHA256, 'new pattern.rs changed')
    retained = retained_session_files()
    initial_digest = digest(initial)

    def unchanged():
        require(sha(BASELINE_MAP) == BASELINE_MAP_SHA256, 'baseline map changed')
        for name, expected in baseline.items():
            require(file_identity(ROOT / name) == expected,
                    'frozen baseline file changed: ' + name)
        require(retained_session_files() == retained,
                'a retained session/input/driver file or inventory changed')
        require(current_identity() == initial,
                'CLI/native/current 235 source/contract inputs changed')

    unchanged()
    OUT.mkdir()  # Exclusive creation: preserve any earlier actual after attempt.
    save(OUT / 'identity-initial.json', dict(initial,
         expected_cli_sha256=args.cli_sha256, identity_digest=initial_digest,
         baseline_map_sha256=BASELINE_MAP_SHA256, retained_files=retained,
         source_changes_from_baseline=CHANGED_SOURCES,
         added_source={NEW_SOURCE: NEW_SOURCE_SHA256},
         scope='Byte identities only. Build provenance is supplied separately by the caller; no proof or source-preservation claim.'))
    with (OUT / 'executed-driver.py.txt').open('xb') as stream:
        stream.write(Path(__file__).read_bytes())
    rows = []
    timed_out = False
    for case in CASES:
        project = ROOT / 'attempt-01' / case
        for profile, action, presentation in ACTIONS:
            unchanged()
            name = f'{case}-{profile}-{action}-{presentation}'
            native_log = OUT / (name + '.native.jsonl')
            native_log.touch(exist_ok=False)
            proposal = OUT / (name + '.proposal.json')
            before_proposal = BEFORE / (name + '.proposal.json')
            require(not proposal.exists(), 'after proposal target already exists')
            command = command_for(project, profile, action, presentation, proposal)
            env = dict(os.environ, QLEISLI_PATTERN_NATIVE_LOG=str(native_log),
                       PYTHONDONTWRITEBYTECODE='1')
            env.pop('QLEISLI_KERNEL', None)
            env.pop('QLEISLI_HIERARCHY_KERNEL', None)
            start = time.monotonic()
            try:
                result = subprocess.run(command, cwd=REPO, env=env,
                                        capture_output=True, timeout=90)
                exit_code, stdout, stderr = result.returncode, result.stdout, result.stderr
            except subprocess.TimeoutExpired as error:
                exit_code, stdout, stderr = None, error.stdout or b'', error.stderr or b''
                timed_out = True
            seconds = time.monotonic() - start
            for suffix, data in [('stdout.txt', stdout), ('stderr.txt', stderr)]:
                with (OUT / (name + '.' + suffix)).open('xb') as stream:
                    stream.write(data)
            current_native = native_arguments(native_log)
            before_native = native_arguments(BEFORE / (name + '.native.jsonl'))
            # Recorded exit/count are data for comparison only, never an argv source.
            before_event = json.loads((BEFORE / (name + '.json')).read_text())
            require(len(before_native) == before_event['native_invocations'],
                    'baseline native count disagrees with its frozen raw log')
            require(before_proposal.exists() == before_event['proposal_emitted'],
                    'baseline proposal presence disagrees with its frozen event')
            stdout_equal, stdout_substitution = compare_output(
                (BEFORE / (name + '.stdout.txt')).read_bytes(), stdout,
                before_proposal, proposal, action)
            stderr_equal, stderr_substitution = compare_output(
                (BEFORE / (name + '.stderr.txt')).read_bytes(), stderr,
                before_proposal, proposal, action)
            proposal_present_equal = proposal.exists() == before_proposal.exists()
            proposal_bytes_equal = proposal_present_equal and (
                not proposal.exists() or proposal.read_bytes() == before_proposal.read_bytes())
            equality = dict(exit_code=exit_code == before_event['exit_code'],
                            stdout=stdout_equal, stderr=stderr_equal,
                            proposal_presence=proposal_present_equal,
                            proposal_bytes=proposal_bytes_equal,
                            native_argv=current_native == before_native,
                            native_count=len(current_native) == len(before_native))
            event = dict(command=command, exit_code=exit_code, timeout=timed_out,
                         seconds=seconds,
                         recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                         timestamp_note='Clock after completion; not authenticated provenance.',
                         identity_digest=initial_digest, cli_sha256=initial['cli_sha256'],
                         native_sha256=initial['native_sha256'],
                         stdout_raw=name + '.stdout.txt', stderr_raw=name + '.stderr.txt',
                         native_log=name + '.native.jsonl',
                         native_invocations=len(current_native), native_argv=current_native,
                         proposal_emitted=proposal.exists(), equality=equality,
                         output_path_substitution=dict(stdout=stdout_substitution,
                                                       stderr=stderr_substitution),
                         baseline_event='before/' + name + '.json')
            if proposal.exists():
                event.update(proposal_file='after/' + name + '.proposal.json',
                             proposal_sha256=sha(proposal), proposal_bytes=proposal.stat().st_size,
                             proposal_authority='Untrusted producer output, not native acceptance or source preservation.')
            save(OUT / (name + '.json'), event)
            rows.append(dict(case=case, profile=profile, action=action,
                             presentation=presentation, observation='after/' + name + '.json',
                             exit_code=exit_code, native_invocations=len(current_native),
                             proposal_emitted=proposal.exists(), equality=equality,
                             all_equal=all(equality.values())))
            unchanged()
            print(name, exit_code, len(current_native), proposal.exists(),
                  all(equality.values()), flush=True)
            if timed_out:
                break
        if timed_out:
            break
    unchanged()
    all_equal = len(rows) == 40 and all(row['all_equal'] for row in rows)
    save(OUT / 'summary.json', dict(rows=rows, actual_observation_count=len(rows),
         required_observation_count=40, all_equal=all_equal, timed_out=timed_out,
         source_repairs=0, retained_baseline_files=191, current_input_files=235,
         first_session_index_unchanged=True,
         native_consistency_is_not_source_preservation=True,
         scope='Only fixed check/emit-proposal commands; no program run/sample or new mathematical guarantee.'))
    save(OUT / 'identity-final.json', dict(current_identity(), identity_digest=initial_digest,
         retained_session_files_unchanged=True, baseline_map_unchanged=True,
         actual_observation_count=len(rows)))
    files = {str(path.relative_to(OUT)): file_identity(path)
             for path in sorted(OUT.rglob('*')) if path.is_file()}
    save(OUT / 'files.json', dict(files=files, self_excluded='files.json'))
    unchanged()
    print(json.dumps(dict(observations=len(rows), all_equal=all_equal,
         cli_sha256=initial['cli_sha256'], native_sha256=initial['native_sha256'],
         retained_baseline_files=191, current_input_files=235,
         total_record_bytes=sum(item['bytes'] for item in files.values())), indent=2))
    return 0 if all_equal else 1


if __name__ == '__main__':
    raise SystemExit(main())
