#!/usr/bin/env python3
"""Compare the same fixed forty checks without executing recorded argv.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
BEFORE_DRIVER_SHA256 = '472756feaf2c8ef3c8ec97df25216885708ac8aaea0221147742cfa2c9a2f426'
FIRST_MAP_SHA256 = 'b7babe5509ef85fd2aa10b27d07b346083645971a7d26a608d3915f5dda6e2a2'
BEFORE_MAP_SHA256 = 'd40022d2d61500baff63e7b97439e47637b6a2f745c936174fa27d5d98f3c936'
RESULTS_BEFORE_SHA256 = 'cc2ac246e1eac8edfeffc39a215b24c8dc039a074c57b246423f03fa9c4daf26'
CHANGED_PRODUCTION = frozenset((
    'src/frontend/pattern.rs', 'src/frontend/compile/mod.rs',
    'src/frontend/sized/check.rs',
))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    with path.open('x', encoding='utf-8') as stream:
        stream.write(json.dumps(value, indent=2) + '\n')


def load_before():
    if sha(ROOT / 'driver.py') != BEFORE_DRIVER_SHA256:
        raise ValueError('Frozen before driver changed')
    spec = importlib.util.spec_from_file_location('parameter_before_fixed', ROOT / 'driver.py')
    before = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(before)
    # The guarded module defines fixed command/identity functions. main is
    # never called; no record supplies executable code or argv.
    return before


def main():
    if len(sys.argv) != 2 or not re.fullmatch(r'attempt-[0-9]{2}', sys.argv[1]):
        raise SystemExit('usage: observe-after.py attempt-NN; root runs after code/build freeze')
    out = ROOT / ('after-' + sys.argv[1])
    out.mkdir(exist_ok=False)
    (out / 'executed-driver.py.txt').open('xb').write(Path(__file__).read_bytes())
    after_driver_sha = sha(Path(__file__))
    plan_sha = sha(ROOT / 'results-after-plan.md')
    protected = {
        'driver.py': BEFORE_DRIVER_SHA256,
        'first-files.json': FIRST_MAP_SHA256,
        'files-before.json': BEFORE_MAP_SHA256,
        'results-before.md': RESULTS_BEFORE_SHA256,
    }
    try:
        for name, digest in protected.items():
            if sha(ROOT / name) != digest:
                raise ValueError('Protected before record changed: ' + name)
        frozen = json.loads((ROOT / 'files-before.json').read_text())['files']
        if len(frozen) != 200:
            raise ValueError('Frozen before packet count changed')
        for name, row in frozen.items():
            if sha(ROOT / name) != row['sha256']:
                raise ValueError('Frozen before packet changed: ' + name)
        before = load_before()
        baseline = json.loads((ROOT / 'before/identity.before.json').read_text())['identity']
        final_baseline = json.loads((ROOT / 'before/identity.final.json').read_text())['identity']
        original = json.loads((ROOT / 'before/summary.json').read_text())
        if baseline != final_baseline or original['actual_observation_count'] != 40:
            raise ValueError('Original capture is not the complete unchanged baseline')
        expected_order = [(case, profile, presentation) for case in before.CASES
                          for profile, presentation in (
                              ('finite', 'text'), ('finite', 'json'),
                              ('selected-auto', 'text'), ('selected-auto', 'json'))]
        if [(r['case'], r['profile'], r['presentation']) for r in original['rows']] != expected_order:
            raise ValueError('Original forty checks differ from authored forms')
        current = before.identity()  # Captured only now, after root's code/build barrier.
        if sys.version_info < (3, 11):
            raise ValueError('Python 3.11+ required')
        if current['cli_sha256'] == baseline['cli_sha256']:
            raise ValueError('Rebuilt CLI must differ from the original baseline bytes')
        if current['native_sha256'] != baseline['native_sha256']:
            raise ValueError('Selected native checker changed')
        if set(current['files']) != set(baseline['files']):
            raise ValueError('Declared external input path set changed')
        changed = {name: dict(before=baseline['files'][name], after=digest)
                   for name, digest in current['files'].items()
                   if digest != baseline['files'][name]}
        if set(changed) != CHANGED_PRODUCTION:
            raise ValueError('External changes differ from the three authorized source paths: ' + repr(set(changed)))
    except (OSError, ValueError, KeyError, TypeError) as error:
        save(out / 'startup-failure.json', dict(child_commands_started=0, error=repr(error)))
        return 1
    save(out / 'identity.before.json', dict(identity=current, changed_production=changed,
         protected_baseline=protected, before_packet_file_count=len(frozen),
         recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
         python_executable=sys.executable, python_version=sys.version,
         scope='Declared current bytes captured at execution; no complete build/proof closure or attestation.'))

    def unchanged():
        for name, digest in protected.items():
            if sha(ROOT / name) != digest:
                raise ValueError('Protected before record changed: ' + name)
        for name, row in frozen.items():
            if sha(ROOT / name) != row['sha256']:
                raise ValueError('Original before packet changed: ' + name)
        if sha(Path(__file__)) != after_driver_sha or sha(ROOT / 'results-after-plan.md') != plan_sha:
            raise ValueError('After driver/plan changed during capture')
        if before.identity() != current:
            raise ValueError('Current source/CLI/native/contract bytes changed during capture')

    comparisons = []
    for case, profile, presentation in expected_order:
        unchanged()
        name = f'{case}-{profile}-check-{presentation}'
        native_log = out / (name + '.native.jsonl')
        native_log.touch(exist_ok=False)
        argv = before.command(case, profile, presentation)
        # Same original source, entry/profile and native-wrapper paths. Only
        # the wrapper's log destination changes via this recording variable.
        env = dict(os.environ, QLEISLI_PARAMETER_NATIVE_LOG=str(native_log),
                   PYTHONDONTWRITEBYTECODE='1')
        env.pop('QLEISLI_KERNEL', None)
        env.pop('QLEISLI_HIERARCHY_KERNEL', None)
        stdout_path, stderr_path = out / (name + '.stdout.txt'), out / (name + '.stderr.txt')
        begin = time.monotonic()
        exit_code, launch_error, timed_out = None, None, False
        with stdout_path.open('xb') as output, stderr_path.open('xb') as errors:
            try:
                result = subprocess.run(argv, cwd=before.REPO, env=env, stdout=output,
                                        stderr=errors, check=False, timeout=90)
                exit_code = result.returncode
            except OSError as error:
                launch_error = repr(error)
            except subprocess.TimeoutExpired:
                timed_out = True
        stdout, stderr = stdout_path.read_bytes(), stderr_path.read_bytes()
        native_raw = native_log.read_bytes()
        native_count = len(native_raw.splitlines())
        event = dict(command=argv, exit_code=exit_code, seconds=time.monotonic() - begin,
                     recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                     timestamp_note='Clock after completion; not authenticated provenance.',
                     launch_error=launch_error, timed_out=timed_out,
                     native_invocations=native_count, native_argv_log=native_log.name,
                     stdout_raw=stdout_path.name, stderr_raw=stderr_path.name,
                     stdout_sha256=sha(stdout_path), stderr_sha256=sha(stderr_path))
        save(out / (name + '.json'), event)
        old = json.loads((ROOT / 'before' / (name + '.json')).read_text())
        comparison = dict(case=case, profile=profile, presentation=presentation,
            command_equal=argv == old['command'], exit_equal=exit_code == old['exit_code'],
            stdout_raw_equal=stdout == (ROOT / 'before' / (name + '.stdout.txt')).read_bytes(),
            stderr_raw_equal=stderr == (ROOT / 'before' / (name + '.stderr.txt')).read_bytes(),
            native_argv_raw_equal=native_raw == (ROOT / 'before' / (name + '.native.jsonl')).read_bytes(),
            native_count_equal=native_count == old['native_invocations'],
            actual_exit_code=exit_code, actual_native_invocations=native_count,
            observation=str((out / (name + '.json')).relative_to(ROOT)))
        comparisons.append(comparison)
        if launch_error or timed_out:
            save(out / 'incomplete.json', dict(comparisons=comparisons,
                 reason='Real launch failure/timeout retained; no child exit invented.'))
            return 1
        unchanged()
        print(name, exit_code, native_count, all(comparison[k] for k in (
            'command_equal', 'exit_equal', 'stdout_raw_equal', 'stderr_raw_equal',
            'native_argv_raw_equal', 'native_count_equal')), flush=True)
    equal = len(comparisons) == 40 and all(row[key] for row in comparisons for key in (
        'command_equal', 'exit_equal', 'stdout_raw_equal', 'stderr_raw_equal',
        'native_argv_raw_equal', 'native_count_equal'))
    save(out / 'summary.json', dict(status='all_equal' if equal else 'differences-observed',
         comparisons=comparisons, actual_observation_count=len(comparisons),
         actual_native_calls=sum(row['actual_native_invocations'] for row in comparisons),
         original_before_packet_unchanged=True, output_normalizations=0,
         recorded_commands_executed=False, checks_only_no_emits_or_runtime=True,
         scope='Exact bounded check-observation comparison only; no common-checker completion, source-preservation proof, guarantee or Issue closure.'))
    save(out / 'identity.final.json', dict(identity=before.identity(), selected_inputs_unchanged=True,
         original_before_packet_unchanged=True, protected_baseline=protected))
    files = {p.name: dict(sha256=sha(p), bytes=p.stat().st_size)
             for p in sorted(out.iterdir()) if p.is_file()}
    save(out / 'files.json', dict(files=files, self_excluded='files.json'))
    return 0 if equal else 1


if __name__ == '__main__':
    raise SystemExit(main())
