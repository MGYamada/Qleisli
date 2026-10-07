"""Shared local/hosted source checks; orchestration grants no acceptance.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

import run_native_ci

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / '.github/ci/source-checks.json'


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def snapshot(root):
    """Bind working inputs, including unstaged and untracked first sources."""
    paths = subprocess.check_output(['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard'], cwd=root)
    state = hashlib.sha256()
    for name in sorted(set(paths.split(b'\0')) - {b''}):
        path = root / os.fsdecode(name)
        state.update(name + b'\0')
        if path.is_symlink():
            state.update(b'link\0' + os.fsencode(os.readlink(path)))
        elif path.is_file():
            state.update(str(path.stat().st_mode & 0o777).encode() + b'\0' + digest(path).encode())
        else:
            state.update(b'missing')
        state.update(b'\0')
    return dict(head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
                working_inputs_sha256=state.hexdigest())


def plan(group, compiler=None):
    manifest = json.loads(MANIFEST.read_text())
    if set(manifest) != {'format', 'groups'} or manifest['format'] != 1:
        raise ValueError('unknown source-check manifest')
    if group not in manifest['groups']:
        raise ValueError('unknown source-check group')
    commands = manifest['groups'][group]
    if not isinstance(commands, list) or not commands or any(
            not isinstance(command, list) or not command or
            any(not isinstance(arg, str) or not arg or '\0' in arg for arg in command)
            for command in commands):
        raise ValueError('invalid source-check command')
    if any('{compiler}' in command for command in commands) and compiler is None:
        raise ValueError('source-contracts requires an explicit --compiler')
    return [[str(compiler.resolve()) if arg == '{compiler}' else arg for arg in command]
            for command in commands]


def execute(group, compiler, output):
    output = output.resolve()
    if output.is_relative_to(ROOT):
        raise ValueError('source-check output must be outside the source checkout')
    output.mkdir(parents=True, exist_ok=False)
    report = dict(format=1, group=group, status='failed', commands=[], python=sys.version)
    try:
        commands = plan(group, compiler)
        report.update(binding=snapshot(ROOT), manifest_sha256=digest(MANIFEST),
                      commands=[dict(argv=argv, status='not-run', reason='earlier check did not complete')
                                for argv in commands])
        if expected := os.environ.get('GITHUB_SHA'):
            if report['binding']['head'] != expected:
                raise ValueError('source checks differ from the exact event commit')
        if compiler is not None:
            # Qleisli has no --version command. Bind the selected executable
            # bytes; the producer job separately records its build toolchain.
            report['compiler'] = dict(path=str(compiler.resolve()), sha256=digest(compiler))
        environment = os.environ.copy()
        if kernel := environment.get('QLEISLI_KERNEL'):
            report['kernel'] = dict(path=kernel, sha256=digest(Path(kernel)))
        environment['PYTHONDONTWRITEBYTECODE'] = '1'
        for number, command in enumerate(commands):
            task = dict(id=str(number), commands=[command])
            result = run_native_ci.run_task(task, ROOT, output / str(number), 900, environment)
            report['commands'][number] = dict(argv=command, **result)
            print(f"{group} {number + 1}/{len(commands)}: {result['status']}", flush=True)
            if result['status'] != 'passed':
                print(Path(result['log']).read_text()[-16384:], file=sys.stderr)
                raise ValueError('source check failed: ' + ' '.join(command))
        if snapshot(ROOT) != report['binding'] or digest(MANIFEST) != report['manifest_sha256']:
            raise ValueError('source inputs changed during checks')
        if compiler is not None and digest(compiler) != report['compiler']['sha256']:
            raise ValueError('compiler changed during checks')
        if 'kernel' in report and digest(Path(report['kernel']['path'])) != report['kernel']['sha256']:
            raise ValueError('kernel changed during checks')
        report['status'] = 'passed'
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        report['error'] = str(error)
        print(error, file=sys.stderr)
    (output / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
    return 0 if report['status'] == 'passed' else 1
