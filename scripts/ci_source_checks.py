"""Shared local/hosted source checks; orchestration grants no acceptance.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import hashlib
import json
import os
from pathlib import Path
import re
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


def definition(group):
    manifest = json.loads(MANIFEST.read_text())
    if set(manifest) != {'format', 'groups', 'tools'} or manifest['format'] != 2:
        raise ValueError('unknown source-check manifest')
    if group not in manifest['groups']:
        raise ValueError('unknown source-check group')
    spec = manifest['groups'][group]
    if set(spec) != {'lanes', 'tools', 'prerequisites', 'prepare', 'environment', 'timeout_seconds', 'commands'}:
        raise ValueError('invalid check group metadata')
    for key in ('lanes', 'tools', 'prerequisites', 'prepare'):
        if not isinstance(spec[key], list) or any(not isinstance(v, str) or not v for v in spec[key]):
            raise ValueError('invalid check group ' + key)
    if not spec['lanes'] or not spec['tools'] or any(t not in manifest['tools'] for t in spec['tools']):
        raise ValueError('missing check lane or tool')
    if (type(spec['timeout_seconds']) is not int or not 1 <= spec['timeout_seconds'] <= 7200
            or not isinstance(spec['environment'], dict)
            or any(not isinstance(k, str) or not isinstance(v, str) or '\0' in v
                   for k, v in spec['environment'].items())):
        raise ValueError('invalid check execution settings')
    commands = spec['commands']
    if not isinstance(commands, list) or not commands or any(
            not isinstance(command, list) or not command or
            any(not isinstance(arg, str) or not arg or '\0' in arg for arg in command)
            for command in commands):
        raise ValueError('invalid source-check command')
    return spec | {'tools': {name: manifest['tools'][name] for name in spec['tools']}}


def describe(group, ancestors=()):
    if group in ancestors:
        raise ValueError('cyclic check preparation')
    spec = definition(group)
    commands, tools, environment = [], {}, {}
    for name in spec['prepare']:
        dependency = describe(name, (*ancestors, group))
        commands.extend(dependency['commands'])
        tools.update(dependency['tools'])
        environment.update(dependency['environment'])
    commands.extend(spec['commands'])
    tools.update(spec['tools'])
    environment.update(spec['environment'])
    return spec | dict(commands=commands, tools=tools, environment=environment,
                       preparation_commands=len(commands) - len(spec['commands']))


def plan(group, compiler=None):
    commands = describe(group)['commands']
    if any('{compiler}' in command for command in commands) and compiler is None:
        raise ValueError(group + ' requires an explicit --compiler')
    return [[str(compiler.resolve()) if arg == '{compiler}' else arg for arg in command]
            for command in commands]


def toolchain(spec, environment):
    observed = {}
    for name, tool in spec['tools'].items():
        if set(tool) != {'command', 'pattern'}:
            raise ValueError('invalid tool probe')
        command = run_native_ci.launch_command(tool['command'])
        result = subprocess.run(command, cwd=ROOT, env=environment, text=True,
                                capture_output=True, timeout=30)
        version = result.stdout.strip()
        observed[name] = dict(command=command, exit_code=result.returncode,
                              version=version, stderr=result.stderr.strip())
        if result.returncode or re.fullmatch(tool['pattern'], version) is None:
            raise ValueError('toolchain mismatch: ' + json.dumps(observed[name]))
    return observed


def execute(group, compiler, output):
    output = output.resolve()
    if output.is_relative_to(ROOT):
        raise ValueError('source-check output must be outside the source checkout')
    output.mkdir(parents=True, exist_ok=False)
    report = dict(format=1, group=group, status='failed', commands=[], python=sys.version)
    try:
        commands = plan(group, compiler)
        spec = describe(group)
        report.update(binding=snapshot(ROOT), manifest_sha256=digest(MANIFEST),
                      plan=spec,
                      commands=[dict(argv=argv, status='not-run', reason='earlier check did not complete')
                                for argv in commands])
        if expected := os.environ.get('GITHUB_SHA'):
            if report['binding']['head'] != expected:
                raise ValueError('source checks differ from the exact event commit')
        if compiler is not None:
            # Qleisli has no --version command. Bind the selected executable
            # bytes; the producer job separately records its build toolchain.
            report['compiler'] = dict(path=str(compiler.resolve()), sha256=digest(compiler))
        environment = run_native_ci.execution_environment()
        for key in ('CARGO_TARGET_DIR', 'QLEISLI_KERNEL'):
            if key in os.environ:
                environment[key] = os.environ[key]
        environment.update({k: v.replace('{root}', str(ROOT)) for k, v in spec['environment'].items()})
        report['environment'] = environment
        report['toolchain'] = toolchain(spec, environment)
        # Preparation is allowed to rebuild its declared checker. Bind it after
        # that phase and before any dependent tests, then check it again at exit.
        preparation = len(commands) if group == 'native-runtime' else spec['preparation_commands']
        kernel = environment.get('QLEISLI_KERNEL')
        if kernel and preparation == 0:
            report['kernel'] = dict(path=kernel, sha256=digest(Path(kernel)))
        environment['PYTHONDONTWRITEBYTECODE'] = '1'
        for number, command in enumerate(commands):
            task = dict(id=str(number), commands=[command])
            result = run_native_ci.run_task(task, ROOT, output / str(number), spec['timeout_seconds'], environment)
            report['commands'][number] = dict(argv=command, **result)
            print(f"{group} {number + 1}/{len(commands)}: {result['status']}", flush=True)
            if result['status'] != 'passed':
                print(Path(result['log']).read_text()[-16384:], file=sys.stderr)
                raise ValueError('source check failed: ' + ' '.join(command))
            if kernel and number + 1 == preparation:
                report['kernel'] = dict(path=kernel, sha256=digest(Path(kernel)))
        if snapshot(ROOT) != report['binding'] or digest(MANIFEST) != report['manifest_sha256']:
            raise ValueError('source inputs changed during checks')
        if compiler is not None and digest(compiler) != report['compiler']['sha256']:
            raise ValueError('compiler changed during checks')
        if 'kernel' in report and digest(Path(report['kernel']['path'])) != report['kernel']['sha256']:
            raise ValueError('kernel changed during checks')
        if toolchain(spec, environment) != report['toolchain']:
            raise ValueError('toolchain changed during checks')
        report['status'] = 'passed'
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        report['error'] = str(error)
        print(error, file=sys.stderr)
    (output / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
    return 0 if report['status'] == 'passed' else 1
