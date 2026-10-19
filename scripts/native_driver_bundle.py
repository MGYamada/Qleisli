"""Prepare fresh regression drivers; select compiled code, never test results.

This optional per-invocation harness has no production acceptance authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import hashlib
import importlib
import json
import os
from pathlib import Path
import re
import subprocess

import ci_source_checks
import native_harness
from check_ratification_packet import json_object, read_file

ROOT = Path(__file__).resolve().parents[1]
BUNDLE_ENV = 'QLEISLI_NATIVE_DRIVERS'
DIGEST_ENV = 'QLEISLI_NATIVE_DRIVERS_SHA256'
SELECTOR_ENV = 'QLEISLI_NATIVE_DRIVER'
ENVIRONMENT = {BUNDLE_ENV, DIGEST_ENV, SELECTOR_ENV}
MODULES = {
    'lean-exact': 'exact', 'lean-finite': 'finite', 'lean-raw': 'raw',
    'lean-observation': 'observation', 'lean-raw-completion': 'raw_completion',
    'lean-branch-function': 'branch_function', 'lean-interference': 'interference',
    'lean-qft': 'qft', 'lean-qft-semantic': 'qft',
    'lean-qft-graph': 'qft_graph', 'lean-qpe': 'qpe',
}
LIMIT = 16 * 1024 * 1024


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def generation_binding():
    """Bind compiled-code inputs; each test still supplies fresh payloads/oracles.

    The runner retains its complete invocation source checks. Every selection
    also regenerates the original Main bytes and validates native dependencies.
    """
    paths = sorted((ROOT / 'scripts').rglob('*.py'))
    paths += [ROOT / '.github/ci/native-comparisons.json', ROOT / '.github/ci/source-checks.json']
    return dict(head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                sources={str(path.relative_to(ROOT)): digest(read_file(ROOT, str(path.relative_to(ROOT))))
                         for path in paths})


def identifiers(values):
    require(type(values) is list and values and all(type(v) is str for v in values)
            and len(set(values)) == len(values) and set(values) <= set(MODULES),
            'unknown, empty or duplicate native driver selection')
    return sorted(values)


def task_ids(tasks):
    """Keep the original manifest commands; only these eleven use this bundle."""
    result = []
    for task in tasks:
        name = task['id']
        if name not in MODULES:
            continue
        command = ['python3', 'scripts/test_lean_' + MODULES[name] + '.py']
        if name in {'lean-observation', 'lean-raw-completion', 'lean-branch-function'}:
            command += ['--record', '{record}']
        if name == 'lean-qft-semantic':
            command += ['--small', '--semantic']
        require(task['commands'] == [command] and not task.get('env'),
                'native driver manifest command changed')
        result.append(name)
    return identifiers(result)


def generate(name):
    identifiers([name])
    module = importlib.import_module('test_lean_' + MODULES[name])
    if name in {'lean-finite', 'lean-raw', 'lean-observation',
                'lean-raw-completion', 'lean-branch-function'}:
        source = module.LEAN
    elif name == 'lean-exact':
        source = module.driver_source(module.cases())
    elif name == 'lean-interference':
        source = module.driver_source(module.driver_words())
    elif name in {'lean-qft', 'lean-qft-semantic'}:
        semantic = name == 'lean-qft-semantic'
        source = module.driver_source(module.driver_cases(semantic, semantic)[0], semantic)
    else:
        source = module.driver_source(module.suite())
    require(type(source) is str and len(source.encode()) <= LIMIT,
            'native driver source exceeds its limit')
    return source


def combine(sources):
    """Scope each unchanged original body; dispatch by an explicit argument."""
    names = identifiers(list(sources))
    imports, sections, branches = set(), [], []
    for index, name in enumerate(names):
        source = sources[name]
        require(type(source) is str and len(source.encode()) <= LIMIT,
                'invalid native driver source')
        body, started = [], False
        for line in source.splitlines(keepends=True):
            if line.startswith('import ') and not started:
                require(re.fullmatch(r'import [A-Za-z0-9_. ]+\n?', line) is not None,
                        'unsupported native driver import')
                imports.add(line.rstrip() + '\n')
            else:
                require(not line.lstrip().startswith('import '),
                        'native driver import is outside its header')
                started = started or bool(line.strip())
                body.append(line)
        namespace = 'RegressionDriver_' + str(index)
        sections.append('namespace ' + namespace + '\nsection\n' + ''.join(body)
                        + '\nend\nend ' + namespace + '\n')
        branches.append('  | [' + json.dumps(name) + '] => ' + namespace + '.main')
    source = ''.join(sorted(imports)) + '\n' + '\n'.join(sections)
    source += '\ndef main (args : List String) : IO Unit := do\n  match args with\n'
    source += '\n'.join(branches) + '\n  | _ => throw (IO.userError "unknown or missing regression driver")\n'
    require(len(source.encode()) <= LIMIT, 'combined native driver source exceeds its limit')
    return source


def prepare(output, selected, log, build_binding=None):
    """Compilation is preparation only; no original main or oracle is run."""
    selected = identifiers(selected)
    output = output.resolve()
    require(not output.is_relative_to(ROOT), 'native drivers must be outside the source')
    output.mkdir(parents=True, exist_ok=False)
    before = ci_source_checks.snapshot(ROOT)
    code = generation_binding()
    if build_binding is None:
        build_binding = output / 'native-build.json'
        native_harness.prepare(build_binding, log)
    build_binding = build_binding.resolve()
    native_harness.validate(build_binding)
    build_bytes = build_binding.read_bytes()
    sources = {name: generate(name) for name in selected}
    source = combine(sources).encode()
    project = output / 'driver'
    project.mkdir()
    (project / 'Main.lean').write_bytes(source)
    binary = native_harness.compile_driver(project, log, binding=build_binding)
    require(ci_source_checks.snapshot(ROOT) == before and generation_binding() == code,
            'source changed while compiling native drivers')
    require(build_binding.read_bytes() == build_bytes, 'native build binding changed')
    native_harness.validate(build_binding)
    record = dict(format='qleisli.native-test-drivers', version=2,
                  status='prepared-not-executed', root=str(ROOT), binding=code, invocation_binding=before,
                  build=dict(path=str(build_binding), sha256=digest(build_bytes)),
                  drivers={name: dict(bytes=len(text.encode()), sha256=digest(text.encode()))
                           for name, text in sources.items()},
                  source=dict(path='driver/Main.lean', sha256=digest(source)),
                  binary=dict(path='driver/native-test', sha256=digest(binary.read_bytes())))
    raw = (json.dumps(record, sort_keys=True, indent=2) + '\n').encode()
    require(len(raw) <= LIMIT, 'native driver record exceeds its limit')
    path = output / 'drivers.json'
    with path.open('xb') as stream:
        stream.write(raw)
    log.append(dict(driver_preparation='not-executed', selectors=selected,
                    record_sha256=digest(raw), executable_sha256=record['binary']['sha256']))
    return path, digest(raw)


def selected(project, log, driver, environment=None):
    environment = os.environ if environment is None else environment
    require(all(environment.get(key) for key in ENVIRONMENT), 'incomplete explicit native driver selection')
    require(environment[SELECTOR_ENV] == driver and driver in MODULES,
            'unknown or different native driver selector')
    path = Path(environment[BUNDLE_ENV])
    require(path.is_absolute() and path.name == 'drivers.json', 'invalid native driver record path')
    raw = read_file(path.parent, path.name)
    require(len(raw) <= LIMIT and digest(raw) == environment[DIGEST_ENV], 'changed native driver record')
    record = json_object(raw, 'native driver record')
    require(set(record) == {'format', 'version', 'status', 'root', 'binding', 'build',
                            'drivers', 'source', 'binary', 'invocation_binding'}
            and record['format'] == 'qleisli.native-test-drivers'
            and type(record['version']) is int and record['version'] == 2
            and record['status'] == 'prepared-not-executed' and record['root'] == str(ROOT)
            and record['binding'] == generation_binding(), 'stale native driver context')
    invocation = record['invocation_binding']
    require(type(invocation) is dict and set(invocation) == {'head', 'working_inputs_sha256'}
            and invocation['head'] == record['binding']['head']
            and type(invocation['working_inputs_sha256']) is str
            and re.fullmatch(r'[0-9a-f]{64}', invocation['working_inputs_sha256']),
            'invalid full invocation source binding')
    require(type(record['drivers']) is dict and driver in identifiers(list(record['drivers'])),
            'missing native driver')
    source = (project / 'Main.lean').read_bytes()
    require(source == generate(driver).encode()
            and record['drivers'][driver] == dict(bytes=len(source), sha256=digest(source)),
            'generated source differs from its prepared native driver')
    for field, expected in [('source', 'driver/Main.lean'), ('binary', 'driver/native-test')]:
        row = record[field]
        require(type(row) is dict and set(row) == {'path', 'sha256'} and row['path'] == expected
                and row['sha256'] == digest(read_file(path.parent, expected)),
                'changed compiled native driver ' + field)
    build = record['build']
    require(type(build) is dict and set(build) == {'path', 'sha256'}
            and type(build['path']) is str and Path(build['path']).is_absolute(),
            'invalid native build binding')
    build_path = Path(build['path'])
    require(digest(read_file(build_path.parent, build_path.name)) == build['sha256'],
            'changed native build binding')
    native_harness.validate(build_path)
    binary = path.parent / record['binary']['path']
    log.append(dict(native_driver=driver, record_sha256=digest(raw),
                    driver_source_sha256=digest(source), executable_sha256=record['binary']['sha256']))
    return native_harness.Driver(binary, driver)
