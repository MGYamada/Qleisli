#!/usr/bin/env python3
"""Compile independent native test drivers against one current kernel library.

Only build products are shared within a CI invocation, never test results.
Standalone comparisons build their dependency before compiling their driver.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / 'lean-kernel'
LIBRARY = PACKAGE / '.lake/build/lib/libqleisli__kernel_QleisliKernel.a'
BUILD_ENV = 'QLEISLI_NATIVE_BUILD'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_identity():
    return {str(path.relative_to(ROOT)): digest(path)
            for path in sorted(PACKAGE.rglob('*')) if path.is_file() and '.lake' not in path.parts
            and (path.suffix == '.lean' or path.name in {'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'})}


def run(command, directory, log, timeout=600):
    started = time.monotonic()
    result = subprocess.run(command, cwd=directory, capture_output=True, text=True, timeout=timeout)
    log.append(dict(command=[str(x) for x in command], cwd=str(directory), exit=result.returncode,
                    stdout=result.stdout, stderr=result.stderr, seconds=time.monotonic() - started))
    if result.returncode:
        raise RuntimeError(json.dumps(log[-1]))
    return result.stdout


def prepare(path, log):
    """Called once by the runner, after its fresh native build/audit gates."""
    if path.exists():
        raise ValueError('refuse an existing native build binding')
    before = source_identity()
    run(['lake', 'build', 'QleisliKernel:static'], PACKAGE, log)
    if before != source_identity():
        raise ValueError('kernel sources changed during native library build')
    products = {str(p.relative_to(ROOT)): digest(p) for p in sorted((PACKAGE / '.lake/build/lib/lean').rglob('*.olean'))}
    products[str(LIBRARY.relative_to(ROOT))] = digest(LIBRARY)
    data = dict(format=1, root=str(ROOT), sources=before, products=products,
                toolchain=run(['lake', 'env', 'lean', '--version'], PACKAGE, log).strip())
    path.write_text(json.dumps(data, indent=2) + '\n')
    return data


def validate(path):
    data = json.loads(path.read_text())
    if data.get('format') != 1 or data.get('root') != str(ROOT) or data.get('sources') != source_identity():
        raise ValueError('native build source identity changed')
    products = data.get('products', {})
    expected = {str(p.relative_to(ROOT)) for p in (PACKAGE / '.lake/build/lib/lean').rglob('*.olean')}
    expected.add(str(LIBRARY.relative_to(ROOT)))
    if set(products) != expected or any(digest(ROOT / name) != value for name, value in products.items()):
        raise ValueError('native build products changed')
    toolchain = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=PACKAGE, text=True).strip()
    if data.get('toolchain') != toolchain:
        raise ValueError('native build toolchain changed')
    return data


def build(project, log, timeout=240):
    """Compile fresh Main.lean; return its executable without running or accepting it."""
    binding = os.environ.get(BUILD_ENV)
    if binding:
        data = validate(Path(binding))
        log.append(dict(native_build=str(binding), library_sha256=data['products'][str(LIBRARY.relative_to(ROOT))]))
    else:
        # A standalone invocation has no earlier runner build to share.
        run(['lake', 'build', 'QleisliKernel:static'], PACKAGE, log)
    source = project / 'Main.lean'
    generated = project / 'Main.c'
    binary = project / 'native-test'
    run(['lake', 'env', 'lean', '-DwarningAsError=true', '--root=' + str(project), '-c', str(generated), str(source)], PACKAGE, log, timeout)
    run(['lake', 'env', 'leanc', '-O3', '-o', str(binary), str(generated), str(LIBRARY)], PACKAGE, log, timeout)
    if binding:
        validate(Path(binding))
    log.append(dict(driver_source_sha256=digest(source), executable_sha256=digest(binary)))
    return binary
