#!/usr/bin/env python3
"""Plan/synchronize product versions and review exact-source binding updates.

No dependency versions, public surfaces, theorem types or proof gates are inferred.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

from check_verification_inventory import INVENTORY, public_surface

ROOT = Path(__file__).resolve().parents[1]
MANIFESTS = {'Cargo.toml': 'package', 'lean/lakefile.toml': '',
             'lean-kernel/lakefile.toml': '', 'python/pyproject.toml': 'project',
             'stdlib/Qargo.toml': 'qrate', 'research/semantic-kernel/Cargo.toml': 'package'}
# Product versions must have the same ordering in SemVer and Python packaging.
# An unnumbered stage normalizes to a0/b0/rc0, so numbered stages start at one.
# Attached digits (alpha10), aliases and arbitrary SemVer identifiers are not
# shared release selectors; build metadata is not a product release selector.
PRODUCT_VERSION = (r'0\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)'
                   r'(?:-(?:alpha|beta|rc)(?:\.[1-9][0-9]*)?)?')
# Never replace only the stable prefix of a prerelease or malformed version.
VERSION_SLOT = PRODUCT_VERSION + r'(?![\w.+-])'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def replace_version(text, section, version):
    parts = re.split(r'(?m)^(\[[^\n]+\]\s*\n)', text)
    index = 0 if not section else next((i + 1 for i in range(1, len(parts), 2)
                                     if parts[i].strip() == '[' + section + ']'), None)
    if index is None:
        raise ValueError('missing version section ' + section)
    parts[index], count = re.subn(r'(?m)^(version\s*=\s*)"[^"\n]+"', lambda m: m[1] + json.dumps(version), parts[index])
    if count != 1:
        raise ValueError('expected one product version in ' + section)
    return ''.join(parts)


def version_plan(root, version):
    if not re.fullmatch(PRODUCT_VERSION, version):
        raise ValueError('expected 0.y.z or 0.y.z-{alpha,beta,rc}[.N] with N >= 1; '
                         'product versions must share SemVer/Python ordering')
    changes = {}
    for name, section in MANIFESTS.items():
        text = (root / name).read_text()
        # Parse first: malformed TOML must not be repaired by textual replacement.
        tomllib.loads(text)
        changes[name] = replace_version(text, section, version)
    text = (root / 'Cargo.lock').read_text()
    tomllib.loads(text)
    chunks = text.split('[[package]]')
    matches = [i for i, chunk in enumerate(chunks[1:], 1)
               if tomllib.loads(chunk).get('name') == 'qleisli' and 'source' not in tomllib.loads(chunk)]
    if len(matches) != 1:
        raise ValueError('expected one local qleisli package in Cargo.lock')
    chunks[matches[0]] = replace_version(chunks[matches[0]], '', version)
    changes['Cargo.lock'] = '[[package]]'.join(chunks)
    text = (root / 'python/qleisli/__init__.py').read_text()
    changes['python/qleisli/__init__.py'], count = re.subn(r'(?m)^__version__ = "[^"\n]+"', '__version__ = ' + json.dumps(version), text)
    if count != 1:
        raise ValueError('expected one Python runtime version')
    name = 'lean-kernel/Protocol/Product.lean'
    if (root / name).is_file():
        text, count = re.subn(r'(?m)^(def productVersion : String := )"[^"\n]+"',
                             lambda m: m[1] + json.dumps(version), (root / name).read_text())
        if count != 1:
            raise ValueError('expected one native product version')
        changes[name] = text
    # Only current installation/version slots; never rewrite release history or
    # published versions. The source-doc URLs are an exact version-only edit.
    patterns = {
        'README.md': [(r'(Development version: )' + VERSION_SLOT, r'\g<1>' + version),
                      (r'(Compiler version `)' + VERSION_SLOT, r'\g<1>' + version),
                      (r'(Once )' + VERSION_SLOT + r'( is published)', r'\g<1>' + version + r'\g<2>'),
                      (r'(cargo install qleisli --version )' + VERSION_SLOT, r'\g<1>' + version)],
        'README.crates.md': [(r'(Package version: \*\*)' + VERSION_SLOT, r'\g<1>' + version),
                             (r'(cargo install qleisli --version )' + VERSION_SLOT, r'\g<1>' + version),
                             (r'(?m)^(qleisli\s*=\s*")' + VERSION_SLOT + r'(")$', r'\g<1>' + version + r'\g<2>'),
                             (r'(Current documentation links target `v)' + VERSION_SLOT, r'\g<1>' + version)],
        'python/README.md': [(r'(separately installed Qleisli )' + VERSION_SLOT + r'( Rust)', r'\g<1>' + version + r'\g<2>')],
        'src/lib.rs': [],
    }
    for name, rules in patterns.items():
        if not (root / name).is_file():
            continue  # Missing required public docs are diagnosed by check_docs.
        text = (root / name).read_text()
        for pattern, replacement in rules:
            text, count = re.subn(pattern, replacement, text)
            if count != 1:
                raise ValueError('expected one current version slot: ' + name + ': ' + pattern)
        if name in {'README.crates.md', 'src/lib.rs'}:
            text = re.sub(r'(https://github.com/MGYamada/Qleisli/blob/v)' + VERSION_SLOT + '/',
                          r'\g<1>' + version + '/', text)
        changes[name] = text
    return {name: text for name, text in changes.items() if text != (root / name).read_text()}


def inventory_plan(root, replacements, reviewed):
    data = json.loads((root / INVENTORY).read_text())
    sources = {row['path']: row for row in data['sources']}
    if set(reviewed) - sources.keys():
        raise ValueError('review names a file outside the existing inventory')
    rows = []
    for name, source in sources.items():
        current = (root / name).read_bytes()
        proposed = replacements[name].encode() if name in replacements else current
        new = digest(proposed)
        if source['sha256'] == new:
            continue
        # Version-only is an exact transformation of a still-bound current file.
        version_only = name in replacements and digest(current) == source['sha256']
        approval = 'version-only' if version_only else 'reviewed' if name in reviewed else 'review-required'
        if name.endswith('.rs') and public_surface(proposed.decode()) != source['surface']:
            raise ValueError('public surface changed; edit/review the inventory explicitly: ' + name)
        row = dict(path=name, before_sha256=source['sha256'], after_sha256=new, classification=approval)
        baseline = subprocess.run(['git', 'show', 'HEAD:' + name], cwd=root, capture_output=True)
        if baseline.returncode == 0:
            row.update(diff_base='git HEAD', diff_base_sha256=digest(baseline.stdout),
                       diff_base_matches_binding=digest(baseline.stdout) == source['sha256'],
                       diff=''.join(difflib.unified_diff(baseline.stdout.decode().splitlines(True),
                                   proposed.decode().splitlines(True), fromfile='HEAD:' + name, tofile=name)))
        rows.append(row)
        if approval != 'review-required':
            source['sha256'] = new
    return data, rows


def command(argv, root, report):
    result = subprocess.run(argv, cwd=root, capture_output=True, text=True)
    report['commands'].append(dict(command=argv, exit_code=result.returncode, stdout=result.stdout, stderr=result.stderr))
    if result.returncode:
        raise ValueError('check failed: ' + ' '.join(argv))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--version', help='defaults to the authoritative Cargo product version')
    parser.add_argument('--write', action='store_true', help='apply the displayed synchronization plan')
    parser.add_argument('--review-source', action='append', default=[], metavar='PATH', help='acknowledge a reviewed existing source change; never inferred from surface equality')
    parser.add_argument('--refresh-registry', action='store_true', help='rebuild, audit, replay and regenerate the theorem registry after synchronization')
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args(argv)
    report = dict(format=1, status='failed', commands=[])
    try:
        root = args.root.resolve()
        version = args.version or tomllib.loads((root / 'Cargo.toml').read_text())['package']['version']
        replacements = version_plan(root, version)
        inventory, review = inventory_plan(root, replacements, args.review_source)
        report.update(version=version, source_review=review, changes=[dict(path=name,
                      before_sha256=digest((root/name).read_bytes()), after_sha256=digest(text.encode()),
                      diff=''.join(difflib.unified_diff((root/name).read_text().splitlines(True), text.splitlines(True), fromfile=name, tofile=name)))
                      for name, text in replacements.items()])
        if args.refresh_registry and not args.write:
            raise ValueError('--refresh-registry requires --write')
        if args.write:
            if any(row['classification'] == 'review-required' for row in review):
                raise ValueError('review source changes before writing; inspect source_review and pass --review-source PATH')
            for name, text in replacements.items():
                (root / name).write_text(text)
            if review:
                (root / INVENTORY).write_text(json.dumps(inventory, indent=2) + '\n')
            if args.refresh_registry:
                command([sys.executable, 'scripts/check_schema_registry.py', '--write'], root, report)
            command([sys.executable, 'scripts/check_verification_inventory.py'], root, report)
            command([sys.executable, 'scripts/check_schema_registry.py', '--source-only'], root, report)
            command([sys.executable, 'scripts/check_docs.py'], root, report)
            command([sys.executable, 'scripts/check_editions.py'], root, report)
        report['status'] = 'passed' if args.write else 'planned'
    except (OSError, ValueError, KeyError, TypeError) as error:
        report['error'] = str(error)
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k not in {'changes', 'commands', 'source_review'}}, indent=2))
    return int(report['status'] == 'failed')


if __name__ == '__main__':
    sys.exit(main())
