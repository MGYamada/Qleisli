#!/usr/bin/env python3
"""Check explicit source migration identities and obsolete-spelling rejection.

This only tests source parsing via the documentation entry point; it does not
issue native handles or establish source preservation. Semantic integration
uses the separately recorded Rust tests and independent native comparisons.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--record', type=Path, required=True)
    args = parser.parse_args()
    binary = args.binary.resolve()
    mapping = HERE / 'historical-current-map.json'
    data = json.loads(mapping.read_text())
    observed = []
    for entry in data['files']:
        old = ROOT / entry['historical_path']
        current = ROOT / entry['current_path']
        assert sha(old.read_bytes()) == entry['historical_sha256'], old
        assert sha(current.read_bytes()) == entry['current_sha256'], current
        if entry['historical_sha256'] == entry['current_sha256']:
            continue
        row = {'historical_path': entry['historical_path'], 'current_path': entry['current_path']}
        for role, path, expected in [('historical', old, 1), ('current', current, 0)]:
            argv = [str(binary), 'doc', str(path)]
            result = subprocess.run(argv, capture_output=True)
            row[role] = {'argv': argv, 'exit_code': result.returncode,
                         'stdout_sha256': sha(result.stdout), 'stderr_sha256': sha(result.stderr)}
            if result.returncode != expected:
                raise AssertionError((path, result.returncode, result.stderr.decode()))
            if role == 'historical':
                text = result.stderr.decode()
                assert 'removed' in text, (path, text)
                row[role]['diagnostic'] = text
        observed.append(row)
    args.record.parent.mkdir(parents=True, exist_ok=True)
    args.record.write_text(json.dumps({'scope': __doc__, 'binary_sha256': sha(binary.read_bytes()),
        'map_sha256': sha(mapping.read_bytes()), 'identity_files': len(data['files']),
        'obsolete_rejected_current_parsed': len(observed), 'observations': observed}, indent=2)+'\n')
    print(f"{len(data['files'])} source identities; {len(observed)} explicit obsolete/current parse pairs")


if __name__ == '__main__':
    main()
