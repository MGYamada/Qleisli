#!/usr/bin/env python3
"""Record local documentation checks for the 109-Issue scope correction.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
MDBOOK = Path('/private/tmp/qleisli-mdbook-0.5.4-bin/mdbook')
PROSE = ['.github/ci/README.md', 'CHANGELOG.md', 'ROADMAP.md',
         'docs/src/design/ratification.md']
PACKET = 'tests/fixtures/constitution_v030/issue-count-109/'
INPUTS = sorted(set(PROSE + [
    'scripts/check_docs.py', 'scripts/check_book.py',
    'scripts/check_release_ready.py', 'scripts/test_check_release_ready.py',
    '.github/workflows/ci.yml', 'README.md', 'AGENTS.md', 'CLAUDE.md',
    'CONSTITUTION.md', 'GOVERNANCE.md', 'TRUSTBOUNDARY.md', 'STDLIB.md',
    PACKET + 'README.md', PACKET + 'scope.json', PACKET + 'documentation-results/record.py',
] + [str(p.relative_to(ROOT)) for p in (ROOT / 'docs').rglob('*') if p.is_file()]))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(name, value):
    with (HERE / name).open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def identities():
    return {name: sha(ROOT / name) for name in INPUTS}


def main():
    before = identities()
    write('before.json', before)
    commands = [
        ['git', 'diff', '--', *PROSE, 'scripts/check_release_ready.py',
         'scripts/test_check_release_ready.py'],
        ['git', 'diff', '--check'],
        [str(MDBOOK), '--version'],
        ['python3', 'scripts/check_docs.py'],
        [str(MDBOOK), 'build', 'docs'],
        ['python3', 'scripts/check_book.py'],
    ]
    write('commands.json', {'argv': commands, 'cwd': str(ROOT),
                           'environment_overrides': {'PYTHONDONTWRITEBYTECODE': '1'},
                           'mdbook_sha256': sha(MDBOOK), 'required_mdbook_version': 'mdbook v0.5.4'})
    results = []
    for index, argv in enumerate(commands):
        stdout = f'{index}.stdout.txt'
        stderr = f'{index}.stderr.txt'
        started = datetime.datetime.now(datetime.timezone.utc).isoformat()
        clock = time.monotonic()
        with (HERE / stdout).open('xb') as out, (HERE / stderr).open('xb') as err:
            run = subprocess.run(argv, cwd=ROOT, env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'},
                                 stdout=out, stderr=err)
        result = {'argv': argv, 'cwd': str(ROOT), 'started_at_utc': started,
                  'finished_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  'seconds': time.monotonic() - clock, 'exit_code': run.returncode,
                  'stdout': {'path': stdout, 'sha256': sha(HERE / stdout)},
                  'stderr': {'path': stderr, 'sha256': sha(HERE / stderr)}}
        if argv == [str(MDBOOK), '--version']:
            result['pinned_version_matches'] = (HERE / stdout).read_text().strip() == 'mdbook v0.5.4'
        results.append(result)
        print(json.dumps({'command': index, 'exit_code': run.returncode, 'seconds': result['seconds']}), flush=True)
        if run.returncode != 0 or result.get('pinned_version_matches') is False:
            break
    after = identities()
    write('after.json', after)
    passed = len(results) == len(commands) and all(
        r['exit_code'] == 0 and r.get('pinned_version_matches', True) for r in results) and before == after
    write('result.json', {'format': 'qleisli.issue-count-documentation-checks', 'version': 1,
                         'status': 'passed' if passed else 'failed', 'commands': results,
                         'inputs_unchanged_during_run': before == after,
                         'changed_inputs': [p for p in before if before[p] != after[p]],
                         'files': {p.name: sha(p) for p in sorted(HERE.iterdir()) if p.is_file()},
                         'input_scope': 'Book sources/configuration, selected active prose, checkers and packet context; not a full repository snapshot.',
                         'scope': 'Local documentation checks only. No Rust/Lean build, GitHub fetch, release approval or new Guardian act.'})
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
