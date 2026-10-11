"""Create complete explicit corpus snapshots with parser-derived old spans.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
The only modified bytes are the two coherent expression spellings.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
HELPER = Path('/private/tmp/qleisli-coherent-spans')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def main():
    first = json.loads((BASE / 'first-sources.json').read_text())
    assert not (BASE / 'sources').exists(), 'refuse overwrite'
    before = json.loads((BASE / 'observations-before/capture.json').read_text())
    assert len(before['results']) == 6 and all(r['exit_code'] == 0 for r in before['results'])
    helper_sha = digest(HELPER)
    span_results = []
    records = {}
    for project in first['projects']:
        name = project['project']
        selected = Path(project['selected_predecessor'])
        target = BASE / 'sources' / name
        target.mkdir(parents=True)
        for file, expected in project['selected_files'].items():
            assert digest(selected / file) == expected, 'changed predecessor'
            assert digest(BASE / 'before-sources' / name / file) == expected, 'changed first snapshot'
            if not file.endswith('.qli'):
                continue
            shutil.copyfile(selected / file, target / file)
        source = (selected / 'kernel.qli').read_bytes()
        assert source.decode('ascii').encode('ascii') == source
        argv = [str(HELPER), str(selected / 'kernel.qli')]
        observed = subprocess.run(argv, cwd=ROOT, capture_output=True, timeout=10)
        assert observed.returncode == 0
        rows = observed.stdout.decode().strip().splitlines()
        assert len(rows) == 1, 'expected one existing coherent expression'
        start, end, bs, be, ins, ine, es, ee = map(int, rows[0].split())
        assert start < bs < be < ins < ine < es < ee == end
        assert source[start:bs] == b'do '
        assert source[be:ins] == b' <- '
        assert source[ine:es] == b';\n    pure '
        binder, input_value, body = source[bs:be], source[ins:ine], source[es:ee]
        replaced = b'basis ' + input_value + b' as ' + binder + b' { ' + body + b' }'
        migrated = source[:start] + replaced + source[end:]
        (target / 'kernel.qli').write_bytes(migrated)
        assert source[:start] == migrated[:start]
        assert source[end:] == migrated[start + len(replaced):]
        for file in sorted(n for n in project['selected_files'] if n.endswith('.qli')):
            path = name + '/' + file
            records[path] = {'before': project['selected_files'][file], 'after': digest(target / file)}
        span_results.append({'project': name, 'argv': argv, 'cwd': str(ROOT),
                             'exit_code': observed.returncode,
                             'stdout': observed.stdout.decode(), 'stderr': observed.stderr.decode(),
                             'helper_sha256': helper_sha,
                             'spans': {'expression': [start, end], 'binder': [bs, be],
                                       'input': [ins, ine], 'basis_body': [es, ee]},
                             'preserved': 'Existing binder, input and basis-body bytes, all surrounding comments/declarations and main source remain exact.'})
    assert digest(HELPER) == helper_sha
    write(BASE / 'span-observations.json', {'format': 'qleisli.coherent-basis-old-parser-spans',
                                          'version': 1, 'helper': str(HELPER), 'sha256': helper_sha,
                                          'results': span_results,
                                          'scope': 'Read-only old-parser offsets; helper bytes are identified, not independently attested as a fresh build.'})
    migration = {'format': 1, 'kind': 'explicit-source-migration', 'issue': 81,
                 'project_version': '0.3.0-alpha', 'created_utc': datetime.now(timezone.utc).isoformat(),
                 'context': 'Only the coherent expression spelling changes in two existing finite kernels. Complete four-QLI-file snapshots preserve the input, binder, basis body, ordinary type tree, exact phase/axis/owner contract, upstream pins and notices. Original roots and earlier migrations stay frozen. OLD check/run/IR observations are saved; AFTER checks, default-run comparison and emitted-IR comparison are pending. This does not establish a universal source-preservation theorem, discharge QS/PR/RS, support generic QFT or certify release readiness.',
                 'projects': [p['project'] for p in first['projects']], 'files': records,
                 'observations': ['checks.json'], 'source_selection': 'snapshot'}
    write(BASE / 'migration.pending.json', migration)
    write(BASE / 'snapshot-inventory.json', {'format': 'qleisli.coherent-basis-corpus-snapshot', 'version': 1,
                                           'first_sources_sha256': digest(BASE / 'first-sources.json'),
                                           'before_observations_sha256': digest(BASE / 'observations-before/capture.json'),
                                           'files': records, 'shared_qargo_sha256': first['shared_qargo_sha256'],
                                           'pending_migration_sha256': digest(BASE / 'migration.pending.json'),
                                           'status': 'Prepared, not selected. AFTER validation is required before manifest selection.'})
    print(json.dumps({'files': records, 'helper_sha256': helper_sha,
                      'pending_migration_sha256': digest(BASE / 'migration.pending.json')}, indent=2))


if __name__ == '__main__':
    main()
