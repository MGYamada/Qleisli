"""Passively verify original qmatch counterexample and repair history.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import hashlib
import io
import json
import lzma
from pathlib import Path, PurePosixPath
import tarfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
README = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/README.md"
ARCHIVE = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/first.tar.xz"
INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/index.json"
VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/validation.json"
OPERANDS = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/operands-first.tar.xz"
OPERAND_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/operands-index.json"
OPERAND_VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/operands-validation.json"
TRANSPORT = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/transport-first.tar.xz"
TRANSPORT_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/transport-index.json"
TRANSPORT_VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/transport-validation.json"
NATIVE_BINDING = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/native-binding-first.tar.xz"
NATIVE_BINDING_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/native-binding-index.json"
NATIVE_BINDING_VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/native-binding-validation.json"
CI_TYPECHECK = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/ci-typecheck-first.tar.xz"
CI_TYPECHECK_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/ci-typecheck-index.json"
CI_TYPECHECK_VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/ci-typecheck-validation.json"
NOMINAL = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/nominal-first.tar.xz"
NOMINAL_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/nominal-index.json"
NOMINAL_VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/nominal-validation.json"
BODY_ROOT = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030"
OWNER_FLOW_ARCHIVE = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/owner-flow-first.tar.xz"
OWNER_FLOW_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/owner-flow-index.json"
RUNTIME_SIGNATURE_ARCHIVE = "tests/fixtures/authoring_sessions/runtime-signature-v030/first.tar.xz"
RUNTIME_SIGNATURE_INDEX = "tests/fixtures/authoring_sessions/runtime-signature-v030/index.json"
RUNTIME_SIGNATURE_VALIDATION = "tests/fixtures/authoring_sessions/runtime-signature-v030/validation.json"
RUNTIME_SIGNATURE_README = "tests/fixtures/authoring_sessions/runtime-signature-v030/README.md"
RUNTIME_ROOT_ARCHIVE = "tests/fixtures/authoring_sessions/runtime-signature-v030/runtime-root-first.tar.xz"
RUNTIME_ROOT_INDEX = "tests/fixtures/authoring_sessions/runtime-signature-v030/runtime-root-index.json"
RUNTIME_ROOT_VALIDATION = "tests/fixtures/authoring_sessions/runtime-signature-v030/runtime-root-validation.json"
RUNTIME_TRANSPORT_ARCHIVE = "tests/fixtures/authoring_sessions/runtime-signature-v030/runtime-transport-first.tar.xz"
RUNTIME_TRANSPORT_INDEX = "tests/fixtures/authoring_sessions/runtime-signature-v030/runtime-transport-index.json"
RUNTIME_TRANSPORT_VALIDATION = "tests/fixtures/authoring_sessions/runtime-signature-v030/runtime-transport-validation.json"
RUNTIME_SOURCE_ARCHIVE = "tests/fixtures/authoring_sessions/runtime-signature-v030/runtime-source-first.tar.xz"
RUNTIME_SOURCE_INDEX = "tests/fixtures/authoring_sessions/runtime-signature-v030/runtime-source-index.json"
RUNTIME_SOURCE_VALIDATION = "tests/fixtures/authoring_sessions/runtime-signature-v030/runtime-source-validation.json"
RUNTIME_STATIC_ARCHIVE = "tests/fixtures/authoring_sessions/runtime-signature-v030/static-first.tar.xz"
RUNTIME_STATIC_INDEX = "tests/fixtures/authoring_sessions/runtime-signature-v030/static-index.json"
RUNTIME_STATIC_VALIDATION = "tests/fixtures/authoring_sessions/runtime-signature-v030/static-validation.json"
RUNTIME_STATIC_V2_ARCHIVE = "tests/fixtures/authoring_sessions/runtime-signature-v030/static-v2-first.tar.xz"
RUNTIME_STATIC_V2_INDEX = "tests/fixtures/authoring_sessions/runtime-signature-v030/static-v2-index.json"
RUNTIME_STATIC_V2_VALIDATION = "tests/fixtures/authoring_sessions/runtime-signature-v030/static-v2-validation.json"
RUNTIME_GENERIC_ARCHIVE = "tests/fixtures/authoring_sessions/runtime-signature-v030/generic-calls-first.tar.xz"
RUNTIME_GENERIC_INDEX = "tests/fixtures/authoring_sessions/runtime-signature-v030/generic-calls-index.json"
RUNTIME_GENERIC_VALIDATION = "tests/fixtures/authoring_sessions/runtime-signature-v030/generic-calls-validation.json"
COMPILER_ARCHIVE = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/compiler-first.tar.xz"
COMPILER_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/compiler-index.json"
COMPILER_VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/compiler-validation.json"
TARGET_ARCHIVE = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/nominal-target-first.tar.xz"
TARGET_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/nominal-target-index.json"
TARGET_VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/nominal-target-validation.json"
CONTEXT_VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/context-validation.json"
CONTEXT_V2_ARCHIVE = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/context-v2-first.tar.xz"
CONTEXT_V2_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/context-v2-index.json"
CONTEXT_V2_VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/context-v2-validation.json"
PROVIDER_ARCHIVE = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/provider-cache-first.tar.xz"
PROVIDER_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/provider-cache-index.json.xz"
PROVIDER_VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/provider-cache-validation.json.xz"
SEQUENCE_ARCHIVE = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/sequence-first.tar.xz"
SEQUENCE_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/sequence-index.json.xz"
SECTOR_SEQUENCE_ARCHIVE = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/sequence-sector-first.tar.xz"
SECTOR_SEQUENCE_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/sequence-sector-index.json.xz"
SEQUENCE_TESTS_ARCHIVE = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/sequence-tests-v3-first.tar.xz"
SEQUENCE_TESTS_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/sequence-tests-v3-index.json"
FRAME_CASES = "tests/fixtures/qmatch_v030/frame-execution-cases.json"


def history_json(path):
    """Read bounded inert metadata, including explicitly compressed JSON."""
    data = path.read_bytes()
    if len(data) > 4 * 1024 * 1024:
        raise ValueError('oversized history metadata')
    if path.suffix == '.xz':
        decoder = lzma.LZMADecompressor(format=lzma.FORMAT_XZ, memlimit=64 * 1024 * 1024)
        data = decoder.decompress(data, max_length=4 * 1024 * 1024 + 1)
        if len(data) > 4 * 1024 * 1024 or not decoder.eof or decoder.unused_data:
            raise ValueError('incomplete, trailing or oversized history metadata')
    return json.loads(data)


def bounded_history(archive_path, index_path):
    """Read inert member bytes only; never extract or replay saved commands."""
    index = history_json(index_path)
    if index['archive'] != archive_path.name:
        raise ValueError('history archive name differs')
    packed = archive_path.read_bytes()
    if (len(packed) > 1024 * 1024 or len(packed) != index['bytes']
            or hashlib.sha256(packed).hexdigest() != index['sha256']):
        raise ValueError('history archive identity/capacity differs')
    decoder = lzma.LZMADecompressor(format=lzma.FORMAT_XZ, memlimit=64 * 1024 * 1024)
    expanded = decoder.decompress(packed, max_length=32 * 1024 * 1024 + 1)
    if len(expanded) > 32 * 1024 * 1024 or not decoder.eof or decoder.unused_data:
        raise ValueError('incomplete, trailing or oversized history')
    members = {}
    with tarfile.open(fileobj=io.BytesIO(expanded)) as archive:
        for entry in archive:
            name = PurePosixPath(entry.name)
            if (not entry.isfile() or name.is_absolute() or '..' in name.parts
                    or entry.name in members or entry.name not in index['records']):
                raise ValueError('unlisted, duplicate or nonregular history member')
            content = archive.extractfile(entry).read()
            row = index['records'][entry.name]
            if len(content) != row['bytes'] or hashlib.sha256(content).hexdigest() != row['sha256']:
                raise ValueError('history member identity differs')
            members[entry.name] = content
    if set(members) != set(index['records']):
        raise ValueError('history member missing')
    return members


class OriginalCouplingHistory(unittest.TestCase):
    def test_sequence_transport_test_migration_preserves_real_failure(self):
        members = bounded_history(ROOT / SEQUENCE_TESTS_ARCHIVE, ROOT / SEQUENCE_TESTS_INDEX)
        self.assertEqual(history_json(ROOT / SEQUENCE_TESTS_INDEX)['sha256'],
                         '2277e15144bb39b3e48697278748cf2f63ead09da05428e9e7f7feb3329818d0')
        identity = json.loads(members['hosted/identity.json.txt'])
        self.assertEqual(hashlib.sha256(members['first/Tests.lean.before.txt']).hexdigest(),
                         identity['original_tests_sha256'])
        self.assertIn(b'Tests.lean:1632:82: error:', members['hosted/full-tests/stdout.txt'])
        for label, code in [('qmatch-tests-v3-full', 1), ('qmatch-tests-v3-full-correct-path', 0)]:
            report = json.loads(members['checks/' + label + '/report.json.txt'])
            self.assertEqual(report['exit_code'], code)
            self.assertTrue(report['stable_source'])
            self.assertEqual(report['before'], report['after'])
            for digest in report['before'].values():
                self.assertEqual(hashlib.sha256(members['objects/' + digest]).hexdigest(), digest)

    def test_sequence_sector_integration_keeps_actual_inputs_and_refusals(self):
        members = bounded_history(ROOT / SECTOR_SEQUENCE_ARCHIVE, ROOT / SECTOR_SEQUENCE_INDEX)
        index = history_json(ROOT / SECTOR_SEQUENCE_INDEX)
        self.assertEqual(index['sha256'], '702430a45960dd37a1b8e745c1d998cef4874d80d1bafef79f0ff8e81f366ed4')
        self.assertEqual(len(members), 111)
        self.assertEqual(len(index['checks']), 20)
        for label, code in index['checks'].items():
            suffix = label.removeprefix('qmatch-sequence-')
            report = json.loads(members['checks/' + suffix + '/report.json.txt'])
            self.assertEqual(report['exit_code'], code)
            self.assertTrue(report['stable_source'])
            self.assertEqual(report['before'], report['after'])
            for digest in report['before'].values():
                self.assertEqual(hashlib.sha256(members['objects/' + digest]).hexdigest(), digest)
        for suffix in ['msrv-185-pinned', 'msrv-clippy']:
            report = json.loads(members['checks/' + suffix + '/report.json.txt'])
            self.assertEqual(report['exit_code'], 0)
            self.assertTrue(report['rustc_version'].startswith('rustc 1.85.0 '))
        self.assertIn(b'15 passed; 0 failed; 0 ignored', members['checks/native-interval-faults/stdout.txt'])
        self.assertIn(b'28 passed; 0 failed; 0 ignored', members['checks/selected-runtime/stdout.txt'])
        self.assertIn(b'22900 kernel/transport declarations', members['checks/current-audit/stdout.txt'])
        result = json.loads(members['checks/original-cli/stdout.txt'])['result']
        self.assertTrue(result['runtime_result_checked'])
        self.assertFalse(result['source_preservation_verified'])
        first = bounded_history(ROOT / SEQUENCE_ARCHIVE, ROOT / SEQUENCE_INDEX)
        self.assertEqual(members['unchanged-first/main.qli.txt'], first['source-first/multiple-selections/main.qli.txt'])
        self.assertEqual(json.loads(members['scope.json.txt'])['issues_open'], [64, 195, 142])

    def test_sequence_first_programs_and_actual_refusals_are_unchanged(self):
        self.assertEqual(hashlib.sha256((ROOT / SEQUENCE_INDEX).read_bytes()).hexdigest(),
                         'c992bbb6fcc5ee8a6383fc1023e2f185da68d0dc241142830926174eeddd8e00')
        members = bounded_history(ROOT / SEQUENCE_ARCHIVE, ROOT / SEQUENCE_INDEX)
        self.assertEqual(len(members), 111)
        plan_bytes = members['source-first/plan.json.txt']
        report_bytes = members['source-first/observations-first/report.json.txt']
        self.assertEqual(hashlib.sha256(plan_bytes).hexdigest(),
                         'dd81eed676367ba7fdb64cb0c70f64895113f5792495ef787406b35ea13b6440')
        self.assertEqual(hashlib.sha256(report_bytes).hexdigest(),
                         '1ba001d9b43ed9f52a2c956ab198f692bd52f395c3fa47d9aa9d6625c5e1c7be')
        plan, report = json.loads(plan_bytes), json.loads(report_bytes)
        self.assertTrue(report['unchanged'])
        self.assertEqual(report['before'], report['after'])
        self.assertEqual(plan['max_physical_bits'], 4)
        self.assertEqual([row['exit_code'] for row in report['records']], [0, 1, 1, 1, 1, 1, 1])
        for row in plan['cases']:
            for name, digest in row['inputs'].items():
                content = members['source-first/' + row['name'] + '/' + name + '.txt']
                self.assertEqual(hashlib.sha256(content).hexdigest(), digest)
        for row in report['records']:
            for stream in ('stdout', 'stderr'):
                content = members['source-first/observations-first/' + row['name'] + '.' + stream + '.txt']
                self.assertEqual(hashlib.sha256(content).hexdigest(), row[stream + '_sha256'])
            self.assertEqual(json.loads(members['source-first/observations-first/' + row['name'] + '.stdout.txt']),
                             row['document'])
        self.assertIn(b'body effect', members['source-first/observations-first/hidden-observe-negative.stdout.txt'])

    def test_sequence_first_component_errors_and_separate_repairs_are_retained(self):
        members = bounded_history(ROOT / SEQUENCE_ARCHIVE, ROOT / SEQUENCE_INDEX)
        index = history_json(ROOT / SEQUENCE_INDEX)
        self.assertEqual(len(index['checks']), 15)
        failed = {'qmatch-sequence-current-source-guard', 'qmatch-sequence-interval-tests-first',
                  'qmatch-sequence-intrinsic-event-build', 'qmatch-sequence-source-tests-first'}
        for label in index['checks']:
            report = json.loads(members['checks/' + label + '/report.json.txt'])
            self.assertEqual(report['exit_code'], int(label in failed))
            self.assertTrue(report['stable_source'])
            self.assertEqual(report['before'], report['after'])
            for digest in report['before'].values():
                self.assertEqual(hashlib.sha256(members['source-objects/' + digest + '.txt']).hexdigest(), digest)
        self.assertIn(b'failed to synthesize', members['checks/qmatch-sequence-source-tests-first/stdout.txt'])
        self.assertIn(b'LawfulBEq Environment', members['checks/qmatch-sequence-intrinsic-event-build/stdout.txt'])
        self.assertIn(b'unexpected identifier', members['checks/qmatch-sequence-interval-tests-first/stdout.txt'])
        self.assertIn(b'stale source identity: lean-kernel/QleisliKernel.lean',
                      members['checks/qmatch-sequence-current-source-guard/stderr.txt'])
        self.assertIn(b'Audited 22705 kernel/transport declarations',
                      members['checks/qmatch-sequence-compiled-audit-first/stdout.txt'])
        repaired = json.loads(members['checks/qmatch-sequence-source-tests-guard/report.json.txt'])
        self.assertLess(repaired['child_peak_rss_bytes'], 1024 * 1024 * 1024)

    def test_provider_profiles_keep_first_controls_and_exact_failed_sources(self):
        members = bounded_history(ROOT / PROVIDER_ARCHIVE, ROOT / PROVIDER_INDEX)
        first = json.loads(members['first-checks/observations.json.txt'])
        after = json.loads(members['after-checks/observations.json.txt'])
        plan = json.loads(members['control-plan.json.txt'])
        self.assertTrue(first['stable'] and after['stable'])
        self.assertEqual([r['exit_code'] for r in first['records']], [0, 0, 1, 1, 1, 1, 1])
        self.assertEqual([r['exit_code'] for r in after['records']], [0, 0, 0, 1, 1, 1, 1])
        for row in plan['cases']:
            for name, digest in row['inputs'].items():
                content = members['first/' + row['name'] + '/' + name + '.txt']
                self.assertEqual(hashlib.sha256(content).hexdigest(), digest)
        self.assertEqual(first['before']['sources'], after['before']['sources'])
        self.assertIn(b'different freshly checked Raw/source graph',
                      members['first-checks/four-controlled-permutations/stdout.txt'])
        self.assertIn(b'no entry found for key', members['checks/compiler/stdout.txt'])
        self.assertIn(b'does not have a field named `function`', members['checks/compiler-second/stderr.txt'])
        for label in ['final-stable', 'final-msrv', 'compiler-third', 'msrv-compiler', 'clippy', 'msrv-clippy']:
            report = json.loads(members['checks/' + label + '/report.json.txt'])
            self.assertEqual(report['exit_code'], 0)
            self.assertEqual(report['before'], report['after'])
        validation = history_json(ROOT / PROVIDER_VALIDATION)
        self.assertEqual(validation['stable_integration'], 88)
        self.assertEqual(validation['msrv_integration'], 88)
        self.assertEqual(validation['stable_compiler_units'], 136)
        self.assertEqual(validation['msrv_compiler_units'], 136)
        self.assertFalse(validation['limits_raised'])
        self.assertEqual(validation['issues_open'], [64, 195, 142])

    def test_context_v2_keeps_exact_first_inputs_and_separate_native_observations(self):
        members = bounded_history(ROOT / CONTEXT_V2_ARCHIVE, ROOT / CONTEXT_V2_INDEX)
        original = bounded_history(ROOT / BODY_ROOT / 'context-first.tar.xz',
                                   ROOT / BODY_ROOT / 'context-index.json')
        first = json.loads(original['source-first/observations.json.txt'])
        after = json.loads(members['after/observations.json.txt'])
        self.assertTrue(after['stable'])
        self.assertEqual(after['before'], after['after'])
        inputs = [json.loads(original['source-first/' + row['name'] + '/plan.json.txt'])['inputs']
                  for row in first['records']]
        self.assertEqual([row['inputs'] for row in after['records']], inputs)
        self.assertEqual([row['exit_code'] for row in after['records']],
                         [0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1])
        refs = json.loads(members['source-review/refs.json.txt'])
        kernel = None
        for suffix, count in [('selected', 26), ('units', 15),
                              ('msrv-selected', 26), ('msrv-units', 15)]:
            prefix = 'observations/context-native-v2-' + suffix + '/'
            report = json.loads(members[prefix + 'report.json.txt'])
            self.assertEqual(report['exit_code'], 0)
            self.assertEqual(report['before'], report['after'])
            self.assertTrue(report['stable_source'])
            self.assertIn(f'{count} passed; 0 failed; 0 ignored'.encode(),
                          members[prefix + 'stdout.txt'])
            if kernel is None:
                kernel = report['kernel_sha256']
            self.assertEqual(report['kernel_sha256'], kernel)
            for name, digest in report['before'].items():
                self.assertEqual(refs[digest]['path'], name)
                self.assertIn(refs[digest]['patch'], members)
        validation = json.loads((ROOT / CONTEXT_V2_VALIDATION).read_text())
        self.assertEqual(validation['issues_open'], [64, 195, 142])
        self.assertFalse(validation['limits_raised'])
        self.assertEqual(validation['ignored_native_tests'], 0)

    def test_context_history_preserves_failures_and_separate_repair(self):
        root = ROOT / BODY_ROOT
        members = bounded_history(root / 'context-first.tar.xz', root / 'context-index.json')
        first = json.loads(members['source-first/observations.json.txt'])
        self.assertTrue(first['stable'])
        self.assertEqual(len(first['records']), 11)
        before = json.loads(members['study/source-frame-first.json.txt'])
        after = json.loads(members['study/source-frame-second.json.txt'])
        self.assertEqual(len(before['cases']), 18)
        for old, new in zip(before['cases'], after['cases']):
            if old['name'] == 'public-isometry-preserved':
                self.assertEqual(old['artifact']['programs'][0]['declared_effect'], 'isometry')
                self.assertEqual(new['artifact']['programs'][0]['declared_effect'], 'iso')
            else:
                self.assertEqual(old, new)
        failed = members['observations/context-sector-comparison-first/stdout.txt']
        fixed = members['observations/context-sector-comparison-second/stdout.txt']
        self.assertIn(b'work=0; expected=true', failed)
        self.assertIn(b'cases=18; mismatches=1', failed)
        self.assertIn(b'cases=18; mismatches=0', fixed)
        self.assertIn(b'maximum number of heartbeats', members['observations/context-sector-first/stdout.txt'])
        self.assertIn(b'shifted_non_qmatch_slice_not_source_evidence', members['study/fourth/stdout.txt'])
        self.assertIn(b'depends on axioms: [propext]', members['study/fourth/stdout.txt'])
        validation = json.loads((ROOT / CONTEXT_VALIDATION).read_text())
        self.assertFalse(validation['limits_raised'])
        self.assertEqual(validation['issues_open'], [64, 195, 142])
        current = json.loads((ROOT / FRAME_CASES).read_text())['cases']
        self.assertEqual({row['name'] for row in current}, {row['name'] for row in after['cases']})
        faults = {row['name']: row['native_code'] for row in current if not row['expected']}
        for name in ['wrong-actual-phase', 'wrong-controlled-phase', 'nominal-relative-phase']:
            self.assertEqual(faults[name], 'equation')

    def test_nominal_target_history_keeps_original_programs_and_budget_failures(self):
        members = bounded_history(ROOT / TARGET_ARCHIVE, ROOT / TARGET_INDEX)
        before = json.loads(members['first/observations.json.txt'])
        after = json.loads(members['after/observations.json.txt'])
        self.assertTrue(before['stable'])
        self.assertEqual([row['exit_code'] for row in before['records']], [1] * 6)
        self.assertEqual([row['exit_code'] for row in after['records']], [0, 0, 0, 0, 1, 1])
        for row in after['records']:
            prefix = 'first/' + row['name'] + '/'
            inputs = json.loads(members[prefix + 'plan.json.txt'])['inputs']
            self.assertEqual(row['inputs'], inputs)
            for name, digest in inputs.items():
                self.assertEqual(hashlib.sha256(members[prefix + name + '.txt']).hexdigest(), digest)
            if row['exit_code'] == 0:
                result = json.loads(members['after/' + row['name'] + '/stdout.txt'])['result']
                self.assertTrue(result['runtime_result_checked'])
                self.assertFalse(result['source_preservation_verified'])
        self.assertIn(b'built-in finite target', members['first/record-target/stdout.txt'])
        for suffix, diagnostic in [('eighth', b'work'),
                                   ('stable-units', b'must exercise a partially emitted body'),
                                   ('clippy', b'large size difference between variants')]:
            prefix = 'observations/nominal-target-' + suffix + '/'
            report = json.loads(members[prefix + 'report.json.txt'])
            self.assertEqual(report['exit_code'], 101)
            self.assertEqual(report['before'], report['after'])
            self.assertIn(diagnostic, members[prefix + 'stdout.txt'] + members[prefix + 'stderr.txt'])
        validation = json.loads((ROOT / TARGET_VALIDATION).read_text())
        self.assertEqual(validation['issues'], {'64': 'OPEN', '195': 'OPEN'})
        for key in ['stable_integration_tests', 'msrv_integration_tests']:
            self.assertEqual(validation[key], 77)
        for key in ['stable_unit_tests', 'msrv_unit_tests']:
            self.assertEqual(validation[key], 31)
        for suffix in ['final-selected', 'final-msrv-units', 'clippy-second']:
            report = json.loads(members['observations/nominal-target-' + suffix + '/report.json.txt'])
            self.assertEqual(report['exit_code'], 0)
            self.assertEqual(report['before'], report['after'])

    def test_nominal_compiler_history_preserves_first_sources_and_api_failures(self):
        folder = ROOT / BODY_ROOT
        members = bounded_history(folder / 'nominal-compiler-first.tar.xz',
                                  folder / 'nominal-compiler-index.json')
        self.assertEqual(len(members), 73)
        for label, diagnostic in [('third', b'mismatched types'),
                                  ('fourth', b"doesn't implement")]:
            prefix = 'observations/nominal-qmatch-' + label + '/'
            self.assertIn(diagnostic, members[prefix + 'stderr.txt'])
            report = json.loads(members[prefix + 'report.json.txt'])
            self.assertEqual(report['exit_code'], 101)
            self.assertEqual(report['before'], report['after'])
        after = json.loads(members['after/observations.json.txt'])
        self.assertEqual([row['exit_code'] for row in after['records']], [0, 0, 0, 0, 1, 1])
        before = bounded_history(ROOT / COMPILER_ARCHIVE, ROOT / COMPILER_INDEX)
        original = json.loads(before['first/observations.json.txt'])
        original_inputs = [json.loads(before['first/' + row['name'] + '/plan.json.txt'])['inputs']
                           for row in original['records']]
        self.assertEqual([row['inputs'] for row in after['records']], original_inputs)
        validation = json.loads((folder / 'nominal-compiler-validation.json').read_text())
        self.assertEqual(validation['issues'], {'64': 'OPEN', '195': 'OPEN'})
        self.assertEqual(validation['stable_tests'], 74)
        self.assertEqual(validation['msrv_tests'], 40)

    def test_compiler_history_keeps_real_projection_and_provider_refusals(self):
        members = bounded_history(ROOT / COMPILER_ARCHIVE, ROOT / COMPILER_INDEX)
        self.assertEqual(len(members), 66)
        first = json.loads(members['first/observations.json.txt'])
        self.assertEqual(len(first['records']), 6)
        self.assertTrue(all(row['exit_code'] == 1 for row in first['records']))
        self.assertIn(b'qmatch requires independently checked coherent lowering',
                      members['first/bit-control/stdout.txt'])
        self.assertIn(b'nominal selectors await typed source/native binding',
                      members['first/tri-reordered/stdout.txt'])
        self.assertIn(b'static target has not been independently checked',
                      members['observations/qmatch-selected-second/stdout.txt'])
        repaired = json.loads(members['observations/qmatch-selected-fifth/report.json.txt'])
        self.assertEqual(repaired['exit_code'], 0)
        self.assertEqual(repaired['before'], repaired['after'])
        self.assertEqual(json.loads((ROOT / COMPILER_VALIDATION).read_text())['issues'],
                         {'64': 'OPEN', '195': 'OPEN'})

    def test_generic_calls_retain_original_refusals_and_separate_repairs(self):
        members = bounded_history(ROOT / RUNTIME_GENERIC_ARCHIVE, ROOT / RUNTIME_GENERIC_INDEX)
        self.assertEqual(len(members), 94)
        first = json.loads(members['first/observations.json.txt'])
        self.assertEqual(len(first['records']), 6)
        self.assertEqual(next(row['exit_code'] for row in first['records']
                              if row['name'] == 'basis-nominal'), 1)
        self.assertIn(b'Q<A>', members['first/basis-nominal/main.qli.txt'])
        self.assertIn(b'nominal source types require typed native transport',
                      members['observations/generic-calls-fourth/stdout.txt'])
        self.assertIn(b'use type(T)', members['observations/generic-calls-third/stdout.txt'])
        for label in ['generic-calls-fifth', 'generic-calls-seventh', 'generic-calls-msrv']:
            result = json.loads(members[f'observations/{label}/report.json.txt'])
            self.assertEqual(result['exit_code'], 0)
            self.assertEqual(result['before'], result['after'])
        current = json.loads((ROOT / RUNTIME_GENERIC_VALIDATION).read_text())
        self.assertEqual(current['issues'], {'64': 'OPEN', '195': 'OPEN'})

    def test_static_execution_keeps_the_first_source_refusal_and_separate_success(self):
        members = bounded_history(ROOT / RUNTIME_STATIC_V2_ARCHIVE, ROOT / RUNTIME_STATIC_V2_INDEX)
        self.assertEqual(len(members), 664)
        first = json.loads(members['runtime-static-v2-first/observation.json.txt'])
        self.assertNotEqual(first['exit_code'], 0)
        self.assertIn(b'original static-binder transport', members['runtime-static-v2-first/stdout.txt'])
        later = json.loads(members['runtime-static-v2-current-cli/observations.json.txt'])
        self.assertEqual(later['records'][0]['source_sha256'], first['source_sha256'])
        self.assertTrue(all(row['exit_code'] == 0 for row in later['records']))
        failed = json.loads(members['observations/static-v2-generic-source-first/report.json.txt'])
        self.assertNotEqual(failed['exit_code'], 0)
        for label in ['static-v2-source-final', 'static-v2-msrv-source']:
            self.assertEqual(members[f'observations/{label}/stdout.txt'].count(
                b'10 passed; 0 failed; 0 ignored'), 2)
        current = json.loads((ROOT / RUNTIME_STATIC_V2_VALIDATION).read_text())
        self.assertEqual(current['native_execution'], 'SELECTED BASIS/NAT ROOTS ENABLED')
        self.assertEqual(current['issues'], {'64': 'OPEN', '195': 'OPEN'})
        self.assertEqual(current['goal_percent'], 58.27)

    def test_static_signature_first_failures_and_bounded_comparisons_are_retained(self):
        members = bounded_history(ROOT / RUNTIME_STATIC_ARCHIVE, ROOT / RUNTIME_STATIC_INDEX)
        self.assertEqual(len(members), 1289)
        self.assertIn(b'Lean exited with code 137', members[
            'observations/static-natural-kernel-reductions/stdout.txt'])
        for name in ['StaticNatMixedProbe.lean', 'StaticNatOverflowProbe.lean']:
            self.assertTrue(members[f'probes/{name}.txt'])
        final = members['observations/static-signature-native-comparisons/stdout.txt']
        for count in [24, 18, 10]:
            self.assertIn(f'passed {count} original'.encode(), final)
        for label, count in [('runtime', 11), ('carrier', 12), ('ordinary', 13)]:
            self.assertIn(f'{count} passed; 0 failed; 0 ignored'.encode(), members[
                f'observations/static-signature-native-{label}-regressions/stdout.txt'])
        current = json.loads((ROOT / RUNTIME_STATIC_VALIDATION).read_text())
        self.assertEqual(current['native_execution'], 'GENERIC ROUTE NOT ENABLED')
        self.assertEqual(current['issues'], {'64': 'OPEN', '195': 'OPEN'})
        self.assertEqual(sum(current['executable_comparisons'].values()), 52)
        self.assertIn('Current evidence is stale', current['proof_records'])

    def test_runtime_source_first_failures_and_repaired_scope_are_retained(self):
        members = bounded_history(ROOT / RUNTIME_SOURCE_ARCHIVE, ROOT / RUNTIME_SOURCE_INDEX)
        first = members['observations/source-native-first/stderr.txt']
        self.assertIn(b'E0560', first)
        self.assertIn(b'E0502', first)
        failed = json.loads(members['observations/source-regression-second/report.json.txt'])
        self.assertEqual(failed['exit_code'], 101)
        for label, passed in [('source-final-eight', 8), ('source-msrv-eight', 8),
                              ('source-native-eleven', 11), ('source-msrv-native-eleven', 11),
                              ('source-types-final', 10), ('source-msrv-types-final', 10)]:
            report = json.loads(members[f'observations/{label}/report.json.txt'])
            self.assertEqual(report['exit_code'], 0)
            self.assertTrue(report['stable_source'])
            self.assertIn(f'{passed} passed; 0 failed; 0 ignored'.encode(),
                          members[f'observations/{label}/stdout.txt'])
        current = json.loads((ROOT / RUNTIME_SOURCE_VALIDATION).read_text())
        self.assertEqual(current['issues'], {'64': 'OPEN', '195': 'OPEN'})
        self.assertEqual(current['goal_percent'], 58.27)
        self.assertIn('FAIL stale current source identity', current['constitutional_check'])
        self.assertIn('generic/static original-binder transport', current['remaining'])

    def test_runtime_transport_preserves_failures_and_fresh_native_scope(self):
        members = bounded_history(ROOT / RUNTIME_TRANSPORT_ARCHIVE, ROOT / RUNTIME_TRANSPORT_INDEX)
        self.assertEqual(len(members), 572)
        for label in ['rust-check-first', 'rust-stable-clippy-first']:
            self.assertIn(b'compiled by an incompatible version of rustc',
                          members[f'observations/{label}/stderr.txt'])
        self.assertIn(b'E0631', members['observations/rust-check-pinned-first/stderr.txt'])
        self.assertIn(b'Audit.lean', members['observations/native-audit-first/stderr.txt'])
        self.assertIn(b'21744 kernel/transport declarations',
                      members['observations/native-audit-second/stdout.txt'])
        for label in ['rust-native-first', 'rust-msrv-native-first']:
            self.assertIn(b'10 passed; 0 failed; 0 ignored', members[f'observations/{label}/stdout.txt'])
        for label in ['rust-ordinary-regression-first', 'rust-msrv-ordinary-first']:
            self.assertIn(b'13 passed; 0 failed; 0 ignored', members[f'observations/{label}/stdout.txt'])
        current = json.loads((ROOT / RUNTIME_TRANSPORT_VALIDATION).read_text())
        self.assertEqual(current['issues'], {'64': 'OPEN', '195': 'OPEN'})
        self.assertIn('normal .qli project/selected lowering', current['remaining'])
        self.assertEqual(current['goal_percent'], 58.27)

    def test_mixed_root_first_failures_and_separate_audit_repair_are_retained(self):
        members = bounded_history(ROOT / RUNTIME_ROOT_ARCHIVE, ROOT / RUNTIME_ROOT_INDEX)
        self.assertEqual(len(members), 130)
        rows = json.loads(members['cli/observations.json.txt'])
        self.assertEqual(len(rows), 8)
        self.assertEqual(sum(row['exit_code'] == 0 for row in rows), 0)
        for row in rows:
            result = json.loads(members['cli/' + row['stdout'] + '.txt'])
            self.assertEqual(result['diagnostics'][0]['code'],
                             'effect' if row['case'] == 'hidden-discard-refusal' else 'unsupported')
        first = members['compile/runtime-code-space-production-first/0.stdout.txt']
        self.assertIn(b'Unknown constant `QleisliKernel.Semantics.Exact.Matrix.compose`', first)
        failure = members['compile/runtime-root-controls-fifth/4.stdout.txt']
        self.assertIn(b'Maps.logicals._unsafe_rec: partial project declaration', failure)
        audit = json.loads(members['compile/runtime-root-audit-repair-first/report.json.txt'])
        self.assertEqual(audit['exit_code'], 0)
        self.assertTrue(audit['stable_inputs'])
        status = json.loads((ROOT / RUNTIME_ROOT_VALIDATION).read_text())
        self.assertEqual(status['native_execution'], 'NOT ENABLED')
        self.assertEqual(status['current_bounded_integration_controls'], 21)
        self.assertEqual(status['issues'], {'64': 'OPEN', '195': 'OPEN'})

    def test_original_runtime_signatures_remain_metadata_and_inert_history(self):
        members = bounded_history(ROOT / RUNTIME_SIGNATURE_ARCHIVE, ROOT / RUNTIME_SIGNATURE_INDEX)
        self.assertTrue((ROOT / RUNTIME_SIGNATURE_README).is_file())
        self.assertEqual(len(members), 93)
        rows = json.loads(members['cli/observations.json.txt'])
        self.assertEqual(len(rows), 14)
        self.assertEqual(sum(row['exit_code'] == 0 for row in rows), 2)
        for row in rows:
            result = json.loads(members['cli/' + row['stdout'] + '.txt'])
            if row['case'] == 'ordinary-inspection-refusal':
                self.assertIn('live Q<T>', result['diagnostics'][0]['message'])
            if row['case'] == 'hidden-observation-refusal':
                self.assertEqual(result['diagnostics'][0]['code'], 'effect')
                self.assertIn('Observe', result['diagnostics'][0]['message'])
        first = members['compile/runtime-signature-production-first/0.stdout.txt']
        self.assertIn(b"unexpected token 'Type'", first)
        second = members['compile/runtime-signature-production-second/1.stdout.txt']
        self.assertIn(b'[].isEmpty', second)
        audit = json.loads(members['compile/runtime-signature-audit-first/report.json.txt'])
        self.assertEqual(audit['exit_code'], 0)
        self.assertTrue(audit['stable_inputs'])
        status = json.loads((ROOT / RUNTIME_SIGNATURE_VALIDATION).read_text())
        self.assertEqual(status['native_execution'], 'NOT ENABLED')
        self.assertEqual(status['issues'], {'64': 'OPEN', '195': 'OPEN'})

    @classmethod
    def setUpClass(cls):
        cls.index = json.loads((ROOT / INDEX).read_text())
        cls.archive = (ROOT / ARCHIVE).read_bytes()
        if len(cls.archive) > 1024 * 1024:
            raise ValueError("historical archive exceeds expected bounded size")
        with lzma.open(io.BytesIO(cls.archive)) as stream:
            data = stream.read(32 * 1024 * 1024 + 1)
        if len(data) > 32 * 1024 * 1024:
            raise ValueError("historical container exceeds expected bounded size")
        cls.members = {}
        with tarfile.open(fileobj=io.BytesIO(data)) as archive:
            for member in archive:
                name = PurePosixPath(member.name)
                if (not member.isfile() or name.is_absolute() or ".." in name.parts
                        or member.name in cls.members or member.name not in cls.index["records"]):
                    raise ValueError("nonregular, duplicate or unlisted history member")
                cls.members[member.name] = archive.extractfile(member).read()

    def test_every_original_byte_is_retained(self):
        self.assertEqual(set(self.members), set(self.index["records"]))
        self.assertEqual(len(self.members), 785)
        self.assertEqual(hashlib.sha256(self.archive).hexdigest(), self.index["archive"]["sha256"])
        self.assertEqual(len(self.archive), self.index["archive"]["bytes"])
        for name, content in self.members.items():
            with self.subTest(member=name):
                self.assertEqual(len(content), self.index["records"][name]["bytes"])
                self.assertEqual(hashlib.sha256(content).hexdigest(), self.index["records"][name]["sha256"])
        self.assertTrue((ROOT / README).is_file())

    def test_first_failure_and_separate_repair_keep_their_scopes(self):
        def report(label):
            return json.loads(self.members[f"observations/{label}/report.json.txt"])

        self.assertEqual(report("source-sector-runtime-first")["exit_code"], 1)
        first = (self.members["observations/source-sector-runtime-first/stdout.txt"]
                 + self.members["observations/source-sector-runtime-first/stderr.txt"])
        self.assertIn(b"UNRESOLVED: source-function substitution survived", first)
        self.assertEqual(report("source-sector-runtime-fourth")["exit_code"], 0)
        self.assertIn(b"22 bounded source/evidence observations passed",
                      self.members["observations/source-sector-runtime-fourth/stdout.txt"])
        current = json.loads((ROOT / VALIDATION).read_text())
        self.assertEqual(current["goal"]["issue195"], "OPEN")
        self.assertIn("NOT RUN", current["uncompleted_checks"]["proof_records"])

    def test_first_hosted_failure_stays_distinct_from_component_repair(self):
        index = json.loads((ROOT / CI_TYPECHECK_INDEX).read_text())
        packed = (ROOT / CI_TYPECHECK).read_bytes()
        self.assertEqual(len(packed), index["bytes"])
        self.assertEqual(hashlib.sha256(packed).hexdigest(), index["sha256"])
        self.assertLessEqual(len(packed), 1024 * 1024)
        with lzma.open(io.BytesIO(packed)) as stream:
            expanded = stream.read(32 * 1024 * 1024 + 1)
        self.assertLessEqual(len(expanded), 32 * 1024 * 1024)
        members = {}
        with tarfile.open(fileobj=io.BytesIO(expanded)) as archive:
            for member in archive:
                name = PurePosixPath(member.name)
                self.assertTrue(member.isfile())
                self.assertFalse(name.is_absolute())
                self.assertNotIn("..", name.parts)
                self.assertNotIn(member.name, members)
                self.assertIn(member.name, index["records"])
                content = archive.extractfile(member).read()
                self.assertEqual(len(content), index["records"][member.name]["bytes"])
                self.assertEqual(hashlib.sha256(content).hexdigest(), index["records"][member.name]["sha256"])
                members[member.name] = content
        self.assertEqual(len(members), 9)
        self.assertEqual(set(members), set(index["records"]))
        self.assertEqual(json.loads(members["observed/kernel-build.command.json.txt"])["exit_code"], 1)
        self.assertIn("Unknown identifier `α`", members["observed/kernel-build.stdout.txt"].decode())
        self.assertIn(b"autoImplicit", members["observed/kernel-build.stdout.txt"])
        repaired = json.loads(members["repair/changed-sources-report.json.txt"])
        self.assertEqual(repaired["exit_code"], 0)
        self.assertTrue(repaired["stable_inputs"])
        self.assertEqual(len(repaired["commands"]), 98)
        self.assertTrue(all(row["exit_code"] == 0 for row in repaired["commands"]))
        current = json.loads((ROOT / CI_TYPECHECK_VALIDATION).read_text())
        self.assertFalse(current["compiled_native_validated"])
        self.assertEqual(current["issue195"], "OPEN")

    def test_operand_counterexamples_and_generated_partial_repair(self):
        index = json.loads((ROOT / OPERAND_INDEX).read_text())
        compressed = (ROOT / OPERANDS).read_bytes()
        self.assertLessEqual(len(compressed), 1024 * 1024)
        self.assertEqual(hashlib.sha256(compressed).hexdigest(), index["sha256"])
        with lzma.open(io.BytesIO(compressed)) as stream:
            contents = stream.read(32 * 1024 * 1024 + 1)
        self.assertLessEqual(len(contents), 32 * 1024 * 1024)
        members = {}
        with tarfile.open(fileobj=io.BytesIO(contents)) as archive:
            for member in archive:
                name = PurePosixPath(member.name)
                self.assertTrue(member.isfile())
                self.assertFalse(name.is_absolute())
                self.assertNotIn("..", name.parts)
                self.assertNotIn(member.name, members)
                self.assertIn(member.name, index["records"])
                content = archive.extractfile(member).read()
                self.assertEqual(len(content), index["records"][member.name]["bytes"])
                self.assertEqual(hashlib.sha256(content).hexdigest(), index["records"][member.name]["sha256"])
                members[member.name] = content
        self.assertEqual(set(members), set(index["records"]))
        self.assertEqual(len(members), 195)
        for label in ("source-operands-first", "source-operands-effect-first",
                      "source-operands-equal-width-first", "source-operands-audit"):
            self.assertEqual(json.loads(members[f"observations/{label}/report.json.txt"])["exit_code"], 1)
        self.assertIn(b"partial project declaration", members["observations/source-operands-audit/stdout.txt"])
        for label in ("source-operands-final", "source-evidence-final", "source-operands-effect-final",
                      "source-operands-equal-width-final", "source-operands-audit-second"):
            self.assertEqual(json.loads(members[f"observations/{label}/report.json.txt"])["exit_code"], 0)
        current = json.loads((ROOT / OPERAND_VALIDATION).read_text())
        self.assertFalse(current["native_activated"])

    def test_original_transport_mismatch_and_repairs_are_inert_and_retained(self):
        index = json.loads((ROOT / TRANSPORT_INDEX).read_text())
        compressed = (ROOT / TRANSPORT).read_bytes()
        self.assertLessEqual(len(compressed), 1024 * 1024)
        self.assertEqual(hashlib.sha256(compressed).hexdigest(), index["sha256"])
        with lzma.open(io.BytesIO(compressed)) as stream:
            contents = stream.read(32 * 1024 * 1024 + 1)
        self.assertLessEqual(len(contents), 32 * 1024 * 1024)
        members = {}
        with tarfile.open(fileobj=io.BytesIO(contents)) as archive:
            for member in archive:
                name = PurePosixPath(member.name)
                self.assertTrue(member.isfile())
                self.assertFalse(name.is_absolute())
                self.assertNotIn("..", name.parts)
                self.assertNotIn(member.name, members)
                self.assertIn(member.name, index["records"])
                content = archive.extractfile(member).read()
                self.assertEqual(len(content), index["records"][member.name]["bytes"])
                self.assertEqual(hashlib.sha256(content).hexdigest(), index["records"][member.name]["sha256"])
                members[member.name] = content
        self.assertEqual(set(members), set(index["records"]))
        self.assertEqual(len(members), 112)
        for label, code in [("qmatch-shape-runtime-first", 1), ("qmatch-shape-runtime-second", 0),
                            ("qmatch-protocol-runtime-first", 1), ("qmatch-protocol-runtime-second", 0),
                            ("qmatch-complete-order-first", 1), ("qmatch-complete-order-second", 0),
                            ("qmatch-transport-tests-first", 1), ("qmatch-transport-tests-second", 0),
                            ("qmatch-execution-runtime-observed-first", 1),
                            ("qmatch-execution-runtime-observed-second", 0)]:
            self.assertEqual(json.loads(members[f"observations/{label}/report.json.txt"])["exit_code"], code)
        self.assertIn(b"port-bits-outside-u8: expected false, observed true",
                      members["observations/qmatch-shape-runtime-first/stdout.txt"])
        self.assertIn(b"2 exact phase controls and 24 QLV3",
                      members["observations/qmatch-execution-runtime-observed-second/stdout.txt"])
        notes = json.loads(members["observations/observer-notes.json.txt"])
        self.assertIn("neither a semantic", notes["first_native_observation"])
        current = json.loads((ROOT / TRANSPORT_VALIDATION).read_text())
        self.assertFalse(current["native_activated"])
        self.assertEqual(current["goal"]["percent"], 58.27)

    def test_first_retained_graph_compile_failure_and_native_test_limits_survive(self):
        index = json.loads((ROOT / NATIVE_BINDING_INDEX).read_text())
        compressed = (ROOT / NATIVE_BINDING).read_bytes()
        self.assertLessEqual(len(compressed), 1024 * 1024)
        self.assertEqual(hashlib.sha256(compressed).hexdigest(), index["sha256"])
        with lzma.open(io.BytesIO(compressed)) as stream:
            contents = stream.read(32 * 1024 * 1024 + 1)
        self.assertLessEqual(len(contents), 32 * 1024 * 1024)
        members = {}
        with tarfile.open(fileobj=io.BytesIO(contents)) as archive:
            for member in archive:
                name = PurePosixPath(member.name)
                self.assertTrue(member.isfile())
                self.assertFalse(name.is_absolute())
                self.assertNotIn("..", name.parts)
                self.assertNotIn(member.name, members)
                self.assertIn(member.name, index["records"])
                content = archive.extractfile(member).read()
                self.assertEqual(len(content), index["records"][member.name]["bytes"])
                self.assertEqual(hashlib.sha256(content).hexdigest(), index["records"][member.name]["sha256"])
                members[member.name] = content
        self.assertEqual(len(members), 167)
        self.assertEqual(set(members), set(index["records"]))
        first = json.loads(members["observations/qmatch-rust-binding-first/report.json.txt"])
        self.assertEqual(first["exit_code"], 101)
        self.assertIn(b"3 previous errors", members["observations/qmatch-rust-binding-first/0.stderr.txt"])
        for label in ["qmatch-rust-binding-second", "qmatch-rust-binding-msrv"]:
            self.assertEqual(json.loads(members[f"observations/{label}/report.json.txt"])["exit_code"], 0)
            self.assertIn(b"3 passed; 0 failed; 2 ignored", members[f"observations/{label}/0.stdout.txt"])
        current = json.loads((ROOT / NATIVE_BINDING_VALIDATION).read_text())
        self.assertFalse(current["compiled_native_validated"])
        self.assertEqual(current["goal"]["issue195"], "OPEN")


    def test_complete_body_failures_and_remaining_native_obligations_survive(self):
        directory = ROOT / BODY_ROOT
        index = json.loads((directory / 'body-index.json').read_text())
        packed = (directory / 'body-first.tar.xz').read_bytes()
        self.assertLessEqual(len(packed), 1024 * 1024)
        self.assertEqual(len(packed), index['bytes'])
        self.assertEqual(hashlib.sha256(packed).hexdigest(), index['sha256'])
        with lzma.open(io.BytesIO(packed)) as stream:
            expanded = stream.read(32 * 1024 * 1024 + 1)
        self.assertLessEqual(len(expanded), 32 * 1024 * 1024)
        members = {}
        with tarfile.open(fileobj=io.BytesIO(expanded)) as archive:
            for entry in archive:
                self.assertTrue(entry.isfile())
                self.assertFalse(PurePosixPath(entry.name).is_absolute())
                self.assertNotIn('..', PurePosixPath(entry.name).parts)
                self.assertNotIn(entry.name, members)
                self.assertIn(entry.name, index['records'])
                content = archive.extractfile(entry).read()
                self.assertEqual(len(content), index['records'][entry.name]['bytes'])
                self.assertEqual(hashlib.sha256(content).hexdigest(), index['records'][entry.name]['sha256'])
                members[entry.name] = content
        self.assertEqual(set(members), set(index['records']))
        self.assertEqual(len(members), 151)
        failed = json.loads(members['observations/qmatch-complete-body-runtime-first/report.json.txt'])
        passed = json.loads(members['observations/qmatch-complete-body-runtime-second/report.json.txt'])
        self.assertEqual(failed['exit_code'], 1)
        self.assertIn(b'Gate.Error.decodedView', members['observations/qmatch-complete-body-runtime-first/stderr.txt'])
        self.assertEqual(passed['exit_code'], 0)
        self.assertIn(b'4 exact controls and 8 QLV3', members['observations/qmatch-complete-body-runtime-second/stdout.txt'])
        current = json.loads((directory / 'body-validation.json').read_text())
        self.assertFalse(current['compiled_native_validated'])
        self.assertEqual(current['issue195'], 'OPEN')

    def test_raw_owner_counterexample_and_matching_permutation_remain_distinct(self):
        directory = ROOT / BODY_ROOT
        members = bounded_history(ROOT / OWNER_FLOW_ARCHIVE, ROOT / OWNER_FLOW_INDEX)
        self.assertEqual(len(members), 118)
        first = members['observations/qmatch-raw-return-owner-swap-first/stderr.txt']
        second = members['observations/qmatch-raw-return-owner-swap-second/stderr.txt']
        self.assertIn(b'Gate.Error.decodedView', first)
        self.assertIn(b'qmatch original bytes/acceptance mismatch', second)
        current = json.loads(members['observations/qmatch-raw-owner-flow-permutation-context-first/report.json.txt'])
        self.assertEqual(current['exit_code'], 0)
        self.assertTrue(current['stable_inputs'])
        self.assertIn(b'5 exact controls and 9 QLV3',
                      members['observations/qmatch-raw-owner-flow-permutation-context-first/stdout.txt'])
        validation = json.loads((directory / 'owner-flow-validation.json').read_text())
        self.assertFalse(validation['compiled_native_validated'])
        self.assertEqual(validation['issue195'], 'OPEN')

    def test_nominal_first_proposals_and_precise_refusals_remain_separate(self):
        index = json.loads((ROOT / NOMINAL_INDEX).read_text())
        packed = (ROOT / NOMINAL).read_bytes()
        self.assertLessEqual(len(packed), 1024 * 1024)
        self.assertEqual(len(packed), index["bytes"])
        self.assertEqual(hashlib.sha256(packed).hexdigest(), index["sha256"])
        with lzma.open(io.BytesIO(packed)) as stream:
            data = stream.read(32 * 1024 * 1024 + 1)
        self.assertLessEqual(len(data), 32 * 1024 * 1024)
        members = {}
        with tarfile.open(fileobj=io.BytesIO(data)) as archive:
            for member in archive:
                self.assertTrue(member.isfile())
                self.assertFalse(PurePosixPath(member.name).is_absolute())
                self.assertNotIn("..", PurePosixPath(member.name).parts)
                self.assertNotIn(member.name, members)
                self.assertIn(member.name, index["records"])
                content = archive.extractfile(member).read()
                self.assertEqual(len(content), index["records"][member.name]["bytes"])
                self.assertEqual(hashlib.sha256(content).hexdigest(), index["records"][member.name]["sha256"])
                members[member.name] = content
        self.assertEqual(set(members), set(index["records"]))
        self.assertEqual(len(members), 72)
        for label in ["qmatch-nominal-context-first", "qmatch-nominal-context-third"]:
            self.assertEqual(json.loads(members[f"observations/{label}/report.json.txt"])["exit_code"], 1)
        self.assertIn(b"Finite.Error.invalid", members["observations/qmatch-nominal-context-first/stderr.txt"])
        self.assertIn(b"Gate.Error.decodedView", members["observations/qmatch-nominal-context-third/stderr.txt"])
        self.assertEqual(json.loads(members["observations/qmatch-nominal-maintained-first/report.json.txt"])["exit_code"], 0)
        diagnostics = members["observations/qmatch-nominal-context-diagnostic/stdout.txt"]
        self.assertEqual(diagnostics.count(b"Finite.Error.equation"), 10)
        self.assertEqual(diagnostics.count(b"Finite.Error.request"), 12)
        self.assertEqual(diagnostics.count(b"Gate.Error.decodedView"), 2)
        current = json.loads((ROOT / NOMINAL_VALIDATION).read_text())
        self.assertFalse(current["compiled_native_validated"])
        self.assertEqual(current["issue195"], "OPEN")


if __name__ == "__main__":
    unittest.main()
