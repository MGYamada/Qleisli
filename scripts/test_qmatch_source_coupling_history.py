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
from unittest.mock import patch

import inert_qmatch_history as shared_history
from test_inert_qmatch_history import BoundedPhysicalReader, SnapshotStructure


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
SHADOW_ARCHIVE = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/lexical-shadow-first.tar.xz"
SHADOW_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/lexical-shadow-index.json.xz"
FRAME_CASES = "tests/fixtures/qmatch_v030/frame-execution-cases.json"



SHARED = None
CONTEXT_ARCHIVE = BODY_ROOT + '/context-prototype/context-first.tar.xz'
CONTEXT_INDEX = BODY_ROOT + '/context-prototype/context-index.json.xz'


def setUpModule():
    global SHARED
    SHARED = shared_history.Snapshot(ROOT)


def tearDownModule():
    SHARED.assert_inputs_unchanged()


def retained_history_path(path):
    logical = path.relative_to(ROOT).as_posix()
    if not logical.startswith(shared_history.PREFIX):
        return None
    name = path.name
    if (name.endswith('.tar.xz') or name == 'index.json'
            or name.endswith(('-index.json', '-index.json.xz'))
            or logical.startswith(shared_history.PREFIX + 'context-prototype/')):
        return logical
    return None


def history_bytes(path):
    logical = retained_history_path(path)
    if logical is not None:
        return SHARED.read(logical)
    return path.read_bytes()


def history_text(path):
    return history_bytes(path).decode('utf-8')


def history_json(path):
    """Read bounded inert metadata, including explicitly compressed JSON."""
    data = history_bytes(path)
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
    packed = history_bytes(archive_path)
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
    def test_phase_static_first_sources_and_real_diagnostics(self):
        path = ROOT / 'tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/phase-static-first.json.xz'
        self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(),
                         '54b29cc1953b6871fc510c431371f310f2f34a4e4e1e195bdf4f93b53f2c433c')
        record = history_json(path)
        self.assertEqual(record['maximum_quantum_bits'], 2)
        self.assertEqual(len(record['sources']), 8)
        for row in record['sources'].values():
            data = row['text'].encode('utf-8')
            self.assertEqual(len(data), row['bytes'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['sha256'])
        windows = record['windows']
        self.assertEqual(sum(len(w['observations']) for w in windows.values()), 16)
        for window in windows.values():
            self.assertTrue(window['inputs_stable'])
            for name, digest in window['original_sources'].items():
                self.assertEqual(record['sources'][name]['sha256'], digest)
            for row in window['observations']:
                self.assertTrue(row['child_reaped'])
                self.assertIsNone(row['host_stop'])
        first = {r['name']: r for r in windows['checks-first']['observations']}
        after = {r['name']: r for r in windows['checks-after-native']['observations']}
        self.assertEqual({r['exit_code'] for r in first.values()}, {1})
        for name, row in after.items():
            if name.startswith('unused-overflow'):
                self.assertEqual(row['exit_code'], 1)
                self.assertEqual(row['stdout'], first[name]['stdout'])
            else:
                self.assertEqual(row['exit_code'], 0)
                if name.endswith('-selected'):
                    result = json.loads(row['stdout'])['result']
                    self.assertFalse(result['source_preservation_verified'])
                    self.assertFalse(result['verification']['source_meaning_verified'])
        for name in ('checks-alias-work-first', 'checks-alias-work-cached'):
            self.assertEqual([r['exit_code'] for r in windows[name]['observations']], [1, 1])
        self.assertIn('external-only', record['scope'])
        self.assertIn('rejection cause remains undiagnosed', record['scope'])

    def test_module_header_first_diagnostic_is_retained(self):
        path = ROOT / 'tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/module-header-first.json'
        self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(),
                         '8cb9bc5a1857f691faf8842fd2b116a3e548b661ac5dbf6c8290d89841d47c1a')
        observed = json.loads(path.read_bytes())
        self.assertEqual(observed['first_source'], '#![no_implicit_prelude]\n' + observed['control_source'])
        first = observed['observations']['header-diagnostic-first']
        self.assertEqual(first['exit_code'], 0)
        self.assertIn('Except.error (QleisliKernel.Finite.Error.request)', first['stdout'])
        self.assertIn('(Except.ok ["pub", "unitary", "fn", "sign"', first['stdout'])
        for name in ('module-header-first', 'helper-call-first'):
            self.assertNotEqual(observed['observations'][name]['exit_code'], 0)
        for name in ('module-header-repair', 'header-conformance', 'helper-call-repair'):
            self.assertEqual(observed['observations'][name]['exit_code'], 0)
        for row in observed['observations'].values():
            self.assertTrue(row['stable_source'])
            self.assertTrue(row['child_reaped'])
            self.assertIsNone(row['host_stop'])

    def test_shared_history_complete_pinned_reconstruction(self):
        self.assertEqual(hashlib.sha256((ROOT / shared_history.MANIFEST).read_bytes()).hexdigest(),
                         'c1ad2909cc92e362563895f5f1a7ffd7d28bdb89d898685d4c6cefa7d26db35d')
        self.assertEqual(SHARED.audit_originals(), (108, 20))

    def test_focused_production_first_sources_and_complete_diagnostics(self):
        prefix = BODY_ROOT + '/production-context-focused/'
        raw_index = SHARED.read(prefix + 'index.json')
        self.assertEqual(hashlib.sha256(raw_index).hexdigest(),
                         '026808eaccd5719ebfb53516f5c061edb8eb0690371e40eb335b1c80b2c7af3e')
        index = json.loads(raw_index)
        self.assertEqual(len(index['records']), 44)
        for name, row in index['records'].items():
            data = SHARED.read(prefix + name)
            self.assertEqual(len(data), row['bytes'], name)
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['sha256'], name)
        windows = index['windows']
        self.assertEqual(len(windows), 14)
        self.assertEqual(sum(row['exit_code'] == 0 for row in windows), 5)
        for window in windows:
            for key in ('complete_stdout', 'complete_stderr'):
                self.assertIn(window[key], index['records'])
            for key in ('external_only_plan', 'external_only_report'):
                self.assertNotIn(window[key]['path'], index['records'])
        self.assertEqual(len(index['exact_first_source_bindings']), 5)
        for row in index['exact_first_source_bindings']:
            self.assertEqual(index['records'][row['locally_retained_original']]['sha256'],
                             row['sha256'])
        self.assertEqual(len(index['external_only_large_test_sources']), 8)
        for row in index['external_only_large_test_sources']:
            self.assertNotIn(row['path'], index['records'])
        repairs = index['current_repair_references']
        self.assertEqual(repairs['commit'], '53e0d4b131e014a350ec19428efe682e8de727ee')
        self.assertEqual(len(repairs['records']), 7)
        self.assertIn('not substitutes for earlier failed versions', repairs['scope'])
        self.assertIn('not a self-contained full-window', index['scope'])

    def test_missing_retained_path_has_no_disk_fallback(self):
        path = ROOT / BODY_ROOT / 'missing-index.json'
        with patch.object(Path, 'read_bytes', side_effect=AssertionError('disk fallback')):
            with self.assertRaisesRegex(ValueError, 'unregistered logical history'):
                history_bytes(path)

    def test_complete_context_original_paths_and_external_bindings(self):
        self.assertEqual(hashlib.sha256(history_bytes(ROOT / CONTEXT_INDEX)).hexdigest(),
                         'a92a651966c3f19e60adfc5d0d1aaddd4d41f825611ed19dc7980045c825cb6e')
        index = history_json(ROOT / CONTEXT_INDEX)
        self.assertEqual(index['sha256'],
                         '4d960e4b16b6b02636213e8dbd1f3769a922b249e7c6e45da2defdfd41e3e855')
        members = bounded_history(ROOT / CONTEXT_ARCHIVE, ROOT / CONTEXT_INDEX)
        self.assertEqual(len(members), 606)
        mapping = json.loads(members['original-records.json'])
        provenance = json.loads(members['provenance.json'])
        self.assertEqual(mapping['format'], 'qleisli.inert-original-records')
        self.assertEqual(mapping['version'], 1)
        self.assertEqual(len(mapping['records']), 941)
        self.assertEqual(len(mapping['external_objects']), 68)
        self.assertEqual(provenance['repository_commit'], shared_history.SOURCE_COMMIT)
        self.assertEqual(provenance['original_path_count'], 941)
        self.assertEqual(provenance['original_expanded_bytes'], 3987256)
        self.assertFalse(provenance['cap_changes'])
        expected_histories = {'sequence': (SEQUENCE_ARCHIVE, SEQUENCE_INDEX),
                              'shadow': (SHADOW_ARCHIVE, SHADOW_INDEX)}
        external = {}
        for pin in provenance['external_histories']:
            self.assertIn(pin['id'], expected_histories)
            self.assertNotIn(pin['id'], external)
            archive_path, index_path = expected_histories[pin['id']]
            self.assertEqual((pin['archive_path'], pin['index_path']), (archive_path, index_path))
            self.assertEqual(pin['commit'], shared_history.SOURCE_COMMIT)
            stored_index = history_bytes(ROOT / index_path)
            self.assertEqual((len(stored_index), hashlib.sha256(stored_index).hexdigest()),
                             (pin['index_bytes'], pin['index_sha256']))
            decoded_index = shared_history.decode(stored_index, shared_history.INDEX_MAX)
            self.assertEqual((len(decoded_index), hashlib.sha256(decoded_index).hexdigest()),
                             (pin['decoded_index_bytes'], pin['decoded_index_sha256']))
            packed = history_bytes(ROOT / archive_path)
            self.assertEqual((len(packed), hashlib.sha256(packed).hexdigest()),
                             (pin['archive_bytes'], pin['archive_sha256']))
            self.assertEqual(len(shared_history.decode(packed, shared_history.TAR_MAX)),
                             pin['expanded_tar_bytes'])
            values = bounded_history(ROOT / archive_path, ROOT / index_path)
            self.assertEqual(len(values), pin['members'])
            external[pin['id']] = (archive_path, values)
        self.assertEqual(set(external), set(expected_histories))
        originals, used_local, used_external = {}, set(), set()
        for name, row in mapping['records'].items():
            shared_history.canonical_path(name)
            self.assertEqual(set(row), {'bytes', 'sha256', 'original_mode', 'object'})
            digest = row['object']
            self.assertEqual(digest, row['sha256'])
            self.assertIs(type(row['original_mode']), int)
            self.assertTrue(0 <= row['original_mode'] <= 0o777)
            if digest in mapping['external_objects']:
                ref = mapping['external_objects'][digest]
                archive_path, values = external[ref['container']]
                data = values[ref['member']]
                self.assertEqual(ref['member_mode'], SHARED.member_mode(archive_path, ref['member']))
                self.assertEqual((ref['bytes'], ref['sha256']), (len(data), digest))
                used_external.add(digest)
            else:
                object_name = 'objects/' + digest
                data = members[object_name]
                used_local.add(object_name)
            self.assertEqual((len(data), hashlib.sha256(data).hexdigest()), (row['bytes'], digest))
            originals[name] = data
        self.assertEqual(used_local, set(members) - {'original-records.json', 'provenance.json'})
        self.assertEqual(used_external, set(mapping['external_objects']))
        reports = []
        for name, data in originals.items():
            if name.startswith('qmatch-context-interval-checks/') and name.endswith(('/plan.json', '/report.json')):
                observation = json.loads(data)
                for side in ('before', 'after'):
                    for digest in observation.get(side, {}).values():
                        body = originals['qmatch-context-interval-source-objects/' + digest]
                        self.assertEqual(hashlib.sha256(body).hexdigest(), digest)
                if name.endswith('/report.json'):
                    reports.append(observation)
        self.assertEqual(len(reports), 133)
        self.assertEqual(sum(row['exit_code'] == 0 for row in reports), 85)
        self.assertEqual(sum(row['exit_code'] != 0 for row in reports), 48)

    def test_original_lexical_shadow_counterexample_and_controls(self):
        members = bounded_history(ROOT / SHADOW_ARCHIVE, ROOT / SHADOW_INDEX)
        self.assertEqual(history_json(ROOT / SHADOW_INDEX)['sha256'],
                         '464d93d50de923cab8ea33c0c2c38dbbddcb855b1d15c146266aa81e30c30f58')
        self.assertEqual(len(members), 79)
        initial = json.loads(members['native-candidate-first/observations-first/report.json'])
        self.assertTrue(initial['stable'])
        self.assertEqual(initial['before'], initial['after'])
        results = {row['label']: row for row in initial['results']}
        rust = json.loads(members['native-rust-project-controls/report.json'])
        for row in rust['results']:
            label = row['label']
            self.assertEqual(results[label + '-native']['exit_code'], 0)
            self.assertEqual(row['exit_code'], int(label == 'consumed-local'))
            self.assertTrue(row['source_identical'])
            self.assertEqual(members['native-candidate-first/' + label + '/main.qli'],
                             members['native-rust-project-controls/' + label + '/main.qli'])
        rejected = next(row for row in rust['results'] if row['label'] == 'consumed-local')
        self.assertEqual(rejected['document']['diagnostics'][0]['message'],
                         'static operation requires a function name, not a local value')
        repaired = json.loads(members['production-repair-first/report.json'])
        self.assertTrue(repaired['stable'])
        self.assertEqual(repaired['exit_code'], 0)

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
        self.assertEqual(hashlib.sha256(history_bytes(ROOT / SEQUENCE_INDEX)).hexdigest(),
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
        validation = json.loads(history_text(ROOT / CONTEXT_V2_VALIDATION))
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
        validation = json.loads(history_text(ROOT / CONTEXT_VALIDATION))
        self.assertFalse(validation['limits_raised'])
        self.assertEqual(validation['issues_open'], [64, 195, 142])
        current = json.loads(history_text(ROOT / FRAME_CASES))['cases']
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
        validation = json.loads(history_text(ROOT / TARGET_VALIDATION))
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
        validation = json.loads(history_text(folder / 'nominal-compiler-validation.json'))
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
        self.assertEqual(json.loads(history_text(ROOT / COMPILER_VALIDATION))['issues'],
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
        current = json.loads(history_text(ROOT / RUNTIME_GENERIC_VALIDATION))
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
        current = json.loads(history_text(ROOT / RUNTIME_STATIC_V2_VALIDATION))
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
        current = json.loads(history_text(ROOT / RUNTIME_STATIC_VALIDATION))
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
        current = json.loads(history_text(ROOT / RUNTIME_SOURCE_VALIDATION))
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
        current = json.loads(history_text(ROOT / RUNTIME_TRANSPORT_VALIDATION))
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
        status = json.loads(history_text(ROOT / RUNTIME_ROOT_VALIDATION))
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
        status = json.loads(history_text(ROOT / RUNTIME_SIGNATURE_VALIDATION))
        self.assertEqual(status['native_execution'], 'NOT ENABLED')
        self.assertEqual(status['issues'], {'64': 'OPEN', '195': 'OPEN'})

    @classmethod
    def setUpClass(cls):
        cls.index = json.loads(history_text(ROOT / INDEX))
        cls.archive = history_bytes(ROOT / ARCHIVE)
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
        current = json.loads(history_text(ROOT / VALIDATION))
        self.assertEqual(current["goal"]["issue195"], "OPEN")
        self.assertIn("NOT RUN", current["uncompleted_checks"]["proof_records"])

    def test_first_hosted_failure_stays_distinct_from_component_repair(self):
        index = json.loads(history_text(ROOT / CI_TYPECHECK_INDEX))
        packed = history_bytes(ROOT / CI_TYPECHECK)
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
        current = json.loads(history_text(ROOT / CI_TYPECHECK_VALIDATION))
        self.assertFalse(current["compiled_native_validated"])
        self.assertEqual(current["issue195"], "OPEN")

    def test_operand_counterexamples_and_generated_partial_repair(self):
        index = json.loads(history_text(ROOT / OPERAND_INDEX))
        compressed = history_bytes(ROOT / OPERANDS)
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
        current = json.loads(history_text(ROOT / OPERAND_VALIDATION))
        self.assertFalse(current["native_activated"])

    def test_original_transport_mismatch_and_repairs_are_inert_and_retained(self):
        index = json.loads(history_text(ROOT / TRANSPORT_INDEX))
        compressed = history_bytes(ROOT / TRANSPORT)
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
        current = json.loads(history_text(ROOT / TRANSPORT_VALIDATION))
        self.assertFalse(current["native_activated"])
        self.assertEqual(current["goal"]["percent"], 58.27)

    def test_first_retained_graph_compile_failure_and_native_test_limits_survive(self):
        index = json.loads(history_text(ROOT / NATIVE_BINDING_INDEX))
        compressed = history_bytes(ROOT / NATIVE_BINDING)
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
        current = json.loads(history_text(ROOT / NATIVE_BINDING_VALIDATION))
        self.assertFalse(current["compiled_native_validated"])
        self.assertEqual(current["goal"]["issue195"], "OPEN")


    def test_complete_body_failures_and_remaining_native_obligations_survive(self):
        directory = ROOT / BODY_ROOT
        index = json.loads(history_text(directory / 'body-index.json'))
        packed = history_bytes(directory / 'body-first.tar.xz')
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
        current = json.loads(history_text(directory / 'body-validation.json'))
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
        validation = json.loads(history_text(directory / 'owner-flow-validation.json'))
        self.assertFalse(validation['compiled_native_validated'])
        self.assertEqual(validation['issue195'], 'OPEN')

    def test_nominal_first_proposals_and_precise_refusals_remain_separate(self):
        index = json.loads(history_text(ROOT / NOMINAL_INDEX))
        packed = history_bytes(ROOT / NOMINAL)
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
        current = json.loads(history_text(ROOT / NOMINAL_VALIDATION))
        self.assertFalse(current["compiled_native_validated"])
        self.assertEqual(current["issue195"], "OPEN")


class IndependentReferenceAuthoringHistory(unittest.TestCase):
    def test_first_sources_and_real_diagnostics(self):
        readme = ROOT / 'tests/fixtures/authoring_sessions/qmatch-reference-authoring-v030/README.md'
        self.assertIn(b'No first source was repaired.', readme.read_bytes())
        archive = ROOT / 'tests/fixtures/authoring_sessions/qmatch-reference-authoring-v030/first.tar.xz'
        index = ROOT / 'tests/fixtures/authoring_sessions/qmatch-reference-authoring-v030/first-index.json.xz'
        self.assertEqual(hashlib.sha256(archive.read_bytes()).hexdigest(),
                         'b4f24ec5d70b1ee27d28f8ee2941e18f7cba55a22e0d6a85bf6604e75d3ab297')
        self.assertEqual(hashlib.sha256(index.read_bytes()).hexdigest(),
                         '38e40184f782407153fe7ecc5e28d622e812d1fce972ba7bb234079baf19535c')
        members = bounded_history(archive, index)
        self.assertEqual(len(members), 47)
        observed = json.loads(members['checks-first/focused-observations.json'])
        self.assertTrue(observed['inputs_stable'])
        self.assertTrue(observed['all_observations_completed'])
        self.assertEqual(observed['participant_inputs_before'], observed['participant_inputs_after'])
        self.assertEqual(len(observed['participant_inputs_before']), 23)
        for name, digest in observed['participant_inputs_before'].items():
            self.assertEqual(hashlib.sha256(members[name]).hexdigest(), digest)
        self.assertEqual(len(observed['results']), 10)
        for row in observed['results']:
            case = row['name']
            for stream in ('stdout', 'stderr'):
                self.assertEqual(hashlib.sha256(members[f'checks-first/{case}/{stream}']).hexdigest(),
                                 row[stream + '_sha256'])
            reply = json.loads(members[f'checks-first/{case}/stdout'])
            self.assertTrue(row['child_reaped'])
            self.assertIsNone(row['host_stop'])
            self.assertIsNone(row['observer_error'])
            if case.endswith('-negative'):
                self.assertNotEqual(row['exit_code'], 0)
                self.assertEqual(reply['outcome'], 'error')
                expected = 'live Q<T> cannot be inspected' if 'classical-match' in case else 'duplicate qmatch ordinal 1'
                self.assertIn(expected, reply['diagnostics'][0]['message'])
            else:
                self.assertEqual(row['exit_code'], 0)
                self.assertEqual(reply['outcome'], 'ok')
                result = reply['result']
                self.assertTrue(result['runtime_result_checked'])
                self.assertFalse(result['source_preservation_verified'])
                self.assertFalse(result['verification']['source_steps_checked'])
                self.assertFalse(result['verification']['source_meaning_verified'])
                self.assertEqual(result['verification']['request_origin'], 'producer')
                self.assertEqual(result['execution_authority'], 'checked-produced-ir')
        checkpoint = json.loads(members['results-checkpoint.json'])
        self.assertEqual(checkpoint['first_authoring']['source_repairs'], 0)
        self.assertEqual(checkpoint['accounting_credit'], 0)
        self.assertTrue(all(not case['independent_native_operator_request_checked']
                            for case in checkpoint['operator_observation']['records']))


if __name__ == "__main__":
    unittest.main()
