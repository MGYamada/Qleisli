"""Passive history preservation; never execute or extract saved sources.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
# Scope notes: "tests/fixtures/authoring_sessions/finite-adts-v030/README.md".
# Original bytes: "tests/fixtures/authoring_sessions/finite-adts-v030/first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/index.json".
# Body history: "tests/fixtures/authoring_sessions/finite-adts-v030/body-index.json"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/body-first.tar.xz".
# Body checks: "tests/fixtures/authoring_sessions/finite-adts-v030/body-validation.json".
# Declaration history: "tests/fixtures/authoring_sessions/finite-adts-v030/declarations-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/declarations-index.json".
# Declaration checks: "tests/fixtures/authoring_sessions/finite-adts-v030/declarations-validation.json".
# Name-resolution history: "tests/fixtures/authoring_sessions/finite-adts-v030/resolution-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/resolution-index.json".
# Name checks: "tests/fixtures/authoring_sessions/finite-adts-v030/resolution-validation.json".
# Type history: "tests/fixtures/authoring_sessions/finite-adts-v030/elaboration-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/elaboration-index.json".
# Type checks: "tests/fixtures/authoring_sessions/finite-adts-v030/elaboration-validation.json".
# Dependency history: "tests/fixtures/authoring_sessions/finite-adts-v030/dependencies-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/dependencies-index.json".
# Dependency checks: "tests/fixtures/authoring_sessions/finite-adts-v030/dependencies-validation.json".
# Current checks: "tests/fixtures/authoring_sessions/finite-adts-v030/validation.json".
# Native history: "tests/fixtures/authoring_sessions/finite-adts-v030/native-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/native-index.json".
# Native checks: "tests/fixtures/authoring_sessions/finite-adts-v030/native-validation.json".
# Immutable extraction: "tests/fixtures/authoring_sessions/finite-adts-v030/native-v2-extract-stdout.json.gz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/native-v2-extract-recovery.json".
# Ordinary runtime history: "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-runtime-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-runtime-index.json".
# Original retention proposal: "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-runtime-retention.json".
# Ordinary match history: "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-match-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-match-index.json".
# Proposal record: "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-match-validation.json".
# Match-keyword repair history: "tests/fixtures/authoring_sessions/finite-adts-v030/match-keyword-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/match-keyword-index.json".
# Proposal record: "tests/fixtures/authoring_sessions/finite-adts-v030/match-keyword-validation.json".
# Ordinary value reference: "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-value-reference-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-value-reference-index.json".
# Proposal record: "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-value-reference-validation.json".
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import tarfile
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'tests/fixtures/authoring_sessions/finite-adts-v030'


def read_history(index_name, archive_name, index_hash, stored_size, archive_hash, expanded):
    index_bytes = (FIXTURES / index_name).read_bytes()
    if hashlib.sha256(index_bytes).hexdigest() != index_hash:
        raise AssertionError('first index changed')
    index = json.loads(index_bytes)
    stored = (FIXTURES / archive_name).read_bytes()
    if (len(stored), hashlib.sha256(stored).hexdigest()) != (stored_size, archive_hash):
        raise AssertionError('first archive changed')
    data = {}
    total = 0
    with tarfile.open(fileobj=io.BytesIO(stored), mode='r:xz') as archive:
        for member in archive:
            path = PurePosixPath(member.name)
            if (not member.isfile() or member.mode != 0o644 or path.is_absolute()
                    or '..' in path.parts or str(path) != member.name
                    or member.name in data or member.name not in index['records']):
                raise AssertionError('noncanonical historical record')
            row = index['records'][member.name]
            if member.size != row['bytes'] or member.size > 8_000_000 or row['original_mode'] != 0o644:
                raise AssertionError('historical record exceeds declared bounds')
            total += member.size
            if total > expanded:
                raise AssertionError('historical expansion exceeds bounds')
            value = archive.extractfile(member).read(member.size + 1)
            if (len(value), hashlib.sha256(value).hexdigest()) != (row['bytes'], row['sha256']):
                raise AssertionError('historical bytes changed')
            data[member.name] = value
    if set(data) != set(index['records']) or total != expanded:
        raise AssertionError('first history is incomplete')
    return data


NATIVE_EXTRACT_GZIP = 'native-v2-extract-stdout.json.gz'
NATIVE_EXTRACT_RECOVERY = 'native-v2-extract-recovery.json'
NATIVE_EXTRACT_RECOVERY_SHA256 = '1de948c6192e148ccc19020fe9dea5040713e8e7ebc32acae7c24bd39a703e08'


def historical_native_stdout(reference_raw, provenance_raw, packed):
    """Resolve one fixed archived reference from inert local bytes, without Git."""
    if (len(provenance_raw) > 4096
            or hashlib.sha256(provenance_raw).hexdigest() != NATIVE_EXTRACT_RECOVERY_SHA256):
        raise AssertionError('historical extraction recovery metadata changed')
    provenance = json.loads(provenance_raw)
    original = provenance['historical_reference']
    if ((len(reference_raw), hashlib.sha256(reference_raw).hexdigest())
            != (original['bytes'], original['sha256'])):
        raise AssertionError('historical extraction reference changed')
    reference = json.loads(reference_raw)
    retained, stdout = provenance['retained_gzip'], provenance['original_stdout']
    if (reference['canonical_gzip'] != provenance['recovery']['git_path']
            or reference['byte_identical_to_decompressed_canonical'] is not True
            or reference['gzip_sha256'] != retained['sha256']
            or (reference['observed_stdout_bytes'], reference['observed_stdout_sha256'])
            != (stdout['bytes'], stdout['sha256'])
            or retained['path'] != 'tests/fixtures/authoring_sessions/finite-adts-v030/' + NATIVE_EXTRACT_GZIP):
        raise AssertionError('historical extraction association changed')
    if ((len(packed), hashlib.sha256(packed).hexdigest())
            != (retained['bytes'], retained['sha256'])):
        raise AssertionError('historical extraction gzip changed')
    blob = hashlib.sha1(b'blob ' + str(len(packed)).encode('ascii') + b'\0' + packed).hexdigest()
    if blob != provenance['recovery']['git_blob']:
        raise AssertionError('historical extraction recovery blob changed')
    # Reading one byte beyond the fixed original length bounds decompression
    # and rejects extra gzip members; no archived source or command is run.
    with gzip.GzipFile(fileobj=io.BytesIO(packed)) as stream:
        actual = stream.read(stdout['bytes'] + 1)
    if ((len(actual), hashlib.sha256(actual).hexdigest())
            != (stdout['bytes'], stdout['sha256'])):
        raise AssertionError('historical extraction stdout changed')
    return actual


def read_historical_native_stdout(fixtures, reference_raw):
    contents = []
    for name, limit in [(NATIVE_EXTRACT_RECOVERY, 4096), (NATIVE_EXTRACT_GZIP, 251833)]:
        path = fixtures / name
        if path.is_symlink() or not path.is_file() or path.stat().st_size > limit:
            raise AssertionError('missing or oversized local historical extraction fixture')
        contents.append(path.read_bytes())
    return historical_native_stdout(reference_raw, *contents)


class FirstFiniteADTs(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('index.json', 'first.tar.xz',
            '1c2f1e7dd7364157ecdf2f7b49068c11b872868b85104066353d64d1aa34fefc',
            862696, 'f3857707618584c552821edc5b207bf461a94913815108c77b55306695385f72', 30_807_429)

    def test_source_predictions_and_actual_refusals_remain_distinct(self):
        self.assertEqual(len(self.data), 60)
        plan = json.loads(self.data['source/plan.json'])
        report = json.loads(self.data['source/report.json'])
        self.assertEqual((len(plan['cases']), len(plan['sources'])), (10, 20))
        self.assertEqual(len(report['commands']), 12)
        self.assertEqual(report['prediction_mismatches'], [])
        self.assertTrue(report['source_unchanged'])
        self.assertTrue(report['first_source_unchanged'])
        self.assertEqual(report['before'], report['after'])
        self.assertEqual(sum(row['exit_code'] == 0 for row in report['commands']), 4)
        self.assertEqual(sum(row['exit_code'] == 1 for row in report['commands']), 8)
        for i, row in enumerate(report['commands'], 1):
            self.assertEqual(json.loads(self.data[f'source/observation-{i:02}.json']), row)
        refusals = [json.loads(row['stdout'])['diagnostics'][0]['code']
                    for row in report['commands'] if row['exit_code'] == 1]
        self.assertEqual(refusals.count('parse'), 7)
        self.assertEqual(refusals.count('type_mismatch'), 1)

    def test_failed_lean_attempt_is_not_promoted_to_a_proof(self):
        first = json.loads(self.data['encoding/observation-01/report.json'])
        self.assertEqual([row['exit_code'] for row in first['commands']], [0, 1])
        self.assertTrue(first['source_unchanged'])
        self.assertEqual(first['before'], first['after'])
        output = self.data['encoding/observation-01/proof.stdout']
        self.assertIn(b'failed to synthesize', output)
        self.assertIn(b'sorryAx', output)
        self.assertEqual(self.data['encoding/FiniteTagStudy.lean'],
                         self.data['encoding/observation-01/FiniteTagStudy.lean.txt'])

    def test_separate_repair_retains_the_actual_standard_axiom_scope(self):
        current = json.loads(self.data['encoding/observation-02/report.json'])
        self.assertEqual([row['exit_code'] for row in current['commands']], [0, 0])
        self.assertTrue(current['source_unchanged'])
        self.assertEqual(current['before'], current['after'])
        output = self.data['encoding/observation-02/proof.stdout'].decode()
        lines = output.splitlines()
        self.assertEqual(len(lines), 15)
        self.assertTrue(all(line.endswith('depends on axioms: [propext]') for line in lines))
        self.assertNotIn('sorryAx', output)
        self.assertEqual(self.data['encoding/observation-02/proof.stderr'], b'')
        self.assertEqual(self.data['encoding/FiniteTagStudy-v2.lean'],
                         self.data['encoding/observation-02/FiniteTagStudy-v2.lean.txt'])


class FirstCarrierBody(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('body-index.json', 'body-first.tar.xz',
            '7f3bc4ede17b2745a58e2280435d13e4df35585fb1cbf55d3135003d8e84be5b',
            594608, 'e9af41b1dcc609b267e90614a5351613a3cfca9bb9d55799dec2ee57f5778e56', 7_089_180)

    def test_observer_path_error_does_not_claim_a_lean_run(self):
        self.assertEqual(len(self.data), 38)
        failure = json.loads(self.data['observer-error/failure-summary.json'])
        self.assertEqual(failure['stage'], 'observer preflight, before Lean commands')
        self.assertEqual(failure['actual_companion'], '/Users/masa/git/qlirgo')
        self.assertIn('no validation command ran', failure['result'])

    def test_first_shadowed_postcondition_remains_a_failed_compile(self):
        first = json.loads(self.data['compile-first/report.json'])
        self.assertTrue(first['source_unchanged'])
        self.assertEqual(first['before'], first['after'])
        self.assertEqual([row['exit_code'] for row in first['commands']], [1])
        self.assertFalse(first['pass'])
        self.assertIn(b'Invalid field `cols`', self.data['compile-first/module.stdout'])
        self.assertIn(b'logical : checked.logical = logical', self.data['compile-first/Qirf-Carrier.lean.txt'])

    def test_successful_reductions_cannot_override_a_failed_compiled_audit(self):
        reductions = json.loads(self.data['recursive-owner-reading/observation-summary.json'])
        self.assertTrue(reductions['pass'])
        self.assertEqual([row['exit_code'] for row in reductions['commands']], [0, 0])
        audit = json.loads(self.data['compiled-audit-refusal/observation-summary.json'])
        self.assertFalse(audit['pass'])
        self.assertEqual([row['exit_code'] for row in audit['commands']], [1])
        self.assertEqual(audit['changed_source_files'], [])
        self.assertIn(b'readOwners._unsafe_rec: partial project declaration',
                      self.data['compiled-audit-refusal/registry.stdout'])
        fold = json.loads(self.data['fold-first/observation-summary.json'])
        self.assertFalse(fold['pass'])
        self.assertIn(b'unexpected token', self.data['fold-first/module.stdout'])


class FirstFiniteDeclarations(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('declarations-index.json', 'declarations-first.tar.xz',
            'd0997f0a9c821eeecc559ab9f6a6f5aceddc450437e352ff0c0679635c73aa5d',
            638664, '92683f7179c3c8c270186a199b89bbfcfab3cb492c48ba548bdb68f94aa59387', 7_227_062)

    def test_failed_documentation_expectation_preserves_original_sources_and_spaces(self):
        self.assertEqual(len(self.data), 23)
        first = json.loads(self.data['first/report.json'])
        self.assertTrue(first['source_unchanged'])
        self.assertEqual(first['before'], first['after'])
        self.assertEqual([row['exit_code'] for row in first['commands']], [0, 101])
        self.assertIn(b'199 passed; 0 failed; 115 ignored', self.data['first/unit.stdout'])
        self.assertIn(b'finite_type_and_member_docs_keep_original_targets_without_verification_claims ... FAILED',
                      self.data['first/integration.stdout'])
        self.assertIn(b'rendered.contains("```text\\nSecond.\\n```")',
                      self.data['first-source/tests/documentation.rs.txt'])
        self.assertIn(b'rendered.contains("```text\\nSecond. \\n```")',
                      self.data['repair-01/documentation.rs.txt'])

    def test_successful_integration_does_not_hide_the_separate_strict_lint_refusal(self):
        repair = json.loads(self.data['repair-01/observation-summary.json'])
        self.assertFalse(repair['pass'])
        self.assertEqual([row['exit_code'] for row in repair['commands']], [0, 101])
        self.assertIn(b'needlessly taken reference of left operand', self.data['repair-01/lint.stderr'])
        self.assertIn(b'35 passed; 0 failed', self.data['repair-01/integration.stdout'])
        self.assertIn(b'4 passed; 0 failed', self.data['repair-01/integration.stdout'])


class FirstNominalResolution(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('resolution-index.json', 'resolution-first.tar.xz',
            '4373a1a8dc7fa01116cac763d9ffbdd26d45700f83cc9c1accd6f76ecde8cedc',
            601404, 'd37ed321b00f82428748e9998e339e6c0f49154f1de795cd4a45cda49ec99f64', 6_964_921)

    def test_new_type_category_requires_explicit_consumers_before_it_compiles(self):
        self.assertEqual(len(self.data), 10)
        report = json.loads(self.data['report.json'])
        self.assertTrue(report['source_unchanged'])
        self.assertEqual(report['before'], report['after'])
        self.assertFalse(report['pass'])
        self.assertEqual([row['exit_code'] for row in report['commands']], [101])
        self.assertEqual(self.data['compile.stderr'].count(b'error[E0004]'), 8)
        self.assertIn(b'non-exhaustive patterns', self.data['compile.stderr'])
        self.assertIn(b'Target::Type', self.data['compile.stderr'])
        self.assertIn(b'fn check_members', self.data['source/src/frontend/resolve/nominal.rs.txt'])


class FirstNominalElaboration(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('elaboration-index.json', 'elaboration-first.tar.xz',
            'e8587e18de7233799a4313e7aa49a7cc853fe442c8dc847ebf39a38542cc6d80',
            737456, 'e899297cfb3b1fe6ad609eaed1f5b9fe38f955efa6cfaf0629d79c4c4335ea16', 10_294_380)

    def test_initial_compile_failures_are_not_passing_type_or_native_checks(self):
        self.assertEqual(len(self.data), 101)
        report = json.loads(self.data['first/report.json'])
        self.assertFalse(report['pass'])
        self.assertTrue(report['source_unchanged'])
        self.assertEqual(report['before'], report['after'])
        self.assertEqual([row['exit_code'] for row in report['commands']], [101])
        self.assertEqual(self.data['first/check.stderr'].count(b'error[E0004]'), 15)
        self.assertEqual(self.data['first/check.stderr'].count(b'error[E0284]'), 1)

    def test_original_nat_call_mistake_and_strict_lint_refusal_remain_failed_attempts(self):
        first = json.loads(self.data['repair-01/observation-summary.json'])
        lint = json.loads(self.data['repair-02/observation-summary.json'])
        self.assertFalse(first['pass'])
        self.assertFalse(lint['pass'])
        self.assertEqual([row['exit_code'] for row in first['commands']], [0, 101])
        self.assertEqual([row['exit_code'] for row in lint['commands']], [0, 0, 0, 101])
        self.assertIn(b'previous(3)', self.data['repair-01/source/src/frontend/check/nominal/tests.rs.txt'])
        self.assertIn(b'expected `)`, found natural number', self.data['repair-01/unit.stdout'])
        self.assertIn(b'clippy::map_entry', self.data['repair-02/lint.stderr'])

    def test_original_ast_deletion_counterexample_is_retained_before_the_repair(self):
        report = json.loads(self.data['removed-type/observation-summary.json'])
        self.assertFalse(report['pass'])
        self.assertTrue(report['source_unchanged'])
        self.assertEqual([row['exit_code'] for row in report['commands']], [101])
        self.assertIn(b'syntax.type_decls.clear()', self.data['removed-type/source/src/frontend/check/nominal/tests.rs.txt'])
        self.assertIn(b'deleting AST declarations must not bypass original-source validation', self.data['removed-type/unit.stdout'])


class FirstNominalDependencies(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('dependencies-index.json', 'dependencies-first.tar.xz',
            'b2f917333ced54d8699e8891dcb50f9418fe8cfbbe1840f2479bc0ec296c220c',
            616624, 'd66e225d82a55f76a6a5dabe817a77c113132885722648c1b7606b340fdecedd', 7_318_408)

    def test_initial_fixture_and_qualification_errors_remain_failed_windows(self):
        self.assertEqual(len(self.data), 28)
        first = json.loads(self.data['first/report.json'])
        repair = json.loads(self.data['repair-01/observation-summary.json'])
        self.assertFalse(first['pass'])
        self.assertFalse(repair['pass'])
        self.assertTrue(first['source_unchanged'])
        self.assertTrue(repair['source_unchanged'])
        self.assertEqual(first['before'], first['after'])
        self.assertIn(b'error[E0599]', self.data['first/check.stderr'])
        self.assertIn(b'error[E0063]', self.data['first/check.stderr'])
        self.assertIn(b'error[E0433]', self.data['repair-01/check.stderr'])

    def test_the_existing_public_thread_sharing_contract_is_preserved_as_a_real_regression(self):
        report = json.loads(self.data['send-sync/observation-summary.json'])
        self.assertFalse(report['pass'])
        self.assertTrue(report['source_unchanged'])
        self.assertEqual([row['exit_code'] for row in report['commands']], [101])
        self.assertEqual(self.data['send-sync/check.stderr'].count(b'error[E0277]'), 8)
        caller = self.data['send-sync/unchanged-caller-sized-source.rs.txt']
        self.assertIn(b'send_sync::<ParsedProgram>()', caller)
        self.assertIn(b'std::thread::spawn(move ||', caller)
        self.assertIn(b'Rc<BTreeMap', self.data['send-sync/check.stderr'])


class FirstCarrierNative(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('native-index.json', 'native-first.tar.xz',
            '9bb7854efc3166cf4cfcb1e4f847dbc6eab7417fdd3608b150a9ce3e9ef12ddb',
            717976, '8598d9e9caf991c6a1464afeae13cb4551ad9607c0ac862ed5694a0bae33a18f', 38_450_889)

    def test_first_source_numeric_and_transport_errors_remain_failed_attempts(self):
        self.assertEqual(len(self.data), 408)
        first = json.loads(self.data['sources-first-build/report.json'])
        self.assertFalse(first['pass'])
        self.assertTrue(first['source_unchanged'])
        self.assertIn(b'unexpected token', self.data['sources-first-build/stdout'])
        self.assertIn(b'isError', self.data['sources-first-examples/stdout'])
        self.assertIn(b'maximum recursion depth', self.data['nested-rfl-probe/stdout'])
        self.assertEqual(self.data['nat-reduction/stdout'].count(b'maximum number of heartbeats'), 2)
        self.assertIn(b'error[E0308]', self.data['native-first-rust-compile/stderr'])

    def test_actual_final_compilers_native_scope_and_protected_outputs_are_separate(self):
        for stage in ['native-final-normal-rust', 'native-final-msrv-rust']:
            report = json.loads(self.data[stage + '/report.json'])
            self.assertTrue(report['pass'])
            self.assertTrue(report['source_and_kernel_unchanged'])
            self.assertEqual(report['before'], report['after'])
            self.assertIn('17 passed; 0 failed; 0 ignored', report['test_summaries'][0])
            self.assertEqual(report['test_summaries'][1], 'native test gate: zero conditional native skips')
        lean = json.loads(self.data['native-v2-lean-validation/report.json'])
        self.assertTrue(lean['pass'])
        self.assertEqual(len(lean['commands']), 8)
        self.assertTrue(all(row['exit_code'] == 0 for row in lean['commands']))
        self.assertEqual(len(lean['output_comparisons']), 6)
        self.assertTrue(all(row['identical_recorded_output'] for row in lean['output_comparisons']))

    def test_original_extraction_uses_immutable_recovery_not_live_current_evidence(self):
        reference_raw = self.data['native-v2-lean-validation/extract-stdout-reference.json']
        reference = json.loads(reference_raw)
        actual = read_historical_native_stdout(FIXTURES, reference_raw)
        self.assertEqual(len(actual), reference['observed_stdout_bytes'])
        self.assertEqual(hashlib.sha256(actual).hexdigest(), reference['observed_stdout_sha256'])
        self.assertTrue(reference['byte_identical_to_decompressed_canonical'])

    def test_historical_extraction_reader_is_portable_without_git_or_live_evidence(self):
        reference_raw = self.data['native-v2-lean-validation/extract-stdout-reference.json']
        reference = json.loads(reference_raw)
        with tempfile.TemporaryDirectory() as temporary:
            fixtures = Path(temporary)
            for name in [NATIVE_EXTRACT_RECOVERY, NATIVE_EXTRACT_GZIP]:
                (fixtures / name).write_bytes((FIXTURES / name).read_bytes())
            self.assertFalse((fixtures / '.git').exists())
            self.assertFalse((fixtures / reference['canonical_gzip']).exists())
            actual = read_historical_native_stdout(fixtures, reference_raw)
            self.assertEqual(hashlib.sha256(actual).hexdigest(), reference['observed_stdout_sha256'])

    def test_historical_extraction_refuses_changed_compressed_blob(self):
        reference_raw = self.data['native-v2-lean-validation/extract-stdout-reference.json']
        provenance = (FIXTURES / NATIVE_EXTRACT_RECOVERY).read_bytes()
        packed = (FIXTURES / NATIVE_EXTRACT_GZIP).read_bytes()
        changed = packed[:-1] + bytes([packed[-1] ^ 1])
        with self.assertRaisesRegex(AssertionError, 'historical extraction gzip changed'):
            historical_native_stdout(reference_raw, provenance, changed)

    def test_historical_extraction_refuses_changed_original_reference(self):
        reference = json.loads(self.data['native-v2-lean-validation/extract-stdout-reference.json'])
        reference['canonical_gzip'] = '../../unrelated-current-evidence.json.gz'
        changed = json.dumps(reference).encode('utf-8')
        with self.assertRaisesRegex(AssertionError, 'historical extraction reference changed'):
            historical_native_stdout(changed, (FIXTURES / NATIVE_EXTRACT_RECOVERY).read_bytes(),
                                     (FIXTURES / NATIVE_EXTRACT_GZIP).read_bytes())

    def test_historical_extraction_refuses_changed_recovery_provenance(self):
        reference = self.data['native-v2-lean-validation/extract-stdout-reference.json']
        original = (FIXTURES / NATIVE_EXTRACT_RECOVERY).read_bytes()
        for field in ['git_commit', 'git_blob']:
            with self.subTest(field=field):
                provenance = json.loads(original)
                provenance['recovery'][field] = '0' * 40
                changed = json.dumps(provenance).encode('utf-8')
                with self.assertRaisesRegex(AssertionError, 'historical extraction recovery metadata changed'):
                    historical_native_stdout(reference, changed, (FIXTURES / NATIVE_EXTRACT_GZIP).read_bytes())


# Type-import history: "tests/fixtures/authoring_sessions/finite-adts-v030/aliases-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/aliases-index.json".
# Current scope: "tests/fixtures/authoring_sessions/finite-adts-v030/aliases-validation.json".
class FirstCarrierTypeAliases(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('aliases-index.json', 'aliases-first.tar.xz',
            '1806082f36d6a1a281bb441438bd831204324b44f7f5a9e1c02e7c6d7e096941',
            801416, '0bacaa8c939d15c718e09be8cc6dfdedaee42aa0304e9135cce6c00e474ffab3', 36_743_615)

    def test_first_source_and_caller_mistake_remain_separate_from_native_scope(self):
        first = json.loads(self.data['adt64-type-alias-first-study/report.json'])
        repair = json.loads(self.data['adt64-type-alias-caller-repair-study/report.json'])
        self.assertEqual(len(self.data), 263)
        self.assertEqual(first['prediction_mismatches'], ['bit-control-source'])
        self.assertEqual(repair['prediction_mismatches'], [])
        self.assertTrue(first['source_and_binaries_unchanged'])
        self.assertTrue(repair['source_and_binaries_unchanged'])
        original = {k: v for k, v in first['before']['inputs'].items() if k.startswith('projects/')}
        self.assertEqual(original, repair['before']['inputs'])
        diagnostic = json.loads(self.data['adt64-type-alias-first-study/bit-control-source.stdout'])
        self.assertEqual(diagnostic['diagnostics'][0]['code'], 'invalid_entry')
        self.assertEqual(repair['commands'][0]['exit_code'], 0)
        after = json.loads(self.data['adt64-type-alias-native-after/report.json'])
        self.assertTrue(after['pass'])
        self.assertTrue(after['source_and_kernel_unchanged'])
        self.assertEqual([r['actual_code'] for r in after['commands']],
                         ['decoded_view', 'decoded_view', 'contract'])
        self.assertTrue(all(r['exit_code'] == 1 for r in after['commands']))

    def test_failed_target_and_cycle_prediction_are_not_successes(self):
        wrong_target = json.loads(self.data['adt64-alias-resolution-first-tests/observation-summary.json'])
        self.assertFalse(wrong_target['pass'])
        self.assertIn(b'unknown target `Tests`', self.data['adt64-alias-resolution-first-tests/stderr'])
        first_native = json.loads(self.data['adt64-alias-source-normal-rust/observation-summary.json'])
        self.assertFalse(first_native['pass'])
        self.assertEqual(first_native['commands'][1]['exit_code'], 101)
        output = self.data['adt64-alias-source-normal-rust/native.stdout']
        self.assertIn(b'17 passed; 1 failed', output)
        self.assertIn(b'left: "limit"', output)
        self.assertIn(b'right: "contract"', output)

    def test_current_proof_and_both_compilers_bind_the_same_selected_checker(self):
        lean = json.loads(self.data['adt64-alias-source-lean-validation/report.json'])
        self.assertTrue(lean['pass'])
        self.assertEqual(len(lean['commands']), 8)
        self.assertTrue(all(r['exit_code'] == 0 for r in lean['commands']))
        self.assertEqual(len(lean['output_comparisons']), 6)
        self.assertTrue(all(r['identical_recorded_output'] for r in lean['output_comparisons']))
        for stage in ['adt64-alias-source-final-normal-rust', 'adt64-alias-source-final-msrv-rust']:
            report = json.loads(self.data[stage + '/report.json'])
            self.assertTrue(report['pass'])
            self.assertEqual(report['before'], report['after'])
            self.assertEqual(report['after']['kernel'], lean['after']['kernel'])
            self.assertIn('18 passed; 0 failed; 0 ignored', report['test_summaries'][0])
            self.assertEqual(report['test_summaries'][1], 'native test gate: zero conditional native skips')


# Numeral history: "tests/fixtures/authoring_sessions/finite-adts-v030/numerals-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/numerals-index.json".
# Current scope: "tests/fixtures/authoring_sessions/finite-adts-v030/numerals-validation.json".
class FirstCarrierSourceNumerals(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('numerals-index.json', 'numerals-first.tar.xz',
            'a1ebb7e260d645d92a9bb23f46c5b13516d09d4088839616ea933b2668fce6bb',
            1011980, 'b1eea4b33b2f160105ccf96c1b6f98038cf89b719ea8f8734878e6e1ee079e82', 42_346_961)

    def test_source_parse_and_null_view_progress_do_not_become_accepted_handles(self):
        first = json.loads(self.data['adt64-nat-spelling-first-study/report.json'])
        after = json.loads(self.data['adt64-nat-spelling-after-study/report.json'])
        self.assertEqual(len(self.data), 133)
        self.assertEqual(first['prediction_mismatches'], ['leading-zero-native'])
        self.assertTrue(first['source_and_binaries_unchanged'])
        self.assertEqual([r['actual_code'] for r in first['commands']],
                         ['unsupported', 'decoded_view', 'parse', 'decoded_view'])
        self.assertTrue(after['pass'])
        self.assertEqual([r['actual_code'] for r in after['commands']], ['decoded_view', 'contract'])
        self.assertEqual(first['before']['original_inputs'], after['before']['original_inputs'])
        self.assertTrue(after['source_and_kernel_unchanged'])

    def test_bad_original_raw_handle_is_a_preserved_counterexample(self):
        first = json.loads(self.data['adt64-nat-spelling-first-native-test/report.json'])
        self.assertFalse(first['pass'])
        self.assertEqual(first['exit_code'], 101)
        self.assertTrue(first['source_unchanged'])
        output = self.data['adt64-nat-spelling-first-native-test/stdout']
        self.assertIn(b'outcome canonical-field-numeral accepted', output)
        self.assertIn(b'outcome leading-zero-field-numeral accepted', output)
        self.assertIn(b'called `Result::unwrap_err()` on an `Ok` value: CarrierChecked', output)
        source = '/sources/src/interchange/native/carrier/tests.rs.txt'
        self.assertEqual(self.data['adt64-nat-spelling-first-native-test' + source],
                         self.data['adt64-nat-spelling-normal-rust' + source])

    def test_repaired_checker_preserves_protected_outputs_and_both_native_test_runs(self):
        lean = json.loads(self.data['adt64-nat-spelling-lean-validation/report.json'])
        self.assertTrue(lean['pass'])
        self.assertEqual(len(lean['commands']), 8)
        self.assertTrue(all(r['exit_code'] == 0 for r in lean['commands']))
        self.assertEqual(len(lean['output_comparisons']), 6)
        self.assertTrue(all(r['identical_recorded_output'] for r in lean['output_comparisons']))
        for stage in ['adt64-nat-spelling-normal-rust', 'adt64-nat-spelling-msrv-rust']:
            report = json.loads(self.data[stage + '/report.json'])
            self.assertTrue(report['pass'])
            self.assertEqual(report['before'], report['after'])
            self.assertEqual(report['after']['kernel'], lean['after']['kernel'])
            self.assertIn('19 passed; 0 failed; 0 ignored', report['test_summaries'][0])
            self.assertEqual(report['test_summaries'][1], 'native test gate: zero conditional native skips')


# Nat syntax history: "tests/fixtures/authoring_sessions/finite-adts-v030/naturals-syntax-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/naturals-syntax-index.json".
# Scope: "tests/fixtures/authoring_sessions/finite-adts-v030/naturals-syntax-validation.json".
class FirstFieldNaturalSyntax(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('naturals-syntax-index.json', 'naturals-syntax-first.tar.xz',
            '54b64ba69903ac1fa2c76a893e952c7d13d04ca89f6d345fa28cdfe2d9ee145a',
            818488, '14f9f900086faf87d6672af34fbed26e5b55d6e3e9348b5c00b69a6e9d65337e', 38_792_408)

    def test_original_field_programs_keep_their_actual_source_and_native_barriers(self):
        first = json.loads(self.data['first-study/report.json'])
        self.assertEqual(len(self.data), 571)
        self.assertTrue(first['source_and_binaries_unchanged'])
        self.assertEqual(first['prediction_mismatches'], [])
        self.assertEqual(len(first['commands']), 28)
        source = [r for r in first['commands'] if r['label'].endswith('-source')]
        native = [r for r in first['commands'] if r['label'].endswith('-native')]
        self.assertEqual([r['actual_code'] for r in source[:6]], ['unsupported'] * 6)
        self.assertEqual([r['actual_code'] for r in source[6:]],
                         ['size', 'unsupported', 'size', 'size', 'limit', 'name', 'static', 'cycle'])
        self.assertEqual([r['actual_code'] for r in native], ['decoded_view'] + ['contract'] * 13)
        self.assertTrue(all(r['exit_code'] == 1 for r in first['commands']))

    def test_compilation_does_not_hide_forbidden_generated_recursion(self):
        self.assertIn(b'DecidableEq', self.data['first-syntax-build/stdout'])
        inspection = self.data['generated-inspection/stdout']
        self.assertIn(b'instBEqExpr.beq._unsafe_rec', inspection)
        self.assertIn(b'instReprExpr.repr._unsafe_rec', inspection)
        self.assertIn(b'evaluate._unsafe_rec', inspection)
        self.assertIn(b'partial=true', inspection)
        rejected = json.loads(self.data['total-generated-audit/observation-summary.json'])
        self.assertFalse(rejected['pass'])
        self.assertIn(b'mapValues._unsafe_rec', self.data['total-generated-audit/stdout'])
        accepted = json.loads(self.data['fold-generated-audit/observation-summary.json'])
        self.assertTrue(accepted['pass'])
        self.assertIn(b'Audited 268', self.data['fold-generated-audit/stdout'])
        final_source = self.data['fold-generated-audit/sources/lean-kernel/QleisliKernel/Semantics/SourceNatural.lean.txt']
        self.assertIn(b'Nat.rec', final_source)
        self.assertIn(b'arguments.foldr', final_source)
        self.assertNotIn(b'deriving BEq', final_source)

    def test_current_reference_proof_and_native_regressions_remain_separate_from_dispatch(self):
        self.assertIn(b'unexpected token', self.data['first-syntax-tests/stdout'])
        self.assertIn(b'did not reduce', self.data['syntax-tests-v2/stdout'])
        total = json.loads(self.data['total-syntax-tests/observation-summary.json'])
        self.assertTrue(total['pass'])
        lean = json.loads(self.data['syntax-reference-lean-validation/report.json'])
        self.assertTrue(lean['pass'])
        self.assertEqual(len(lean['commands']), 8)
        self.assertEqual(len(lean['output_comparisons']), 6)
        self.assertTrue(all(r['identical_recorded_output'] for r in lean['output_comparisons']))
        for stage in ['syntax-normal-rust', 'syntax-msrv-rust']:
            report = json.loads(self.data[stage + '/report.json'])
            self.assertTrue(report['pass'])
            self.assertEqual(report['before'], report['after'])
            self.assertEqual(report['after']['kernel'], lean['after']['kernel'])
            self.assertIn('19 passed; 0 failed; 0 ignored', report['test_summaries'][0])
            self.assertEqual(report['test_summaries'][1], 'native test gate: zero conditional native skips')


# Affine/header first history: "tests/fixtures/authoring_sessions/finite-adts-v030/naturals-affine-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/naturals-affine-index.json".
# Scope: "tests/fixtures/authoring_sessions/finite-adts-v030/naturals-affine-validation.json".
class FirstFieldNaturalAffine(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('naturals-affine-index.json', 'naturals-affine-first.tar.xz',
            '1f8141b11bdbfabd598d62b855caada565a3fbcf0a1cc92610bb7b761dcb80e1',
            99288, 'a0f16b36bab15a784294af44518a4c4d7deb0b8e4ec61be5ba54166053ad5a5f', 1_464_256)

    def report(self, stage):
        return json.loads(self.data['adt64-field-' + stage + '/observation.json'])

    def source(self, stage, name):
        manifest = json.loads(self.data['adt64-field-' + stage + '/original-source-records.json'])
        entry = manifest['sources/lean-kernel/QleisliKernel/' + name + '.lean']
        data = self.data[entry['record']]
        self.assertEqual((len(data), hashlib.sha256(data).hexdigest()),
                         (entry['bytes'], entry['sha256']))
        return data

    def test_failed_authoring_attempts_remain_failed_original_observations(self):
        self.assertEqual(len(self.data), 174)
        for stage in ['affine-first-build', 'affine-first-operation-proofs',
                      'affine-first-constraints-build', 'affine-constraints-v2-build',
                      'affine-constraints-v3-build', 'affine-first-checks', 'affine-checks-v2',
                      'predicates-first-build', 'predicates-build-v2', 'helper-declarations-first-build']:
            report = self.report(stage)
            self.assertFalse(report['pass'])
            self.assertTrue(report['source_unchanged'])
            self.assertNotEqual(report['exit_code'], 0)
        self.assertIn(b'Decidable', self.data['adt64-field-affine-first-checks/stdout'])
        self.assertIn(b'maximum number of heartbeats', self.data['adt64-field-affine-checks-v2/stdout'])
        self.assertIn(b'List.rec', self.data['adt64-field-predicates-build-v2/stdout'])

    def test_exact_operations_and_actual_original_headers_have_audited_total_definitions(self):
        for stage in ['affine-checks-v3', 'predicates-headers-first-checks', 'affine-generated-audit']:
            report = self.report(stage)
            self.assertTrue(report['pass'])
            self.assertTrue(report['source_windows_unchanged'])
        self.assertIn(b'Audited 759', self.data['adt64-field-affine-generated-audit/stdout'])
        predicates = self.source('affine-generated-audit', 'SourceTypes/NaturalPredicates')
        self.assertIn(b'Nat.rec', predicates)
        self.assertIn(b'Comparison.negate_relation', predicates)
        constraints = self.source('affine-generated-audit', 'SourceTypes/NaturalConstraints')
        self.assertIn(b'witness : NoValues source', constraints)
        self.assertIn(b'proof.witness', predicates)
        sources = self.source('affine-generated-audit', 'SourceTypes/Declarations')
        self.assertIn(b'static-fn', sources)
        self.assertIn(b'original.declaration.isPublic', sources)

    def test_fresh_proof_and_native_results_do_not_claim_generic_helper_dispatch(self):
        lean = self.report('affine-helpers-lean-validation')
        self.assertTrue(lean['pass'])
        self.assertEqual(len(lean['commands']), 8)
        self.assertEqual(len(lean['output_comparisons']), 6)
        self.assertTrue(all(row['identical_recorded_output'] for row in lean['output_comparisons']))
        for stage in ['affine-normal-rust', 'affine-msrv-rust']:
            report = self.report(stage)
            self.assertTrue(report['pass'])
            self.assertTrue(report['source_windows_unchanged'])
            self.assertEqual(report['before'], report['after'])
            self.assertEqual(report['after']['kernel'], lean['after']['kernel'])
            self.assertIn('19 passed; 0 failed; 0 ignored', report['test_summaries'][0])
            self.assertEqual(report['test_summaries'][1], 'native test gate: zero conditional native skips')
        source = self.source('affine-generated-audit', 'SourceTypes')
        self.assertIn(b'literalWidth width', source)
        self.assertIn(b'General Nat expressions still refuse', source)


# Recovery records: "tests/fixtures/authoring_sessions/finite-adts-v030/helper-authoring-recovery.json"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/helper-first-test-recovered.lean.txt".
class RecoveredHelperAuthoring(unittest.TestCase):
    def test_retained_events_do_not_replace_unavailable_full_observations(self):
        data = (FIXTURES / 'helper-authoring-recovery.json').read_bytes()
        self.assertEqual(hashlib.sha256(data).hexdigest(),
                         'd5db45d42f187596c104b1f0b8ef3777cdb3a242dcd17a8f6ce1a3011aa6ad9b')
        recovered = json.loads(data)
        self.assertEqual(len(recovered['items']), 25)
        self.assertIn('result remains unknown', recovered['scope'])
        self.assertIn('not a substitute for lost raw streams', recovered['scope'])

    def test_first_test_source_is_preserved_as_inert_bytes(self):
        data = (FIXTURES / 'helper-first-test-recovered.lean.txt').read_bytes()
        self.assertEqual((len(data), hashlib.sha256(data).hexdigest()),
                         (4911, '730d399cac9ddb94b4d6c5a9a74ddfd35604b1e2ae40eccb5d17dd00bf14f18b'))


# Original helper history: "tests/fixtures/authoring_sessions/finite-adts-v030/helpers-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/helpers-index.json".
# Current scope: "tests/fixtures/authoring_sessions/finite-adts-v030/helpers-validation.json".
class FirstOriginalHelperFields(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('helpers-index.json', 'helpers-first.tar.xz',
            '2d62e735841fb5f738ad5f2d93e3f085bb8af346ff2b1ee739a168e08ed48c6b',
            79872, '55e376fdd8e7eaeb83915551047d46ae3078363f985e28727a45b81301649b00', 1_913_960)

    def report(self, stage):
        return json.loads(self.data[stage + '/observation.json'])

    def test_failed_elaboration_and_first_native_observations_remain_failed(self):
        self.assertEqual(len(self.data), 193)
        for stage in ['definition-binding-support-build', 'bound-helper-reader-first-build',
                      'bound-helper-call-checks', 'field-natural-dispatch-first-build',
                      'field-natural-dispatch-build-v2', 'field-natural-dispatch-build-v3',
                      'field-natural-dispatch-build-v4', 'field-natural-dispatch-build-v5',
                      'field-natural-dispatch-build-v6', 'first-field-native-old-checker',
                      'helper-field-normal-rust']:
            self.assertFalse(self.report(stage)['pass'])
        first = self.data['first-field-native-old-checker/stdout']
        self.assertIn(b'outcome field-nat-precedence contract', first)
        native = self.data['helper-field-normal-rust/native.stdout']
        self.assertIn(b'outcome field-nat-i128-intermediate-overflow limit', native)
        self.assertIn(b'right: "contract"', native)

    def test_executable_lean_assertions_keep_their_bounded_test_scope(self):
        for stage, count in [('generic-execution-checks', 26),
                             ('bound-helper-call-checks-v2', 17),
                             ('field-source-first-checks', 18)]:
            self.assertTrue(self.report(stage)['pass'])
            self.assertEqual(self.data[stage + '/stdout'].count(b'PASS: '), count)
        self.assertIn(b'Audited 1332', self.data['bound-helper-compiled-audit/stdout'])

    def test_fresh_shared_proofs_preserve_all_six_protected_outputs(self):
        lean = self.report('helper-field-full-lean')
        self.assertTrue(lean['pass'])
        self.assertTrue(lean['source_windows_unchanged_except_registry'])
        self.assertEqual(lean['changed_source_files'], ['lean/schema-registry.json'])
        self.assertEqual(len(lean['commands']), 8)
        self.assertEqual(len(lean['output_comparisons']), 6)
        self.assertTrue(all(row['identical_recorded_output'] for row in lean['output_comparisons']))

    def test_sequential_native_windows_retain_the_actual_small_source_cases(self):
        kernel = self.report('helper-field-full-lean')['after']['kernel']
        for stage in ['helper-field-normal-rust-v2', 'helper-field-msrv-rust-v2']:
            report = self.report(stage)
            self.assertTrue(report['pass'])
            self.assertTrue(report['source_windows_unchanged'])
            self.assertEqual(report['before'], report['after'])
            self.assertEqual(report['after']['kernel'], kernel)
            self.assertIn('21 passed; 0 failed; 0 ignored', report['test_summaries'][0])
            self.assertEqual(report['test_summaries'][1], 'native test gate: zero conditional native skips')
            output = self.data[stage + '/native.stdout']
            self.assertIn(b'outcome field-nat-original-ordinal-order accepted', output)
            self.assertIn(b'outcome field-nat-simultaneous-original-binders accepted', output)
            self.assertIn(b'outcome field-nat-unused-private-helper contract', output)


# Host root history: "tests/fixtures/authoring_sessions/finite-adts-v030/host-roots-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/host-roots-index.json".
# Scope: "tests/fixtures/authoring_sessions/finite-adts-v030/host-roots-validation.json".
class FirstHostTypeRoots(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('host-roots-index.json', 'host-roots-first.tar.xz',
            '950aa96690bfb2cb0d7507aa1c4f4367e00b33d040f01b197555d182779bee0a',
            170064, '5f0f6574aacaa29167d40ce35308dcbb295d36e401a808887dfe705421f93ec4', 2_129_955)

    def report(self, stage):
        return json.loads(self.data[stage + '/observation.json'])

    def test_first_configuration_refusals_do_not_validate_type_or_native_rules(self):
        self.assertEqual(len(self.data), 186)
        first = self.report('first')
        self.assertTrue(first['source_unchanged'])
        self.assertEqual([r['exit_code'] for r in first['commands']], [0, 1, 1, 1, 1, 1, 1])
        for case in ['public-host', 'private-host', 'private-facade', 'unit-control', 'unused-host', 'direct-source']:
            result = json.loads(self.data['first/' + case + '.stdout'])
            self.assertEqual(result['diagnostics'][0]['code'], 'project')
            self.assertIn('schema-version = 2', result['diagnostics'][0]['message'])
            repaired = json.loads(self.data['manifest-repair/' + case + '.stdout'])
            self.assertEqual(repaired['diagnostics'][0]['code'], 'unsupported')
        unit = json.loads(self.data['unit-isolation/unit-control.stdout'])
        self.assertEqual(unit['result']['verification']['scope'], 'native-validity')
        self.assertFalse(unit['result']['source_preservation_verified'])

    def test_test_authoring_errors_remain_failed_original_attempts(self):
        self.assertFalse(self.report('first-host-root-tests')['pass'])
        self.assertIn(b'E0061', self.data['first-host-root-tests/stderr'])
        self.assertFalse(self.report('host-root-tests-v2')['pass'])
        self.assertIn(b'expected `;`, found identifier', self.data['host-root-tests-v2/stderr'])
        self.assertTrue(self.report('host-root-tests-v3')['pass'])
        self.assertTrue(self.report('host-root-tests-v4')['pass'])
        self.assertIn(b'7 passed; 0 failed', self.data['host-root-tests-v4/stdout'])

    def test_current_normal_msrv_windows_have_no_conditional_native_skips(self):
        for stage in ['normal-final', 'msrv-final']:
            report = self.report(stage)
            self.assertTrue(report['pass'])
            self.assertTrue(report['source_and_kernel_unchanged'])
            self.assertEqual(report['before'], report['after'])
            for group, counts in [('frontend', [335]), ('integration', [12, 16, 5]), ('native', [21])]:
                summaries = report['test_summaries'][group]
                actual = [int(line.split()[3]) for line in summaries if line.startswith('test result:')]
                self.assertEqual(actual, counts)
                self.assertEqual(summaries[-1], 'native test gate: zero conditional native skips')
        self.assertTrue(self.report('normal-strict-lint')['pass'])

    def test_cli_exposes_real_selection_checks_and_retains_the_execution_gate(self):
        expected = [('public-host', 'unsupported'), ('private-host', 'visibility'),
                    ('private-facade', 'name'), ('unit-control', 'unsupported'),
                    ('unused-host', 'unsupported'), ('direct-source', 'unsupported'),
                    ('isolated-unit', None)]
        for stage in ['cli-normal', 'cli-msrv']:
            report = self.report(stage)
            self.assertTrue(report['pass'])
            self.assertTrue(report['inputs_and_cli_unchanged'])
            self.assertEqual([(row['name'], row['code']) for row in report['cases']], expected)


# Value history: "tests/fixtures/authoring_sessions/finite-adts-v030/values-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/values-index.json".
# Scope: "tests/fixtures/authoring_sessions/finite-adts-v030/values-validation.json".
class FirstOrdinaryValues(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('values-index.json', 'values-first.tar.xz',
            'd12bb0e8fff68ffd6f8b129acd845526ee37242e77115fa0a3ddb9e47af866df',
            215040, '0b2aae13383acde445bbff974515418a79f61d3b32d652169188fca6f1fa6dfc', 2_659_991)

    def report(self, stage):
        return json.loads(self.data[stage + '/observation.json'])

    def test_first_parser_name_failures_remain_separate_from_native_validity(self):
        self.assertEqual(len(self.data), 259)
        first = self.report('first')
        self.assertTrue(first['sources_and_binaries_unchanged'])
        self.assertTrue(first['first_sources_unchanged'])
        self.assertEqual(first['before'], first['after'])
        self.assertEqual([row['code'] for row in first['commands']],
                         ['module', 'module', 'parse', 'parse', 'parse', 'parse',
                          'parse', 'parse', 'parse', 'module', None])
        control = json.loads(self.data['first/bit-control.stdout'])
        self.assertEqual(control['result']['verification']['scope'], 'native-validity')
        self.assertFalse(control['result']['source_preservation_verified'])
        mapping = json.loads(self.data['first/original-source-records.json'])
        source = self.data[mapping['record-order/main.qli']['record']]
        self.assertIn(b'Packet{bit:1,tag:Color::Green,zero:()}', source)

    def test_actual_stack_failure_and_unsuccessful_repairs_are_not_successes(self):
        self.assertFalse(self.report('compile-first')['pass'])
        self.assertIn(b'E0004', self.data['compile-first/stderr'])
        for stage in ['tests-first', 'tests-second']:
            self.assertFalse(self.report(stage)['pass'])
            self.assertIn(b'has overflowed its stack', self.data[stage + '/stderr'])
        self.assertFalse(self.report('tests-third')['pass'])
        self.assertIn(b'parsed_preparation_keeps_concrete_execution_gate',
                      self.data['tests-third/stderr'])
        self.assertTrue(self.report('frontend-first')['pass'])
        self.assertIn(b'348 passed; 0 failed; 0 ignored', self.data['frontend-first/stdout'])

    def test_real_sandbox_failure_and_separate_complete_rerun_retain_their_scopes(self):
        for stage in ['normal-final', 'msrv-final']:
            report = self.report(stage)
            self.assertTrue(report['stable'])
            self.assertEqual(report['before'], report['after'])
            for group, counts in [('frontend', [348]), ('integration', [12, 16, 5]), ('native', [21])]:
                summaries = report['summaries'][group]
                self.assertEqual([int(s.split()[3]) for s in summaries if s.startswith('test result:')], counts)
                self.assertEqual(summaries[-1], 'native test gate: zero conditional native skips')
        self.assertFalse(self.report('normal-final')['pass'])
        self.assertIn(b'Operation not permitted', self.data['normal-final/companion-tests.stdout'])
        self.assertTrue(self.report('companion-normal-retry')['pass'])
        self.assertTrue(self.report('msrv-final')['pass'])
        for stream in ['companion-normal-retry/stdout', 'msrv-final/companion-tests.stdout']:
            lines = self.data[stream].decode().splitlines()
            summaries = [s for s in lines if s.startswith('test result: ok.')]
            self.assertEqual(sum(int(s.split()[3]) for s in summaries), 176)
            self.assertTrue(all('0 failed; 0 ignored' in s for s in summaries))
        self.assertTrue(self.report('passive-readers')['pass'])

    def test_current_cli_refusals_and_four_staged_tools_do_not_claim_nominal_execution(self):
        for stage in ['cli-normal', 'cli-msrv']:
            report = self.report(stage)
            self.assertTrue(report['pass'])
            self.assertTrue(report['stable'])
            self.assertEqual(len(report['cases']), 15)
            cases = {case['name']: case['code'] for case in report['cases']}
            self.assertEqual([cases[n] for n in ['enum', 'classical', 'record', 'field', 'empty', 'public']],
                             ['unsupported'] * 6)
            self.assertEqual([cases[n] for n in ['private', 'quantum-field', 'observation', 'order']],
                             ['visibility', 'type', 'effect', 'ownership'])
        staged = json.loads(self.data['companion-compatibility/staging.json.txt'])
        self.assertEqual([r['name'] for r in staged['files']], ['qargo', 'qlippy', 'qlifmt', 'qlidoc'])
        self.assertTrue(all(r['target_sha256'] == r['staged_sha256'] for r in staged['files']))
        self.assertTrue(self.report('staged-runtime')['pass'])
        self.assertIn(b'no binary-source attestation', self.data['staged-runtime/stdout'])
        validation = json.loads((FIXTURES / 'values-validation.json').read_bytes())
        self.assertEqual(validation['format'], 'qleisli.finite-values-validation')
        sources = json.loads(self.data['final-validated-source-records.json'])
        self.assertEqual(validation['source_files'], {n: row['sha256'] for n, row in sources.items()})
        for name, row in sources.items():
            self.assertEqual(hashlib.sha256(self.data[row['record']]).hexdigest(), row['sha256'], name)
        self.assertEqual(validation['history']['records'], len(self.data))
        self.assertEqual(validation['history']['archive']['sha256'],
                         '0b2aae13383acde445bbff974515418a79f61d3b32d652169188fca6f1fa6dfc')


class CarrierSourceHistory(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history(
            'carrier-source-index.json', 'carrier-source-first.tar.xz',
            '431ca032f33b9c2077e81f908943050508b3987306037577207e65cdcaa43acb', 493792, '21df188096ceff6675f1377abad656cd2cf08379b40c70c252aa40ae5b86684a', 8269775)

    def observation(self, stage):
        return json.loads(self.data[stage + '/observation.json'])

    def source(self, stage, original_name):
        mapping = json.loads(self.data[stage + '/original-source-records.json'])
        row = mapping[original_name]
        raw = self.data[row['record']]
        self.assertEqual((len(raw), hashlib.sha256(raw).hexdigest()),
                         (row['bytes'], row['sha256']))
        return raw

    def root_record(self, original_name):
        mapping = json.loads(self.data['root-capture-records.json'])['records']
        row = mapping[original_name]
        raw = self.data[row['record']]
        self.assertEqual((len(raw), hashlib.sha256(raw).hexdigest()),
                         (row['bytes'], row['sha256']))
        return raw

    def test_first_transport_barriers_and_original_static_plan_failure_are_retained(self):
        first = self.observation('first')
        self.assertTrue(first['stable'])
        self.assertTrue(first['first_sources_unchanged'])
        self.assertEqual(first['before'], first['after'])
        self.assertEqual([row['code'] for row in first['commands']],
                         ['unsupported'] * 4 + [None])
        self.assertIn(b'Q<Tri>', self.source('first', 'direct-enum/main.qli'))
        explicit = json.loads(self.data['type-argument-first/stdout'])
        self.assertEqual(explicit['diagnostics'][0]['code'], 'source')
        self.assertEqual(explicit['diagnostics'][0]['message'],
                         'Basis plan requires its original static binder')
        self.assertEqual(self.observation('type-argument-first')['exit_code'], 1)

    def test_failed_full_lean_attempts_are_separate_from_prepared_and_isolated_work(self):
        failed = self.observation('kernel-tests-decide-cbv-proof-budget')
        self.assertFalse(failed['pass'])
        self.assertEqual(failed['exit_code'], 1)
        prepared = json.loads(self.data['lean-unit-split-candidate/prepared-capture.json'])
        self.assertFalse(prepared['terminal_observation'])
        self.assertIn('UNEXECUTED', prepared['scope'])
        first = json.loads(self.source('isolation-inputs',
            'tests-decide-cbv-proof-budget-manifest.json'))
        corrected = json.loads(self.source('isolation-inputs',
            'tests-decide-cbv-proof-budget-manifest-v2.json'))
        self.assertEqual(first['original_examples'], 475)
        self.assertEqual(corrected['original_examples'], 476)
        self.assertIn('475', corrected['metadata_correction'])
        self.assertNotEqual(first, corrected)
        isolated = self.observation('coverage-decide-cbv-postconditions-v2')
        self.assertTrue(isolated['pass'])
        self.assertEqual(isolated['exit_code'], 0)
        self.assertTrue(isolated['stable'])
        actual = self.source('coverage-decide-cbv-postconditions-v2',
            'explicit-inputs/CarrierSourceCoverageDecideCbvPostconditionsV2.lean')
        self.assertEqual(sum(line.startswith(b'example :')
                             for line in actual.splitlines()), 13)
        applied = json.loads(self.root_record('coverage-v2-root-tests-applied.json'))
        self.assertTrue(applied['namespace_only'])
        self.assertEqual(applied['actual_isolated_report_sha256'],
                         isolated['full_local_report_sha256'])
        self.assertNotEqual(applied['before'], applied['after'])

    def test_interrupted_normal_and_separate_completion_and_full_msrv_keep_their_scopes(self):
        initial = self.observation('normal-final')
        completion = self.observation('normal-remaining-bounded')
        msrv = self.observation('msrv-current-bounded')
        joined = self.observation('rust-current-join')
        self.assertFalse(initial['pass'])
        interrupted = next(row for row in initial['commands']
                           if row['name'] == 'companion-tests')
        self.assertTrue(interrupted['executed'])
        self.assertEqual(interrupted['exit_code'], -15)
        for report in (initial, completion, msrv):
            self.assertTrue(report['stable'])
            self.assertEqual(report['before'], report['after'])
            self.assertEqual(report['before'], initial['before'])
        for report in (completion, msrv):
            self.assertTrue(report['pass'])
            self.assertTrue(all(row['executed'] and row['exit_code'] == 0
                                for row in report['commands']))
        self.assertEqual(msrv['selection'], 'all')
        self.assertTrue(joined['pass'])
        self.assertTrue(joined['normal_initial_interruption_preserved'])
        self.assertEqual(set(completion['selection']),
                         set(joined['normal_completion_selection']))
        self.assertEqual(joined['normal_and_msrv'], {
            'frontend': 363, 'integration': 33, 'native': 23, 'cli_cases': 7,
            'companion': 176, 'ignored': 0, 'conditional_native_skips': 0})

    def test_registry_stops_and_protected_partial_result_never_become_full_success(self):
        for stage in ('registry-current-bounded', 'registry-current-bounded-v2',
                      'registry-current-bounded-purge', 'registry-current-bounded-no-header'):
            report = self.observation(stage)
            self.assertFalse(report['pass'])
            self.assertFalse(report['canonical_audit_checked'])
            self.assertEqual(report['changed_files'], [])
            self.assertEqual(report['exit_code'], -15)
            self.assertEqual(report['stop_reason'], 'owned-process-group-rss-limit')
            self.assertEqual(report['rss_group_limit_kib'], 2_097_152)
        authorization = json.loads(self.root_record('memory-preference-20261021.json'))
        self.assertEqual(authorization['reply'], '単独実行に限り3 GiBまで使う')
        self.assertEqual(authorization['heavy_jobs'], 1)
        for stage in ('registry-current-bounded-3g', 'kernel-tests-current-3g'):
            report = self.observation(stage)
            self.assertFalse(report['pass'])
            self.assertEqual(report['stop_reason'], 'owned-process-group-rss-limit')
            self.assertEqual(report['rss_group_limit_kib'], 3_145_728)
            self.assertEqual(report['heavy_job_concurrency'], 1)
        audit = self.observation('kernel-audit-current-isolation')
        self.assertTrue(audit['pass'])
        self.assertEqual(audit['exit_code'], 0)
        self.assertIn(b'Audited 16685 kernel/transport declarations',
                      self.data['kernel-audit-current-isolation/stdout'])
        protected = self.observation('protected-comparisons-v3')
        self.assertFalse(protected['pass'])
        rows = {row['name']: row for row in protected['commands']}
        self.assertEqual(set(rows), {'review', 'binding', 'basis', 'raw', 'extract', 'main-replay'})
        for name in ('review', 'binding', 'basis', 'raw', 'extract'):
            self.assertEqual(rows[name]['exit_code'], -15)
            self.assertEqual(rows[name]['stop_reason'], 'owned-process-group-rss-limit')
        replay = rows['main-replay']
        self.assertEqual(replay['exit_code'], 0)
        self.assertIsNone(replay['stop_reason'])
        self.assertTrue(replay['identical_recorded_output'])
        self.assertTrue(replay['source_and_kernel_window_unchanged'])
        self.assertEqual(replay['stdout_sha256'], hashlib.sha256(b'').hexdigest())
        self.assertEqual(replay['stderr_sha256'], hashlib.sha256(b'').hexdigest())

    def test_staged_runtime_uses_actual_four_tools_and_preserves_its_snapshots(self):
        window = self.observation('staged-runtime-window')
        runtime = self.observation('staged-runtime-current')
        self.assertTrue(window['pass'])
        self.assertEqual(window['exit_code'], 0)
        self.assertTrue(window['stable'])
        self.assertEqual(window['peak_rss_kib'], 90_352)
        self.assertTrue(runtime['pass'])
        self.assertEqual(runtime['exit_code'], 0)
        self.assertIsNone(runtime['exception'])
        self.assertEqual(runtime['before'], runtime['after'])
        self.assertTrue(all(runtime['checks'].values()))
        self.assertEqual(set(runtime['before']['staged_workspace_binaries']),
                         {'qargo', 'qlippy', 'qlifmt', 'qlidoc'})
        self.assertEqual(len(runtime['before']['four_preexisting_dirty_files']), 4)
        self.assertIn(b'no Cargo/Rustdoc invocation', self.data['staged-runtime-current/stdout'])
        self.assertEqual(self.data['staged-runtime-current/stderr'], b'')
        self.assertEqual(runtime['stdout']['sha256'],
                         hashlib.sha256(self.data['staged-runtime-current/stdout']).hexdigest())

    def test_deferred_header_and_prepared_refresh_plans_are_inert_records(self):
        deferred = json.loads(self.root_record('carrier-header-deferred.json'))
        candidate = self.root_record('carrier-header-candidate.lean.txt')
        self.assertEqual(deferred['candidate_sha256'], hashlib.sha256(candidate).hexdigest())
        self.assertNotEqual(deferred['candidate_sha256'], deferred['restored_sha256'])
        self.assertIn('Original header is retained', deferred['scope'])
        for version in ('v2', 'v3'):
            prepared = json.loads(self.root_record(
                'refresh-current-evidence-guarded-' + version + '.preparation.json'))
            self.assertIn('PREPARED ONLY', prepared['status'])
            self.assertFalse(prepared['root_edited'])
            script = self.root_record('refresh-current-evidence-guarded-' + version + '.py')
            self.assertEqual(prepared['sha256'], hashlib.sha256(script).hexdigest())

    def test_every_source_root_record_and_full_external_report_identity_is_preserved(self):
        originals = json.loads(self.data['original-external-records.json'])['records']
        for name, raw in self.data.items():
            if name.endswith('/original-source-records.json'):
                for original_name, row in json.loads(raw).items():
                    value = self.data[row['record']]
                    self.assertEqual((len(value), hashlib.sha256(value).hexdigest()),
                                     (row['bytes'], row['sha256']), original_name)
            if name.endswith('/observation.json'):
                stage = name.rsplit('/', 1)[0]
                held = json.loads(raw)
                original = originals[stage + '/report.json']
                self.assertEqual(held['full_local_report_bytes'], original['bytes'])
                self.assertEqual(held['full_local_report_sha256'], original['sha256'])
        for name in json.loads(self.data['root-capture-records.json'])['records']:
            self.root_record(name)
        validation = json.loads((FIXTURES / 'carrier-source-validation.json').read_bytes())
        self.assertEqual(validation['history']['records'], len(self.data))
        self.assertEqual(validation['history']['expanded_bytes'], 8269775)
        self.assertEqual(validation['history']['archive']['sha256'], '21df188096ceff6675f1377abad656cd2cf08379b40c70c252aa40ae5b86684a')
        self.assertEqual(validation['history']['index']['sha256'], '431ca032f33b9c2077e81f908943050508b3987306037577207e65cdcaa43acb')
        self.assertLessEqual(validation['history']['archive']['bytes'] +
            validation['history']['index']['bytes'] +
            (FIXTURES / 'carrier-source-validation.json').stat().st_size, 7_360_000)



class OrdinaryRuntimeFirstHistory(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history(
            'ordinary-runtime-index.json', 'ordinary-runtime-first.tar.xz',
            '458ea4695d8f9506ec9e2d7aef325a0e8224c98ec03c5245b867ca4d5b1bab58',
            581156, 'f8660884ef336f824e0c6b93600795e775304dc6636506585dab3aba14c8e2c7',
            3410855)
        cls.originals = json.loads(cls.data['original-records.json'])['records']
        cls.index = json.loads((FIXTURES / 'ordinary-runtime-index.json').read_bytes())

    def raw(self, name):
        row = self.originals[name]
        value = self.data[row['record']]
        self.assertEqual((len(value), hashlib.sha256(value).hexdigest()),
                         (row['bytes'], row['sha256']))
        return value

    def test_all_original_files_are_retained_losslessly_with_one_copy_per_object(self):
        self.assertEqual(len(self.data), 41)
        self.assertEqual(len(self.originals), 58)
        self.assertEqual(self.originals, self.index['original_records'])
        self.assertEqual(sum(row['bytes'] for row in self.originals.values()), 6721406)
        used = set()
        for name, row in self.originals.items():
            path = PurePosixPath(name)
            self.assertFalse(path.is_absolute())
            self.assertNotIn('..', path.parts)
            self.assertEqual(str(path), name)
            self.assertEqual(row['original_mode'], 0o644)
            self.assertEqual(row['record'], 'objects/' + row['sha256'])
            self.raw(name)
            used.add(row['record'])
        self.assertEqual(set(self.data), used | {'original-records.json'})
        self.assertEqual(len(used), 40)

    def test_original_predictions_and_all_fourteen_project_files_remain_frozen(self):
        original = self.raw('manifest.json')
        self.assertEqual(hashlib.sha256(original).hexdigest(),
                         '5bc7b8f56ccb6c1164bee1021401b7f15755fba7a7da6722883f9d638cbeff0c')
        manifest = json.loads(original)
        self.assertEqual(manifest['study_kind'], 'informed-study')
        self.assertEqual(len(manifest['cases']), 6)
        self.assertEqual(manifest['bounds']['max_live_qubits'], 1)
        self.assertEqual(len(manifest['records']), 14)
        for name, row in manifest['records'].items():
            raw = self.raw(name)
            self.assertEqual((len(raw), hashlib.sha256(raw).hexdigest()),
                             (row['bytes'], row['sha256']))
            if name.endswith('/Qargo.toml'):
                self.assertEqual(raw, b'schema-version = 2\n\n[qrate]\nedition = "2026"\n')
        self.assertEqual(self.raw('projects/foreign-enum-label/left.qli'),
                         self.raw('projects/foreign-enum-label/right.qli'))
        self.assertIn(b'fn missing', self.raw('projects/missing-and-duplicate-arms/main.qli'))
        self.assertIn(b'fn duplicate', self.raw('projects/missing-and-duplicate-arms/main.qli'))

    def test_every_actual_check_record_keeps_full_streams_and_first_barrier(self):
        report = json.loads(self.raw('observations-01/report.json'))
        self.assertTrue(report['complete'])
        self.assertTrue(report['stable'])
        self.assertEqual(len(report['commands']), 12)
        codes = []
        spans = {'enum-helper': (0, 20), 'record-zero-data': (0, 17),
                 'runtime-tri-match': (157, 158), 'missing-and-duplicate-arms': (70, 71),
                 'foreign-enum-label': (54, 55), 'quantum-match-unused': (59, 60)}
        for ordinal, row in enumerate(report['commands']):
            prefix = f"observations-01/{ordinal:02d}-{row['case']}-{row['route']}/"
            self.assertEqual(json.loads(self.raw(prefix + 'command.json')), row)
            self.assertEqual(row['argv'][1], 'check')
            self.assertEqual(row['exit_code'], 1)
            self.assertFalse(row['timed_out'])
            stdout, stderr = self.raw(prefix + 'stdout'), self.raw(prefix + 'stderr')
            self.assertEqual(hashlib.sha256(stdout).hexdigest(), row['stdout_sha256'])
            self.assertEqual(hashlib.sha256(stderr).hexdigest(), row['stderr_sha256'])
            self.assertEqual(stderr, b'')
            result = json.loads(stdout)
            self.assertEqual(result['command'], 'check')
            self.assertEqual(result['outcome'], 'error')
            self.assertIsNone(result['result'])
            self.assertEqual(len(result['diagnostics']), 1)
            diagnostic = result['diagnostics'][0]
            primary = diagnostic['primary']
            self.assertEqual((primary['start'], primary['end']), spans[row['case']])
            expected = 'unsupported' if ordinal < 4 else 'parse'
            self.assertEqual(diagnostic['code'], expected)
            self.assertEqual(diagnostic['message'],
                'finite type declarations require typed native transport before source execution'
                if expected == 'unsupported' else 'expected `}`, found identifier')
            codes.append(diagnostic['code'])
        self.assertEqual(codes.count('unsupported'), 4)
        self.assertEqual(codes.count('parse'), 8)

    def test_complete_original_windows_are_shared_without_inventory_compaction(self):
        before_raw = self.raw('observations-01/before.json')
        self.assertEqual(before_raw, self.raw('observations-01/after.json'))
        self.assertEqual(len(before_raw), 3327228)
        self.assertEqual(hashlib.sha256(before_raw).hexdigest(),
                         'f42b892f9ca52a30fcac1c85a8d6d9526eb39c119c5663748437fabfd8ac1527')
        before = json.loads(before_raw)
        self.assertEqual(len(before['root']), 20230)
        canonical = json.dumps(before['root'], sort_keys=True, separators=(',', ':'),
                               ensure_ascii=False).encode('utf-8')
        self.assertEqual(hashlib.sha256(canonical).hexdigest(),
                         '744b1f5a32762765faca58ff39fc529ef229516b3a57f17fc4587c0c221e7afb')
        for name, digest in before['study'].items():
            self.assertEqual(hashlib.sha256(self.raw(name)).hexdigest(), digest)
        self.assertEqual(before['manifest'], hashlib.sha256(self.raw('manifest.json')).hexdigest())
        self.assertEqual(self.originals['observations-01/before.json']['record'],
                         self.originals['observations-01/after.json']['record'])

    def test_inspection_preserves_unknown_native_invocation_and_semantic_limits(self):
        raw = self.raw('inspection-01.json')
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         '1d3d8f059255e8a849fb4f5fc33f9e9d9a0d1cb40d7723fed72b1d699a7e851e')
        inspection = json.loads(raw)
        self.assertEqual(inspection['summary']['check_commands'], 12)
        self.assertEqual(inspection['summary']['run_commands'], 0)
        self.assertEqual(inspection['summary']['unexpected_diagnostics'], [])
        self.assertIn('Unknown: no native invocation trace',
                      inspection['summary']['native_invocation'])
        context = json.loads(self.raw('observations-01/context.json'))
        self.assertIn('No native invocation trace is collected.', context['identity_limit'])
        self.assertIn('full original streams are not retained',
                      context['first_version_probe']['observation'])
        retention_raw = (FIXTURES / 'ordinary-runtime-retention.json').read_bytes()
        self.assertEqual((len(retention_raw), hashlib.sha256(retention_raw).hexdigest()),
                         (2646, '38ceb1dc5e98aec0203b70512a18bd1ba49e48d989e66ef81d7979eba51b00d7'))
        retention = json.loads(retention_raw)
        self.assertEqual(retention['format'], 'qleisli.inert-retention-proposal')
        self.assertIn('have not been performed by this proposal', retention['pending'])
        self.assertEqual(retention['original_files'], 58)
        self.assertEqual(retention['original_bytes'], 6721406)
        self.assertEqual(retention['archive']['sha256'],
                         'f8660884ef336f824e0c6b93600795e775304dc6636506585dab3aba14c8e2c7')


class OrdinaryMatchAuthoringHistory(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history(
            'ordinary-match-index.json', 'ordinary-match-first.tar.xz',
            '1d29c4ad0fd628787e6c721881c97fcefaee843c5a55bc27fdadb9341e82de30',
            1777180, 'ebb598f4e10b4a6f6fb5beb09f85ec0c3a91251e6208582a377a6441e2a7a2d5',
            99006698)
        cls.originals = json.loads(cls.data['original-records.json'])['records']
        cls.index = json.loads((FIXTURES / 'ordinary-match-index.json').read_bytes())
        raw = (FIXTURES / 'ordinary-match-validation.json').read_bytes()
        if (len(raw), hashlib.sha256(raw).hexdigest()) != (
                12589, '958858fd5c7869e173101aace182f1b3f14e1f654e6eacd7b5956bcddd779f55'):
            raise AssertionError('ordinary match retention proposal changed')
        cls.validation = json.loads(raw)

    def raw(self, name):
        row = self.originals[name]
        value = self.data[row['record']]
        self.assertEqual((len(value), hashlib.sha256(value).hexdigest()),
                         (row['bytes'], row['sha256']), name)
        return value

    def record(self, stage, name):
        return json.loads(self.raw(stage + '/' + name))

    def test_complete_original_inventory_and_whole_file_deduplication(self):
        self.assertEqual((len(self.data), len(self.originals)), (98, 294))
        self.assertEqual(self.originals, self.index['original_records'])
        self.assertEqual(sum(row['bytes'] for row in self.originals.values()), 109807776)
        used = set()
        for name, row in self.originals.items():
            path = PurePosixPath(name)
            self.assertFalse(path.is_absolute())
            self.assertNotIn('..', path.parts)
            self.assertEqual(str(path), name)
            self.assertEqual(row['original_mode'], 0o644)
            self.assertEqual(row['record'], 'objects/' + row['sha256'])
            self.raw(name)
            used.add(row['record'])
        self.assertEqual(set(self.data), used | {'original-records.json'})
        self.assertEqual(len(used), 97)

    def test_full_windows_bind_captured_sources_and_observers_without_execution(self):
        expected = [False, False, True, False, False, False, True, True, True, True]
        windows = self.validation['windows']
        self.assertEqual([row['pass'] for row in windows], expected)
        for summary in windows:
            stage = summary['window']
            report = self.record(stage, 'report.json')
            before = self.record(stage, 'before.json')
            plan = self.record(stage, 'plan.json')
            self.assertEqual(before, report['before'])
            self.assertEqual(before, report['after'])
            self.assertEqual(len(before['files']), 20237)
            self.assertEqual(before['kernel'],
                '6d4ccbaefa09985169acd12fe74fd6c2a1b5ad45b8dc389b68bdc66df510c57b')
            self.assertTrue(report['stable'])
            self.assertEqual(report['exit_code'], 0 if summary['pass'] else 101)
            self.assertEqual(report['pass'], summary['pass'])
            self.assertIsNone(report['stop_reason'])
            self.assertEqual(report['rss_group_limit_kib'], 3145728)
            self.assertEqual(report['heavy_job_concurrency'], 1)
            self.assertLessEqual(report['peak_rss_kib'], 3145728)
            self.assertEqual(plan['argv'], report['argv'])
            self.assertEqual(plan['environment'],
                {'CARGO_BUILD_JOBS': '1', 'RUST_TEST_THREADS': '1', 'LEAN_NUM_THREADS': '1'})
            for name in ('before', 'report'):
                raw = self.raw(stage + '/' + name + '.json')
                self.assertEqual(summary[name],
                    {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()})
            prefix = stage + '/sources/'
            captured = [name for name in self.originals if name.startswith(prefix)]
            self.assertGreaterEqual(len(captured), 18)
            for name in captured:
                self.assertEqual(hashlib.sha256(self.raw(name)).hexdigest(),
                                 before['files'][name[len(prefix):]], name)
            observer = ('run-bounded-runtime-3g.py' if before['explicit_inputs']
                        else 'run-bounded-rust185-integration-3g.py')
            self.assertEqual(self.raw(stage + '/observer.py.txt'), self.raw(observer))
            for name, digest in before['explicit_inputs'].items():
                held = self.raw(stage + '/explicit-inputs/' + PurePosixPath(name).name)
                self.assertEqual(hashlib.sha256(held).hexdigest(), digest)
                self.assertEqual(held, self.raw(PurePosixPath(name).name))

    def test_first_compile_and_three_frontend_test_failures_remain_failed(self):
        self.assertIn(b'no method named `try_node_id_expr`',
                      self.raw('ordinary-match-msrv-01/stderr'))
        self.assertNotIn(b'test result:', self.raw('ordinary-match-msrv-01/stdout'))
        out = self.raw('ordinary-match-msrv-02/stdout')
        for text in (b'371 passed; 3 failed', b'unresolved function init0',
                     b'`leaf::E` is not public', b'left: "name"', b'right: "effect"'):
            self.assertIn(text, out)
        first = self.raw('ordinary-match-msrv-01/sources/src/frontend/resolve/locals.rs')
        self.assertIn(b'try_node_id_expr', first)
        self.assertNotEqual(first,
            self.raw('ordinary-match-msrv-03/sources/src/frontend/resolve/locals.rs'))

    def test_three_integration_expectation_failures_are_not_successful_runs(self):
        first = self.raw('ordinary-match-integration-msrv-01/stdout')
        self.assertIn(b'40 passed; 1 failed', first)
        self.assertIn(b'error.message.contains("`match`")', first)
        second = self.raw('ordinary-match-integration-msrv-02/stdout')
        self.assertIn(b'41 passed; 0 failed', second)
        self.assertIn(b'5 passed; 1 failed', second)
        self.assertIn(b'called `Result::unwrap_err()` on an `Ok` value: Instantiation', second)
        third = self.raw('ordinary-match-integration-msrv-03/stdout')
        self.assertIn(b'5 passed; 1 failed', third)
        self.assertIn(b'left: "type_mismatch"', third)
        self.assertIn(b'right: "type"', third)
        self.assertIn(b'non-exhaustive match: missing variant B', third)

    def test_passing_scopes_preserve_filters_and_actual_driver_commands(self):
        self.assertIn(b'374 passed; 0 failed; 0 ignored; 0 measured; 147 filtered out',
                      self.raw('ordinary-match-msrv-03/stdout'))
        for stage in ('ordinary-match-integration-msrv-04', 'ordinary-match-stable-01'):
            out = self.raw(stage + '/stdout')
            self.assertIn(b'41 passed; 0 failed; 0 ignored', out)
            self.assertIn(b'6 passed; 0 failed; 0 ignored', out)
        self.assertIn(b'374 passed; 0 failed; 0 ignored; 0 measured; 147 filtered out',
                      self.raw('ordinary-match-stable-01/stdout'))
        lint = self.record('ordinary-match-msrv-clippy-01', 'report.json')['argv']
        self.assertEqual(lint[-7:], ['clippy', '--offline', '--locked', '--all-targets', '--', '-D', 'warnings'])
        self.assertEqual(self.raw('ordinary-match-msrv-clippy-01/stdout'), b'')
        driver = self.raw('run-ordinary-match-stable.py')
        self.assertEqual(hashlib.sha256(driver).hexdigest(),
                         '81449ee23dc66e1476dbd5f1c310edd677b25a33713a8407c8eb912c5e55c89f')
        self.assertIn(b'"build", "--offline", "--locked", "--bin", "qleisli"', driver)

    def test_twelve_current_cli_refusals_bind_the_unchanged_first_sources(self):
        stage = 'ordinary-match-current-cli-01'
        report = self.record(stage, 'report.json')
        self.assertTrue(report['stable'])
        self.assertTrue(report['passed'])
        self.assertEqual(report['before'], report['after'])
        self.assertEqual(report['before'], self.record(stage, 'before.json'))
        self.assertEqual(report['source_manifest_sha256'],
                         '5bc7b8f56ccb6c1164bee1021401b7f15755fba7a7da6722883f9d638cbeff0c')
        old = json.loads((FIXTURES / 'ordinary-runtime-index.json').read_bytes())['original_records']
        self.assertEqual(len(report['before']['sources']), 14)
        for name, digest in report['before']['sources'].items():
            self.assertEqual(digest, old[name]['sha256'])
        self.assertEqual(len(report['commands']), 12)
        for ordinal, row in enumerate(report['commands']):
            self.assertEqual(row['argv'][1], 'check')
            self.assertEqual(row['exit_code'], 1)
            self.assertTrue(row['passed'])
            prefix = f"{stage}/{ordinal:02d}-{row['case']}-{row['route']}"
            stdout, stderr = self.raw(prefix + '.stdout'), self.raw(prefix + '.stderr')
            self.assertEqual(hashlib.sha256(stdout).hexdigest(), row['stdout_sha256'])
            self.assertEqual(hashlib.sha256(stderr).hexdigest(), row['stderr_sha256'])
            self.assertEqual(stderr, b'')
            result = json.loads(stdout)
            self.assertEqual(result['outcome'], 'error')
            self.assertIsNone(result['result'])
            self.assertEqual(result['diagnostics'], [row['diagnostic']])
            code = 'unsupported' if ordinal < 6 else (
                'type_mismatch' if row['route'] == 'ordinary' else 'type')
            self.assertEqual(row['diagnostic']['code'], code)
        self.assertIn('missing variant C', report['commands'][6]['diagnostic']['message'])
        self.assertIn('expected `left::Tri`, found `right::Tri`',
                      report['commands'][8]['diagnostic']['message'])
        self.assertIn('ordinary match requires', report['commands'][10]['diagnostic']['message'])

    def test_original_packet_and_proposal_scope_remain_unchanged(self):
        for name, row in self.validation['unchanged_original_packet'].items():
            raw = (FIXTURES / name).read_bytes()
            self.assertEqual((len(raw), hashlib.sha256(raw).hexdigest()),
                             (row['bytes'], row['sha256']))
        self.assertEqual(self.validation['format'], 'qleisli.inert-retention-proposal')
        self.assertIn('PREPARED ONLY', self.validation['state'])
        self.assertIn('have not been performed by this proposal', self.validation['pending'])
        self.assertEqual(self.validation['inner_cli']['accepted_runtime_commands'], 0)
        self.assertEqual(self.validation['inner_cli']['run_commands'], 0)
        self.assertIn('No native invocation trace', self.validation['limits'][2])
        self.assertLessEqual(sum((FIXTURES / name).stat().st_size for name in (
            'ordinary-match-first.tar.xz', 'ordinary-match-index.json',
            'ordinary-match-validation.json')), 1_910_000)


class MatchKeywordRepairHistory(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history(
            'match-keyword-index.json', 'match-keyword-first.tar.xz',
            '57c544788ac8dc3d4c3156179707d1088201d4d16a91b1c095270e2aba424220', 1040248,
            '8d17c4e2ea2e3ff627319d7ba4da9a580cb7727360a85c10422675a68b60ca94', 51205220)
        cls.originals = json.loads(cls.data['original-records.json'])['records']
        cls.index = json.loads((FIXTURES / 'match-keyword-index.json').read_bytes())
        raw = (FIXTURES / 'match-keyword-validation.json').read_bytes()
        if (len(raw), hashlib.sha256(raw).hexdigest()) != (
                6089, '670b6922ab2df06767b041405859278e3e5246e0249c66a0d3484c2e6be232c5'):
            raise AssertionError('match keyword retention proposal changed')
        cls.validation = json.loads(raw)

    def raw(self, name):
        row = self.originals[name]
        value = self.data[row['record']]
        self.assertEqual((len(value), hashlib.sha256(value).hexdigest()),
                         (row['bytes'], row['sha256']), name)
        return value

    def record(self, stage, name):
        return json.loads(self.raw(stage + '/' + name))

    def test_complete_originals_and_whole_file_deduplication(self):
        self.assertEqual((len(self.originals), len(self.data)), (87, 66))
        self.assertEqual(self.originals, self.index['original_records'])
        self.assertEqual(sum(row['bytes'] for row in self.originals.values()), 51516603)
        used = set()
        for name, row in self.originals.items():
            path = PurePosixPath(name)
            self.assertFalse(path.is_absolute())
            self.assertNotIn('..', path.parts)
            self.assertEqual(str(path), name)
            self.assertEqual(row['original_mode'], 0o644)
            self.assertEqual(row['record'], 'objects/' + row['sha256'])
            self.raw(name)
            used.add(row['record'])
        self.assertEqual(len(used), 65)
        self.assertEqual(set(self.data), used | {'original-records.json'})

    def test_original_sources_and_predicted_inputs_remain_unmodified(self):
        first = self.record('prepared/first', 'expectations.json')
        self.assertEqual(first['status'], 'prepared-not-executed')
        self.assertEqual(len(first['cases']), 5)
        for row in first['cases']:
            self.assertIsNone(row['observed'])
            self.assertEqual(row['status'], 'prepared-not-executed')
        for name, digest in first['input_sha256'].items():
            self.assertEqual(hashlib.sha256(self.raw('prepared/first/' + name)).hexdigest(), digest)
        self.assertNotIn(b'deriving instance DecidableEq for Except',
                         self.raw('prepared/first/BeforeReaderAcceptance.lean'))
        self.assertIn(b'deriving instance DecidableEq for Except',
                      self.raw('prepared/BeforeReaderAcceptanceV2.lean'))

    def test_full_observation_windows_and_captured_sources(self):
        self.assertEqual([row['exit_code'] for row in self.validation['windows']], [1, 0, 101, 0, 0])
        self.assertEqual([row['reported_pass'] for row in self.validation['windows']],
                         [False, True, False, True, True])
        for summary in self.validation['windows']:
            name = summary['window']
            report = self.record(name, 'report.json')
            before = self.record(name, 'before.json')
            self.assertEqual(before, report['before'])
            self.assertEqual(report['before']['files'], report['after']['files'])
            self.assertEqual(report['before']['head'], report['after']['head'])
            self.assertTrue(report['stable'])
            self.assertIsNone(report['stop_reason'])
            self.assertEqual(report['exit_code'], summary['exit_code'])
            self.assertEqual(report['pass'], summary['reported_pass'])
            self.assertEqual(report['rss_group_limit_kib'], 3145728)
            self.assertEqual(report['heavy_job_concurrency'], 1)
            self.assertLessEqual(report['peak_rss_kib'], 3145728)
            self.assertEqual(self.record(name, 'plan.json')['argv'], report['argv'])
            if name == 'match-keyword-native-build-01':
                self.assertNotEqual(report['before']['kernel'], report['after']['kernel'])
                self.assertIn('fixed native build output only', report['kernel_change_scope'])
            else:
                self.assertEqual(report['before'], report['after'])
            for part in ('before', 'report'):
                raw = self.raw(name + '/' + part + '.json')
                self.assertEqual(summary[part],
                                 {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()})
            prefix = name + '/sources/'
            for source in self.originals:
                if source.startswith(prefix):
                    self.assertEqual(hashlib.sha256(self.raw(source)).hexdigest(),
                                     before['files'][source[len(prefix):]])
            for explicit, digest in before['explicit_inputs'].items():
                original = name + '/explicit-inputs/' + PurePosixPath(explicit).name
                self.assertEqual(hashlib.sha256(self.raw(original)).hexdigest(), digest)

    def test_failed_first_probe_and_successful_original_reader_are_distinct(self):
        failed = self.raw('match-keyword-original-reader-01/stdout')
        self.assertEqual(failed.count(b'failed to synthesize'), 3)
        self.assertNotIn(b'depends on axioms', failed)
        passed = self.raw('match-keyword-original-reader-02/stdout')
        for name in ('declaration', 'variant', 'field'):
            self.assertIn(("'reserved_" + name + "_accepted' depends on axioms: "
                           "[propext, Classical.choice, Quot.sound]").encode(), passed)
        self.assertNotIn(b'sorryAx', passed)
        self.assertNotIn(b'error:', passed)

    def test_actual_before_fix_handle_is_a_failed_negative(self):
        output = self.raw('match-keyword-original-native-01/stdout')
        for label in ('valid-enum', 'valid-field', 'reserved-declaration'):
            self.assertIn(('outcome ' + label + ' accepted').encode(), output)
        self.assertIn(b'called `Result::unwrap_err()` on an `Ok` value', output)
        self.assertIn(b'test result: FAILED. 0 passed; 1 failed; 0 ignored;', output)
        for label in ('reserved-variant', 'reserved-field'):
            self.assertNotIn(('outcome ' + label + ' ').encode(), output)

    def test_current_refusals_and_bounded_native_runs_are_actual_separate_results(self):
        report = self.record('current-01', 'report.json')
        self.assertTrue(report['pass'])
        self.assertEqual([row['name'] for row in report['commands']],
                         ['reader', 'audit', 'native', 'msrv'])
        self.assertEqual([row['exit_code'] for row in report['commands']], [0, 0, 0, 0])
        source = self.raw('current-inputs/CurrentReaderRefusals.lean')
        self.assertEqual(source.count(b'= .error .request := by decide +kernel'), 3)
        tests = self.raw('match-keyword-current-validation-01/sources/lean-kernel/Tests.lean')
        self.assertIn(source[source.index(b'-- Reserved words'):].rstrip(), tests)
        self.assertEqual(self.raw('current-01/reader.stdout'), b'')
        self.assertEqual(self.raw('current-01/audit.stderr'), b'')
        self.assertIn(b'Audited 16685 kernel/transport declarations', self.raw('current-01/audit.stdout'))
        self.assertNotIn(b'sorryAx', self.raw('current-01/audit.stdout'))
        for row in report['commands']:
            for name, digest in row['source_inputs'].items():
                if name.endswith('/CurrentReaderRefusals.lean'):
                    original = 'current-inputs/CurrentReaderRefusals.lean'
                else:
                    relative = name.split('/Qleisli/', 1)[1]
                    original = 'match-keyword-current-validation-01/sources/' + relative
                self.assertEqual(hashlib.sha256(self.raw(original)).hexdigest(), digest)
        for tool, count, filtered in (('native', 11, 511), ('msrv', 1, 521)):
            output = self.raw('current-01/' + tool + '.stdout')
            for label in ('valid-enum', 'valid-field'):
                self.assertIn(('outcome ' + label + ' accepted').encode(), output)
            for label in ('reserved-declaration', 'reserved-variant', 'reserved-field'):
                self.assertIn(('outcome ' + label + ' contract').encode(), output)
            self.assertIn((f'test result: ok. {count} passed; 0 failed; 0 ignored; '
                           f'0 measured; {filtered} filtered out;').encode(), output)
            self.assertIn(b'native test gate: zero conditional native skips', output)

    def test_proposal_scope_and_fixed_size_target(self):
        self.assertEqual(self.validation['format'], 'qleisli.inert-retention-proposal')
        self.assertIn('PREPARED ONLY', self.validation['state'])
        self.assertIn('have not been performed by this proposal', self.validation['pending'])
        self.assertIn('Full 479-case Lean suite', self.validation['limits'][3])
        self.assertIn('full proof-identity refresh', self.validation['limits'][3])
        self.assertLessEqual(sum((FIXTURES / name).stat().st_size for name in (
            'match-keyword-first.tar.xz', 'match-keyword-index.json',
            'match-keyword-validation.json')), 1572864)


class OrdinaryValueReferenceHistory(unittest.TestCase):
    """Read one bounded archive; saved code, paths and commands remain inert data."""

    STEM = 'ordinary-value-reference-'
    INDEX_SHA = '9e691dbce382e92ba1df58ab6532687f18fcaca6ac715bb4dc0451345598756a'
    ARCHIVE_SHA = 'ad3da88dbe714eedb4eec6d14d934d6e26de12251d07ce2e4933b37bae330557'
    VALIDATION_SHA = '89b2d632dc623e8ae3738b31a7ba17dfb33f558a5a79be6b91f785258d9960f3'
    # Historical strings are compared only, never resolved or opened.
    ACTUAL = '/private/tmp/qleisli-ordinary-value-validation-20261022-3rgzx7ko'
    TOOLCHAIN = '/Users/masa/.elan/toolchains/leanprover--lean4---v4.30.0/bin/'
    SOURCES = {
        'core': 'lean-kernel/QleisliKernel/Semantics/OrdinaryValue.lean',
        'bridge': 'lean/Qleisli/Semantics/OrdinaryValue.lean',
        'examples': 'tests/OrdinaryValueExamples.lean',
        'raw-examples': 'tests/OrdinaryValueRawExamples.lean',
        'audit': 'tests/OrdinaryValueAudit.lean',
    }
    WINDOWS = {
        '02-core': 1, '03-core': 1, '04-core': 0, '05-bridge': 1,
        '06-bridge': 0, '07-examples': 1, '09-examples': 0,
        '10-raw-examples': 0, '11-audit': 1, '12-core': 0,
        '13-bridge': 0, '14-examples': 0, '15-raw-examples': 0,
        '16-audit': 0, '17-fresh-audit': 0,
    }

    @staticmethod
    def pin(value):
        return {'bytes': len(value), 'sha256': hashlib.sha256(value).hexdigest()}

    @classmethod
    def setUpClass(cls):
        index = (FIXTURES / (cls.STEM + 'index.json')).read_bytes()
        validation = (FIXTURES / (cls.STEM + 'validation.json')).read_bytes()
        if cls.pin(index) != {'bytes': 108527, 'sha256': cls.INDEX_SHA}:
            raise AssertionError('ordinary value index changed')
        if cls.pin(validation) != {'bytes': 8385, 'sha256': cls.VALIDATION_SHA}:
            raise AssertionError('ordinary value summary changed')
        cls.index, cls.validation = json.loads(index), json.loads(validation)
        cls.originals = cls.index['original_records']
        cls.data = read_history(cls.STEM + 'index.json', cls.STEM + 'first.tar.xz',
                                cls.INDEX_SHA, 1521176, cls.ARCHIVE_SHA, 141896245)

    @classmethod
    def tearDownClass(cls):
        # The complete original inventories are large; do not retain a second
        # decoded copy or keep their byte objects after this class finishes.
        for name in ('data', 'originals', 'index', 'validation'):
            delattr(cls, name)

    def raw(self, name):
        row = self.originals[name]
        value = self.data[row['record']]
        self.assertEqual(self.pin(value), {key: row[key] for key in ('bytes', 'sha256')})
        return value

    def decoded(self, name):
        return json.loads(self.raw(name))

    def check_original_map(self, originals):
        self.assertEqual(len(originals), 289)
        self.assertEqual(sum(row['bytes'] for row in originals.values()), 156378431)
        self.assertEqual({row['record'] for row in originals.values()},
                         set(self.data) - {'original-records.json'})
        for name, row in originals.items():
            path = PurePosixPath(name)
            self.assertFalse(path.is_absolute())
            self.assertNotIn('..', path.parts)
            self.assertEqual(str(path), name)
            self.assertNotIn('/lib/', name)
            self.assertFalse(name.endswith(('.olean', '.ilean', '.pyc')))
            self.assertEqual(row['original_mode'], 0o644)
            self.assertEqual(row['record'], 'objects/' + row['sha256'])
            self.assertEqual(self.pin(self.data[row['record']]),
                             {key: row[key] for key in ('bytes', 'sha256')})
        mapped = json.loads(self.data['original-records.json'])
        self.assertEqual(mapped, {'format': 'qleisli.inert-original-records',
                                  'version': 1, 'records': originals})

    def check_sources(self, window, inputs):
        prefix = 'validation/' + window + '-sources/'
        expected = set(self.SOURCES.values())
        if int(window[:2]) < 11:
            expected.remove(self.SOURCES['audit'])
        self.assertEqual(set(inputs['sources']), expected)
        self.assertEqual({name[len(prefix):] for name in self.originals
                          if name.startswith(prefix) and name.endswith('.lean')}, expected)
        for name, pin in inputs['sources'].items():
            self.assertEqual(self.pin(self.raw(prefix + name)), pin)
        if int(window[:2]) >= 3:
            audit = int(window[:2]) >= 11
            manifest = 'namespace-cache-audit-pins.json' if audit else 'namespace-cache-pins.json'
            observer = 'attempt-v3.py' if audit else 'attempt-v2.py'
            self.assertEqual(self.raw(prefix + manifest), self.raw('validation/' + manifest))
            self.assertEqual(inputs['namespace_cache_pins'], self.pin(self.raw(prefix + manifest)))
            self.assertEqual(self.raw(prefix + observer), self.raw('validation/' + observer))

    def invocation(self, window):
        if window == '17-fresh-audit':
            return ([self.TOOLCHAIN + 'leanchecker', '--fresh', 'OrdinaryValueAudit'],
                    self.ACTUAL + '/work/tests', None)
        source = self.SOURCES[window.split('-', 1)[1]]
        root, module = source.split('/', 1)
        output = module.removesuffix('.lean') + '.olean'
        return ([self.TOOLCHAIN + 'lean', '-j1', '-DautoImplicit=false',
                 '-DwarningAsError=true', '-o', self.ACTUAL + '/lib/' + output,
                 self.ACTUAL + '/work/' + source], self.ACTUAL + '/work/' + root, source)

    def check_window(self, window, report=None, plan=None, inputs=None):
        prefix = 'validation/' + window
        if report is None:
            report = self.decoded(prefix + '/report.json')
        if plan is None:
            plan = self.decoded(prefix + '/plan.json')
        if inputs is None:
            inputs = self.decoded(prefix + '-sources/inputs.json')
        self.assertEqual((report['format'], report['version']),
                         ('qleisli.bounded-current-validation', 1))
        code = self.WINDOWS[window]
        self.assertIs(type(report['exit_code']), int)
        self.assertEqual(report['exit_code'], code)
        self.assertIs(report['pass'], code == 0)
        self.assertIs(report['stable'], True)
        self.assertIsNone(report['stop_reason'])
        before = report['before']
        self.assertTrue(before == self.decoded(prefix + '/before.json'), 'captured source inventory changed')
        self.assertTrue(before == report['after'], 'window source inventory changed')
        early = window in ('02-core', '03-core', '04-core')
        self.assertEqual(before['head'], '239e0546d24bfe952020a413fd24ae7f65a66d92' if early
                         else 'e936505ecc156d3cc31b8f5dffda780be7a1ef99')
        for name, digest in before['files'].items():
            path = PurePosixPath(name)
            self.assertFalse(path.is_absolute())
            self.assertNotIn('..', path.parts)
            self.assertEqual(str(path), name)
            self.assertRegex(digest, r'^[0-9a-f]{64}$')
        self.assertRegex(before['kernel'], r'^[0-9a-f]{64}$')
        argv, cwd, source = self.invocation(window)
        self.assertEqual(report['argv'], argv)
        self.assertEqual(report['cwd'], cwd)
        self.assertEqual(plan['argv'], argv)
        self.assertEqual(plan['cwd'], cwd)
        self.assertEqual(inputs['command'], argv)
        self.assertEqual(inputs['cwd'], cwd)
        live = self.decoded(prefix + '/live.json')
        self.assertEqual(live['argv'], argv)
        self.assertEqual(live['limit_seconds'], 600)
        self.assertEqual(plan['time_limit_seconds'], 600)
        self.assertEqual(inputs['timeout_seconds'], 600)
        for limit in (report['rss_group_limit_kib'], plan['rss_group_limit_kib'],
                      inputs['group_rss_limit_kib']):
            self.assertEqual(limit, 3145728)
        self.assertEqual(report['heavy_job_concurrency'], 1)
        self.assertEqual(inputs['heavy_concurrency'], 1)
        self.assertGreater(report['peak_rss_kib'], 0)
        self.assertLess(report['peak_rss_kib'], 3145728)
        self.assertGreater(report['seconds'], 0)
        self.assertLess(report['seconds'], 600)
        self.assertEqual(plan['environment'], {'CARGO_BUILD_JOBS': '1',
                                             'RUST_TEST_THREADS': '1', 'LEAN_NUM_THREADS': '1'})
        self.assertEqual(self.raw(prefix + '/observer.py.txt'),
                         self.raw('validation/run-bounded-runtime-3g.py'))
        self.check_sources(window, inputs)
        explicit = {} if source is None else {
            self.ACTUAL + '/work/' + source: inputs['sources'][source]['sha256']}
        self.assertEqual(before['explicit_inputs'], explicit)
        for absolute, digest in explicit.items():
            value = self.raw(prefix + '/explicit-inputs/' + PurePosixPath(absolute).name)
            self.assertEqual(self.pin(value)['sha256'], digest)
            self.assertEqual(value, self.raw(prefix + '-sources/' + source))
        for name in self.originals:
            if name.startswith(prefix + '/sources/'):
                relative = name[len(prefix + '/sources/'):]
                self.assertEqual(self.pin(self.raw(name))['sha256'], before['files'][relative])
        return dict(window=window, **{key: report[key] for key in (
            'exit_code', 'pass', 'stable', 'stop_reason', 'peak_rss_kib', 'seconds')},
            head_before=before['head'], head_after=report['after']['head'],
            report_record=prefix + '/report.json')

    def check_summary_order(self, rows):
        self.assertEqual([row['window'] for row in rows], ['01-core', *self.WINDOWS])
        self.assertEqual(rows[0], dict(window='01-core',
                                      result='No final report; 01 stopped before Lean spawn.', lean_result=None))

    def check_summary_row(self, row):
        window = row['window']
        self.assertIn(window, self.WINDOWS)
        record = 'validation/' + window + '/report.json'
        report = self.decoded(record)
        self.assertEqual(row, dict(window=window, **{key: report[key] for key in (
            'exit_code', 'pass', 'stable', 'stop_reason', 'peak_rss_kib', 'seconds')},
            head_before=report['before']['head'], head_after=report['after']['head'], report_record=record))

    def check_audit(self, audit, repaired):
        count = 284 if repaired else 301
        self.assertEqual((audit['format'], audit['version']),
                         ('qleisli.ordinary-value-candidate-audit', 1))
        rows = audit['declarations']
        self.assertEqual(audit['checked'], count)
        self.assertEqual(len(rows), count)
        self.assertEqual(len({row['name'] for row in rows}), count)
        self.assertEqual({row['module'] for row in rows}, {
            'QleisliKernel.Semantics.OrdinaryValue', 'Qleisli.Semantics.OrdinaryValue',
            'OrdinaryValueExamples', 'OrdinaryValueRawExamples'})
        self.assertEqual({axiom for row in rows for axiom in row['axioms']},
                         {'propext', 'Classical.choice', 'Quot.sound'})
        self.assertTrue(all(row['unsafe'] is False for row in rows))
        partial = {row['name'] for row in rows if row['partial']}
        expected = set() if repaired else {
            'QleisliKernel.Semantics.OrdinaryValue.littleEndian._unsafe_rec',
            'QleisliKernel.Semantics.OrdinaryValue.instReprValue.repr._unsafe_rec',
            'QleisliKernel.Semantics.OrdinaryValue.instReprStorage.repr._unsafe_rec'}
        self.assertEqual(partial, expected)
        self.assertEqual(audit['status'], 'pass' if repaired else 'fail')
        self.assertEqual(set(audit['failures']), {name + ': partial declaration' for name in expected})
        self.assertEqual(len(audit['failures']), len(expected))

    def check_fresh_inputs(self, fresh):
        final = self.decoded('validation/16-audit-sources/inputs.json')
        self.assertEqual(fresh['sources'], final['sources'])
        expected = dict(final['already_compiled_candidate_modules'])
        self.assertEqual(len(expected), 4)
        expected['lib/OrdinaryValueAudit.olean'] = {
            'bytes': 4992, 'sha256': '646ccca2865a41929fc10790b965001fe38ad2f6abd245153acf5f52c52eee3d'}
        self.assertEqual(fresh['already_compiled_candidate_modules'], expected)
        self.assertEqual(fresh['namespace_cache_pins'], final['namespace_cache_pins'])

    def test_complete_original_bytes_modes_and_map(self):
        self.assertEqual((self.index['format'], self.index['version']),
                         ('qleisli.inert-content-addressed-history', 1))
        self.assertEqual(len(self.data), 114)
        self.assertEqual(sum(map(len, self.data.values())), 141896245)
        self.check_original_map(self.originals)
        self.assertEqual({prefix: sum(name.startswith(prefix + '/') for name in self.originals)
                          for prefix in ('design', 'first', 'imports', 'validation')},
                         {'design': 1, 'first': 9, 'imports': 13, 'validation': 266})
        required17 = {'validation/17-fresh-audit/' + name for name in (
            'observer.py.txt', 'live.json', 'stderr', 'stdout', 'report.json', 'plan.json', 'before.json')}
        required17 |= {'validation/17-fresh-audit-sources/' + name for name in (
            *self.SOURCES.values(), 'attempt-v3.py', 'inputs.json', 'namespace-cache-audit-pins.json')}
        self.assertEqual({name for name in self.originals if name.startswith('validation/17-')}, required17)

    def test_uncompiled_first_sources_and_original_failed_observations(self):
        first = self.decoded('first/provenance.json')
        self.assertEqual(first['status'], 'uncompiled-candidate-only')
        for field in ('repository_modified_by_candidate', 'lean_cargo_build_or_axiom_audit_run',
                      'source_preservation_or_acceptance_claim'):
            self.assertIs(first[field], False)
        self.assertEqual(len(first['candidate_files']), 8)
        for name, pin in first['candidate_files'].items():
            self.assertEqual(self.pin(self.raw('first/' + name)), pin)
        closure = first['consulted_project_import_closure']
        self.assertEqual(len(closure), 13)
        self.assertEqual({'imports/' + name for name in closure},
                         {name for name in self.originals if name.startswith('imports/')})
        for name, pin in closure.items():
            self.assertEqual(self.pin(self.raw('imports/' + name)), pin)
        self.assertEqual(self.pin(self.raw('design/PROPOSAL.md')),
                         {key: first['base_proposal'][key] for key in ('bytes', 'sha256')})
        blocked = self.decoded('validation/BLOCKED.json')
        self.assertIs(blocked['attempt_01']['lean_spawned'], False)
        self.assertIs(blocked['attempt_01']['final_report_exists'], False)
        self.assertIs(blocked['attempt_02']['lean_spawned'], False)
        self.assertIs(blocked['attempt_02']['attempt_directory_exists'], False)
        self.assertIn('/bin/ps', blocked['attempt_01']['failure'])
        for name in ('report.json', 'live.json'):
            self.assertNotIn('validation/01-core/' + name, self.originals)
        for stream in ('stdout', 'stderr'):
            self.assertEqual(self.raw('validation/01-core/' + stream), b'')
        self.check_sources('01-core', self.decoded('validation/01-core-sources/inputs.json'))
        self.assertFalse(any(name.startswith('validation/08-') for name in self.originals))
        for window, text in (('02-core', 'FiniteCarrier.olean'), ('03-core', 'congrArg₂'),
                             ('05-bridge', 'Type mismatch'), ('07-examples', 'Dependent elimination failed')):
            self.assertIn(text.encode(), self.raw('validation/' + window + '/stdout'))

    def test_actual_windows_bind_source_inventories_invocations_and_summary(self):
        summaries = [dict(window='01-core', result='No final report; 01 stopped before Lean spawn.',
                          lean_result=None)]
        reports = {name.split('/')[1] for name in self.originals
                   if name.endswith('/report.json') and name.startswith('validation/')}
        self.assertEqual(reports, set(self.WINDOWS))
        for window in self.WINDOWS:
            with self.subTest(window=window):
                # Decode and discard one complete source inventory at a time.
                summaries.append(self.check_window(window))
        self.check_summary_order(self.validation['windows'])
        self.assertEqual(self.validation['windows'], summaries)

    def test_failed_and_repaired_audits_and_fresh_compiled_inputs(self):
        for window, repaired in (('11-audit', False), ('16-audit', True)):
            self.check_audit(json.loads(self.raw('validation/' + window + '/stdout').splitlines()[0]), repaired)
        self.check_fresh_inputs(self.decoded('validation/17-fresh-audit-sources/inputs.json'))
        for stream in ('stdout', 'stderr'):
            self.assertEqual(self.raw('validation/17-fresh-audit/' + stream), b'')
        final = self.decoded('validation/16-audit-sources/inputs.json')['sources']
        for name in self.SOURCES.values():
            self.assertEqual(self.pin(self.raw('validation/work/' + name)), final[name])
        # These are incoming identities, so the core/examples remain old until
        # their respective successful compile. Do not rewrite them as final.
        for earlier, later, module in (
                ('12-core', '13-bridge', 'lib/QleisliKernel/Semantics/OrdinaryValue.olean'),
                ('14-examples', '15-raw-examples', 'lib/OrdinaryValueExamples.olean')):
            before = self.decoded('validation/' + earlier + '-sources/inputs.json')
            after = self.decoded('validation/' + later + '-sources/inputs.json')
            self.assertNotEqual(before['already_compiled_candidate_modules'][module],
                                after['already_compiled_candidate_modules'][module])

    def test_import_cache_identities_preserve_source_closure_without_payloads(self):
        for name in ('namespace-cache-pins.json', 'namespace-cache-audit-pins.json'):
            manifest = self.decoded('validation/' + name)
            self.assertEqual((manifest['format'], manifest['version'], manifest['link_kind']),
                             ('qleisli.temporary-namespace-cache-overlay', 1, 'symlink'))
            cached = manifest['cached_modules']
            self.assertEqual(len(cached), 13)
            self.assertEqual({'imports/' + row['source'] for row in cached.values()},
                             {name for name in self.originals if name.startswith('imports/')})
            for module, row in cached.items():
                self.assertEqual(self.pin(self.raw('imports/' + row['source'])),
                                 {key: row[key] for key in ('bytes', 'sha256')})
                self.assertEqual(set(row['artifacts']),
                                 {module.replace('.', '/') + suffix for suffix in ('.olean', '.ilean')})
                for artifact, identity in row['artifacts'].items():
                    self.assertTrue(identity['target'].endswith('/' + artifact))
                    self.assertGreater(identity['bytes'], 0)
                    self.assertRegex(identity['sha256'], r'^[0-9a-f]{64}$')

    def test_fixed_summary_sizes_and_limited_scope(self):
        v = self.validation
        self.assertEqual((v['format'], v['version']), ('qleisli.inert-retention-proposal', 1))
        self.assertTrue(v['state'].startswith('PREPARED ONLY'))
        self.assertEqual((v['original_files'], v['original_bytes'], v['unique_objects'],
                          v['archive_members'], v['expanded_bytes']),
                         (289, 156378431, 113, 114, 141896245))
        self.assertEqual(v['index'], dict(path=self.STEM + 'index.json', bytes=108527, sha256=self.INDEX_SHA))
        self.assertEqual(v['archive'], dict(path=self.STEM + 'first.tar.xz', bytes=1521176, sha256=self.ARCHIVE_SHA))
        self.assertIs(v['fresh_audit_17_included'], True)
        self.assertEqual(v['target_combined_bytes'], 1258291)
        self.assertEqual(1521176 + 108527 + 8385, 1638088)  # Retained above the original target.
        self.assertEqual(v['compression']['dictionary_bytes'], 16777216)
        self.assertIn('No newly annotated phi output-tree correspondence', v['scope'])
        self.assertIn('typed native replay, original whole-AST preservation', v['limitations'][2])
        self.assertIn('No root adoption, acceptance path, new guarantee', v['limitations'][3])
        self.assertIn('not a fresh import-closure rebuild or binary/source attestation', v['identities'])

    def test_tampered_source_invocation_inventory_and_promoted_failure_are_rejected(self):
        window = '16-audit'
        inputs = self.decoded('validation/' + window + '-sources/inputs.json')
        inputs['sources'][self.SOURCES['core']] = self.decoded(
            'validation/03-core-sources/inputs.json')['sources'][self.SOURCES['core']]
        with self.assertRaises(AssertionError):
            self.check_sources(window, inputs)
        report = self.decoded('validation/' + window + '/report.json')
        plan = self.decoded('validation/' + window + '/plan.json')
        inputs = self.decoded('validation/' + window + '-sources/inputs.json')
        for record, key in ((report, 'argv'), (plan, 'argv'), (inputs, 'command')):
            record[key] = [self.TOOLCHAIN + 'leanchecker', 'Unrelated']
        with self.assertRaises(AssertionError):
            self.check_window(window, report, plan, inputs)
        report = self.decoded('validation/' + window + '/report.json')
        report['after']['files']['invented.lean'] = '0' * 64
        with self.assertRaises(AssertionError):
            self.check_window(window, report)
        report = self.decoded('validation/11-audit/report.json')
        report['exit_code'], report['pass'] = 0, True
        with self.assertRaises(AssertionError):
            self.check_window('11-audit', report)

    def test_tampered_audit_cache_and_original_metadata_are_rejected(self):
        audit = json.loads(self.raw('validation/16-audit/stdout').splitlines()[0])
        audit['declarations'].pop()
        audit['checked'] -= 1
        with self.assertRaises(AssertionError):
            self.check_audit(audit, True)
        audit = json.loads(self.raw('validation/16-audit/stdout').splitlines()[0])
        audit['declarations'][0]['axioms'].append('sorryAx')
        with self.assertRaises(AssertionError):
            self.check_audit(audit, True)
        fresh = self.decoded('validation/17-fresh-audit-sources/inputs.json')
        old = self.decoded('validation/12-core-sources/inputs.json')
        module = 'lib/QleisliKernel/Semantics/OrdinaryValue.olean'
        fresh['already_compiled_candidate_modules'][module] = old['already_compiled_candidate_modules'][module]
        with self.assertRaises(AssertionError):
            self.check_fresh_inputs(fresh)
        fresh = self.decoded('validation/17-fresh-audit-sources/inputs.json')
        del fresh['already_compiled_candidate_modules']['lib/OrdinaryValueAudit.olean']
        with self.assertRaises(AssertionError):
            self.check_fresh_inputs(fresh)
        name = 'first/provenance.json'
        for field, value in (('original_mode', 0o755), ('bytes', 0)):
            originals = dict(self.originals)
            originals[name] = dict(originals[name], **{field: value})
            with self.assertRaises(AssertionError):
                self.check_original_map(originals)
        originals = dict(self.originals)
        del originals[name]
        with self.assertRaises(AssertionError):
            self.check_original_map(originals)

    def test_promoted_summary_and_missing_window_are_rejected(self):
        failed = next(row for row in self.validation['windows'] if row['window'] == '11-audit')
        self.check_summary_row(failed)
        promoted = dict(failed, exit_code=0, **{'pass': True})
        with self.assertRaises(AssertionError):
            self.check_summary_row(promoted)
        altered = dict(failed, report_record='validation/16-audit/report.json')
        with self.assertRaises(AssertionError):
            self.check_summary_row(altered)
        missing = [row for row in self.validation['windows'] if row['window'] != '11-audit']
        with self.assertRaises(AssertionError):
            self.check_summary_order(missing)


# Focused history: "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-phi-effects-first.tar.xz"
# "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-phi-effects-index.json"
# "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-phi-effects-validation.json"
# Production history: "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-phi-effects-production-first.tar.xz"
# "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-phi-effects-production-index.json"
# "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-phi-effects-production-validation.json"


class _PhiEffectsHistory:
    """Passive original-byte checks; external report references are never opened."""
    HEAD = 'e4652ccaf001fd90cd53276165f0b78231e87c65'
    PHI = '/private/tmp/qleisli-ordinary-phi-validation-20261022-5ZSOXm'
    EFFECTS = '/private/tmp/qleisli-ordinary-effects-first-o5c7k82j'

    @staticmethod
    def pin(value):
        return {'bytes': len(value), 'sha256': hashlib.sha256(value).hexdigest()}

    @classmethod
    def setUpClass(cls):
        m = cls.META
        index = (FIXTURES / m['index']['path']).read_bytes()
        validation = (FIXTURES / m['validation']['path']).read_bytes()
        if cls.pin(index) != {k: m['index'][k] for k in ('bytes', 'sha256')} or cls.pin(validation) != {k: m['validation'][k] for k in ('bytes', 'sha256')}:
            raise AssertionError('focused history metadata changed')
        cls.index, cls.validation = json.loads(index), json.loads(validation)
        cls.originals = cls.index['original_records']
        cls.data = read_history(m['index']['path'], m['archive']['path'], m['index']['sha256'],
                                m['archive']['bytes'], m['archive']['sha256'], m['expanded_bytes'])

    @classmethod
    def tearDownClass(cls):
        for name in ('data', 'originals', 'index', 'validation'):
            delattr(cls, name)

    def raw(self, name):
        row = self.originals[name]
        value = self.data[row['record']]
        self.assertEqual(self.pin(value), {k: row[k] for k in ('bytes', 'sha256')})
        return value

    def decoded(self, name):
        return json.loads(self.raw(name))

    def test_original_map_and_external_scope(self):
        self.assertEqual(json.loads(self.data['original-records.json']),
                         {'format': 'qleisli.inert-original-records', 'version': 1, 'records': self.originals})
        self.assertEqual({row['record'] for row in self.originals.values()}, set(self.data) - {'original-records.json'})
        self.assertEqual(len(self.originals), self.validation['original_files'])
        self.assertEqual(sum(row['bytes'] for row in self.originals.values()), self.validation['original_bytes'])
        for name, row in self.originals.items():
            path = PurePosixPath(name)
            self.assertFalse(path.is_absolute())
            self.assertNotIn('..', path.parts)
            self.assertEqual(str(path), name)
            self.assertNotIn('lib', path.parts)
            self.assertFalse(name.endswith(('/before.json', '/report.json', '.olean', '.ilean', '.ir', '.pyc')))
            self.assertEqual(row['original_mode'], 0o644)
            self.assertEqual(row['record'], 'objects/' + row['sha256'])
            self.raw(name)
        self.assertEqual(self.validation['format'], 'qleisli.inert-retention-proposal')
        self.assertEqual(self.validation['version'], 1)
        self.assertEqual(self.validation['unique_objects'], len(self.data) - 1)
        self.assertEqual(self.validation['archive_members'], len(self.data))
        self.assertEqual(self.validation['expanded_bytes'], self.META['expanded_bytes'])
        self.assertEqual(self.validation['archive'], self.META['archive'])
        self.assertEqual(self.validation['index'], self.META['index'])
        self.assertIn('not an original report or self-contained verification', self.validation['windows'][0]['derivation'])
        for name, ref in self.validation['external_records'].items():
            self.assertNotIn(name, self.originals)
            self.assertTrue(name.endswith(('/before.json', '/report.json')))
            self.assertGreater(ref['bytes'], 0)
            self.assertRegex(ref['sha256'], r'^[0-9a-f]{64}$')

    def check_window(self, row, expected_exit):
        self.assertIs(type(row['exit_code']), int)
        self.assertEqual(row['exit_code'], expected_exit)
        self.assertIs(row['pass'], expected_exit == 0)
        self.assertIs(row['stable'], True)
        self.assertIs(row['full_window_equal'], True)  # Recorded derived field, not a fresh full-map check.
        self.assertIsNone(row['stop_reason'])
        self.assertEqual(row['before'], row['after'])
        self.assertEqual(row['before']['head'], self.HEAD)
        self.assertEqual((row['rss_group_limit_kib'], row['heavy_job_concurrency']), (3145728, 1))
        self.assertTrue(0 < row['peak_rss_kib'] <= 3145728)
        self.assertTrue(0 <= row['seconds'] < float('inf'))
        ref = self.validation['external_records'][row['prefix'] + '/report.json']
        self.assertEqual(row['report_reference'], {'path': ref['source'], **{k: ref[k] for k in ('bytes', 'sha256')}})
        before = self.validation['external_records'][row['prefix'] + '/before.json']
        self.assertEqual(row['before_reference'], {k: before[k] for k in ('source', 'bytes', 'sha256')})
        plan = self.decoded(row['prefix'] + '/plan.json')
        inputs = self.decoded(row['inputs_record'])
        argv = inputs['command'] if row['kind'] == 'phi' else inputs['argv']
        self.assertEqual(plan['argv'], argv)
        self.assertEqual(row['argv'], argv)
        self.assertEqual(row['cwd'], plan['cwd'])
        self.assertEqual(len(argv), 7)
        self.assertEqual(argv[:5], ['/Users/masa/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean',
                                    '-j1', '-DautoImplicit=false', '-DwarningAsError=true', '-o'])
        self.assertEqual((plan['time_limit_seconds'], plan['rss_group_limit_kib']), (600, 3145728))
        source = argv[-1]
        if row['kind'] == 'phi':
            self.assertEqual(inputs['cwd'], row['cwd'])
            relative = source.removeprefix(self.PHI + '/work/')
            for name, digest in inputs['sources'].items():
                self.assertEqual(self.pin(self.raw(row['source_prefix'] + name)), digest)
            source_bytes = self.raw(row['source_prefix'] + relative)
            cache_names = [name for name in self.originals if name.startswith(row['source_prefix'] + 'namespace-cache-')]
            self.assertEqual(len(cache_names), 1)
            self.assertEqual(self.pin(self.raw(cache_names[0])), inputs['namespace_cache_pins'])
            after = self.decoded(row['source_prefix'] + 'after.json')
            self.assertEqual(after['observer_exit'], expected_exit)
            self.assertIs(after['candidate_sources_stable'], True)
            self.assertIs(after['import_sources_and_cache_stable'], True)
            self.assertEqual(after['output'], argv[-2])
        elif row['kind'] == 'effects':
            source_bytes = self.raw(row['source_prefix'] + PurePosixPath(source).name)
            result = self.decoded(row['source_prefix'] + 'result.json')
            for key, value in inputs.items():
                self.assertEqual(result[key], value)
            self.assertEqual(inputs['source'], source)
            self.assertEqual(self.pin(source_bytes), inputs['source_pin'])
            self.assertEqual(result['exit_code'], expected_exit)
            self.assertIs(result['imports_stable'], True)
            self.assertIs(result['source_stable'], True)
            self.assertEqual(str(PurePosixPath(source).parent), row['cwd'])
            if row['window'] != 'effects-01-first':
                self.assertIs(result['prior_stages_stable'], True)
                self.assertEqual(self.pin(self.raw(row['source_prefix'] + 'run_stage.py')), inputs['driver'])
        else:
            self.assertEqual(inputs['cwd'], row['cwd'])
            source_bytes = self.raw(row['source_prefix'] + inputs['stage']['source'])
            for name, digest in inputs['candidate_sources'].items():
                self.assertEqual(self.pin(self.raw(row['source_prefix'] + name)), digest)
            self.assertEqual(inputs['namespace_cache_pin'], self.pin(self.raw('production/namespace-cache.json')))
        self.assertEqual(self.raw(row['prefix'] + '/stderr'), b'')
        self.assertEqual(row['before']['explicit_inputs'], {source: self.pin(source_bytes)['sha256']})
        self.assertEqual(source_bytes, self.raw(row['prefix'] + '/explicit-inputs/' + PurePosixPath(source).name))
        return inputs

    def check_audit(self, row, expected_format, modules, count):
        self.assertEqual(row['exit_code'], 0)
        self.assertIs(row['pass'], True)
        found = []
        for line in self.raw(row['prefix'] + '/stdout').decode().splitlines():
            try:
                item = json.loads(line)
            except ValueError:
                continue
            if isinstance(item, dict) and item.get('format') == expected_format:
                found.append(item)
        self.assertEqual(len(found), 1)
        audit = found[0]
        self.assertEqual((audit['version'], audit['status'], audit['failures']), (1, 'pass', []))
        rows = audit['declarations']
        self.assertEqual(audit['checked'], count)
        self.assertEqual(len(rows), count)
        self.assertEqual(len({r['name'] for r in rows}), count)
        self.assertEqual({r['module'] for r in rows}, set(modules))
        for record in rows:
            self.assertIs(record['unsafe'], False)
            self.assertIs(record['partial'], False)
            for override in ('csimp', 'extern', 'implemented_by'):
                if override in record:
                    self.assertIs(record[override], False)
            self.assertTrue(set(record['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'})
        return audit


class OrdinaryPhiEffectsHistory(_PhiEffectsHistory, unittest.TestCase):
    META = {'archive': {'bytes': 50068,
             'path': 'ordinary-phi-effects-first.tar.xz',
             'sha256': 'c7cbd2c6481875c78b553cfdda00e4d707fd61b4e62682329e0a3ceba27232ee'},
 'expanded_bytes': 580445,
 'index': {'bytes': 97039,
           'path': 'ordinary-phi-effects-index.json',
           'sha256': 'db9b41ad49de8d67e68c7354f6fc9ca4a9d62400bfa0b0bd25bea3e7d195fcde'},
 'validation': {'bytes': 39364,
                'path': 'ordinary-phi-effects-validation.json',
                'sha256': 'df9aaa32caf48acd4fc8974be949a540eb8f900d2bf68c1812936682f978f29b'}}
    OUTCOMES = [('02-core', 1), ('03-core', 1), ('04-core', 0), ('05-bridge', 1),
                ('06-bridge', 0), ('07-examples', 0), ('08-types', 0), ('09-audit', 0),
                ('effects-01-first', 0), ('effects-02-examples', 1), ('effects-03-examples', 0), ('effects-04-audit', 0)]

    def check_complete_input_maps(self, row, inputs, outputs):
        if row['kind'] == 'phi':
            prefix = row['source_prefix']
            expected = {name[len(prefix):] for name in self.originals
                        if name.startswith(prefix) and name.endswith('.lean')}
            self.assertEqual(set(inputs['sources']), expected)
            self.assertEqual({self.PHI + '/' + name: digest for name, digest in
                              inputs['already_compiled_candidate_modules'].items()}, outputs)
        else:
            expected = set()
            if row['window'] != 'effects-01-first':
                expected.update(['first/OrdinaryValueEffects.lean', '01-first/result.json',
                                 '01-first/lib/OrdinaryValueEffects.olean'])
            if row['window'] == 'effects-04-audit':
                expected.update(['source-controls-v2-pno0Zu/OrdinaryValueEffectsExamples.lean',
                                 '03-examples/result.json',
                                 '03-examples/lib/OrdinaryValueEffectsExamples.olean'])
            self.assertEqual(set(inputs.get('prior_stage_inputs', {})),
                             {self.EFFECTS + '/' + name for name in expected})

    def test_failed_and_passing_windows_keep_source_and_prior_output_bindings(self):
        rows = self.validation['windows']
        self.assertEqual([r['window'] for r in rows], [w for w, _ in self.OUTCOMES])
        outputs = {}
        for row, (_, code) in zip(rows, self.OUTCOMES):
            inputs = self.check_window(row, code)
            self.check_complete_input_maps(row, inputs, outputs)
            if row['kind'] == 'phi':
                for name, digest in inputs['already_compiled_candidate_modules'].items():
                    self.assertEqual(digest, outputs[self.PHI + '/' + name])
                after = self.decoded(row['source_prefix'] + 'after.json')
                if code == 0:
                    outputs[after['output']] = after['output_pin']
            else:
                result = self.decoded(row['source_prefix'] + 'result.json')
                for path, digest in inputs.get('prior_stage_inputs', {}).items():
                    if '/lib/' in path:
                        self.assertEqual(digest, outputs[path])
                    else:
                        self.assertEqual(digest, self.pin(self.raw('effects/' + path.removeprefix(self.EFFECTS + '/'))))
                if code == 0:
                    outputs[inputs['argv'][-2]] = result['output']
        self.check_audit(rows[7], 'qleisli.ordinary-value-phi-candidate-audit',
                         ['OrdinaryValuePhiExamples', 'OrdinaryValuePhiTypes', 'Qleisli.Semantics.OrdinaryValuePhi',
                          'QleisliKernel.Semantics.OrdinaryValueTransport'], 114)
        self.check_audit(rows[-1], 'qleisli.ordinary-value-effects-candidate-audit',
                         ['OrdinaryValueEffects', 'OrdinaryValueEffectsExamples'], 20)

    def test_pre_spawn_failure_is_not_the_later_real_second_attempt(self):
        blocked = self.decoded('phi-validation/BLOCKED.json')
        self.assertIs(blocked['attempt_01']['lean_spawned'], False)
        self.assertIs(blocked['attempt_01']['observer_report_exists'], False)
        self.assertIs(blocked['attempt_02']['attempt_directory_exists'], False)
        self.assertIn('aborted by user', blocked['attempt_02']['tool_result'])
        self.assertIn(b'/bin/ps', self.raw('phi-validation/01-driver.stderr'))
        self.assertEqual(self.raw('phi-validation/01-core/stdout'), b'')
        self.assertEqual(self.raw('phi-validation/01-core/stderr'), b'')
        self.assertNotIn('phi-validation/01-core/report.json', self.validation['external_records'])
        self.assertEqual(self.validation['windows'][0]['window'], '02-core')

    def test_changed_failure_and_source_commands_are_rejected(self):
        row = self.validation['windows'][3]
        with self.assertRaises(AssertionError):
            self.check_window(dict(row, exit_code=0, **{'pass': True}), 1)
        changed = dict(row, argv=[*row['argv'][:-1], row['argv'][-1] + '.changed'])
        with self.assertRaises(AssertionError):
            self.check_window(changed, 1)
        inputs = self.decoded(row['inputs_record'])
        outputs = {self.PHI + '/' + name: digest for name, digest in
                   inputs['already_compiled_candidate_modules'].items()}
        for field in ('sources', 'already_compiled_candidate_modules'):
            with self.assertRaises(AssertionError):
                self.check_complete_input_maps(row, dict(inputs, **{field: {}}), outputs)
        effects = self.validation['windows'][-2]
        inputs = self.decoded(effects['inputs_record'])
        with self.assertRaises(AssertionError):
            self.check_complete_input_maps(effects, dict(inputs, prior_stage_inputs={}), {})


class OrdinaryPhiEffectsProductionHistory(_PhiEffectsHistory, unittest.TestCase):
    META = {'archive': {'bytes': 52968,
             'path': 'ordinary-phi-effects-production-first.tar.xz',
             'sha256': '4c0970dc387323ff6fc08bec203c9b3a47b9fd8e26c007d06766d88b16dcf2ec'},
 'expanded_bytes': 558111,
 'index': {'bytes': 50141,
           'path': 'ordinary-phi-effects-production-index.json',
           'sha256': '5524ee6e225cc649cd9778b8c8f8408b8bea8c6d53cd9d0c2f2fc806a3e2eeb9'},
 'validation': {'bytes': 23267,
                'path': 'ordinary-phi-effects-production-validation.json',
                'sha256': 'befce7ce4644c5f367b1fa05a35b9c9892d86928679accb92ae7b43ed6fc1996'}}

    def test_seven_completed_canonical_stages_and_exact_audit_body(self):
        plan = self.decoded('production/plan.json')
        summary = self.decoded('production/summary.json')
        rows = self.validation['windows']
        self.assertEqual(len(plan['stages']), 7)
        self.assertEqual([r['window'] for r in rows], [s['label'] for s in plan['stages']])
        self.assertEqual(summary['status'], 'pass')
        self.assertEqual((summary['root_head'], plan['root_head']), (self.HEAD, self.HEAD))
        self.assertEqual((summary['group_rss_limit_kib'], summary['heavy_job_concurrency']), (3145728, 1))
        self.assertEqual([s['label'] for s in summary['stages']], [r['window'] for r in rows])
        self.assertIs(summary['candidate_sources_stable'], True)
        self.assertIs(summary['pinned_imports_and_tools_stable'], True)
        self.assertIs(summary['full_math_hosted_pending'], True)
        outputs = {}
        for row, stage, result in zip(rows, plan['stages'], summary['stages']):
            inputs = self.check_window(row, 0)
            self.assertEqual(inputs['stage'], stage)
            self.assertEqual(inputs['prior_fresh_modules'], outputs)
            self.assertEqual((result['observer_exit'], result['status'], result['stable']), (0, 'pass', True))
            self.assertEqual(result['report'], row['report_reference']['path'])
            self.assertEqual((result['seconds'], result['peak_rss_kib']), (row['seconds'], row['peak_rss_kib']))
            output_name = '/'.join(stage['module'].split('.')) + '.olean'
            self.assertEqual(summary['fresh_artifacts'][output_name], result['output'])
            outputs[output_name] = result['output']
        self.assertEqual(outputs, summary['fresh_artifacts'])
        original = self.raw('integration/lean/Audit.lean')
        focused = self.raw('production/sources/focused/Audit.lean')
        prefix = ''.join('import ' + m + '\n' for m in plan['audit_modules']).encode()
        self.assertTrue(original.startswith(b'import Qleisli\n'))
        self.assertEqual(focused, prefix + original[len(b'import Qleisli\n'):])
        manifest = self.decoded('integration/manifest.json')
        for name, digest in manifest['candidate_files'].items():
            self.assertEqual(self.pin(self.raw('production/sources/' + name)), digest)
        cache = self.decoded('production/namespace-cache.json')
        self.assertEqual((len(cache['cached_modules']), len(cache['direct_external_imports'])), (17, 11))
        audit = self.check_audit(rows[-1], 'qleisli.ordinary-value-audit', plan['audit_modules'], 417)
        self.assertEqual(audit, self.decoded('production/focused-audit-inventory.json'))
        self.assertEqual(summary['stages'][-1]['audited_declarations'], 417)

    def test_early_audit_json_cannot_promote_failed_whole_invocation(self):
        row = dict(self.validation['windows'][-1], exit_code=1, **{'pass': False})
        with self.assertRaises(AssertionError):
            self.check_audit(row, 'qleisli.ordinary-value-audit', [], 417)


# Inert member-authoring history; external full inventories remain referenced only.
# Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
# History: "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-members-first.tar.xz"
# Index: "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-members-index.json"
# Observations: "tests/fixtures/authoring_sessions/finite-adts-v030/ordinary-members-validation.json.gz"
class OrdinaryMemberHistory(unittest.TestCase):
    STEM = 'ordinary-members-'
    HEAD = 'e4652ccaf001fd90cd53276165f0b78231e87c65'
    AUTHORING = '/private/tmp/qleisli-ordinary-members-20261023-iCLsR0/'
    REPAIR = '/private/tmp/qleisli-member-v9-test-repair-sh_6y56k/'
    REPAIR2 = '/private/tmp/qleisli-member-v9-test-repair2-xnnp5kyx/'
    REPAIR3 = '/private/tmp/qleisli-member-v9-test-repair3-mlau62wy/'
    TOTALITY_REPAIR = '/private/tmp/qleisli-member-totality-repair-8d65tczl/'
    LEAN = '/Users/masa/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean'
    MEMBERS = 'QleisliKernel.SourceTypes.Members'
    TOTALITY_ORDER = ('QleisliKernel.SourceTypes.LocatedFacts', MEMBERS, 'MemberFullAudit')
    ORDER = (
        'CachedCompiledImports', 'QleisliKernel.SourceTypes.Lexer',
        'QleisliKernel.SourceTypes.Imports', 'QleisliKernel.SourceTypes.Declarations',
        'QleisliKernel.SourceTypes.NaturalSyntax', 'QleisliKernel.SourceTypes.NaturalHeaders',
        'QleisliKernel.SourceTypes.NaturalCatalog', 'QleisliKernel.SourceTypes.NaturalFrames',
        'QleisliKernel.SourceTypes.NaturalPrepare', 'QleisliKernel.SourceTypes.NaturalHelpers',
        'QleisliKernel.SourceTypes', 'Protocol.Carrier', 'Protocol.ExecutionView.CheckedCarrier',
        'Protocol.NativeContext', 'Cli.NativeContext', 'Protocol.NativeContext.Bindings',
        'Main', 'QleisliKernel', 'QleisliKernel.SourceTypes.LocatedFacts', MEMBERS,
        'QleisliKernel.SourceTypesLegacy.Lexer', 'QleisliKernel.SourceTypesLegacy.Imports',
        'QleisliKernel.SourceTypesLegacy.Declarations', 'MemberBoundaryProbes',
        'MemberLegacyComparison', 'MemberSmallExamples', 'MemberFullAudit', 'AllCompiledImports',
    )
    # Fixed history, not inferred from a success flag. The reported totality
    # pass is admitted only when its completed archived records also pass.
    RUNS = {'v5-full': (2, False), 'v6-full': (19, False), 'v7-full': (20, False),
            'v8-diagnostic': (1, False), 'v9-diagnostic': (1, True),
            'v9-full': (25, False), 'v9-tail': (1, False),
            'v9-tail2': (2, False), 'v9-tail3': (3, False), 'totality-core': (3, True)}
    DERIVED = ('Compact fields copied from externally pinned full reports and inputs; '
               'not an original report or self-contained verification of omitted '
               'root/source/artifact inventories.')
    META = {'archive_bytes': 249204,
     'archive_members': 509,
     'archive_sha256': '6cb34ee69a66e02236a29dfe1126acf3e0249050066e3d1a83b3dd91f6691f0c',
     'audit_marker': 'Audited 17252 kernel/transport declarations, 1163 pure import modules and 1210 '
                     'executable import modules, 1059 member-reader import modules; axioms used: '
                     '[propext,\n'
                     ' Classical.choice,\n'
                     ' Quot.sound]',
     'authoring_original_map_sha256': 'f828502e4e6eecee0704e5a99a2d4ead851c0c6aae84b0e981b4dc05c13622a5',
     'cached_compiled_report_sha256': '1a91cf179160f7ea8c086a62ea9766dd1e6ff804c8c5f7394c7c323e84feb17b',
     'expanded_bytes': 6104591,
     'external_records_sha256': 'f0186028c91347972bc026eda5ce5fd4ed8c1fec114bb0235232063d7e3422f8',
     'index_bytes': 329291,
     'index_sha256': '749f55f720f06a3b6b497ab91406f5fae06fccf94d09bb3bb1e96ec6199bd947',
     'original_bytes': 9311455,
     'original_files': 932,
     'original_map_sha256': '9242810ebcc8b663895297fa4d0b4bcbdfc1e1f9577e49bff41eb79f495205f0',
     'remaining_work': 1979563,
     'unique_objects': 508,
     'validation_bytes': 303775,
     'validation_gzip_bytes': 37714,
     'validation_gzip_sha256': '794addcd03982f4f27c01ccff50fd1657fd74e3b658463aafe3012e4e9572960',
     'validation_sha256': '89781be464f08953c4bc6ba23f2c4346734949e0b8f4e75dbb1b6e84521bac2b'}

    @staticmethod
    def pin(value):
        return {'bytes': len(value), 'sha256': hashlib.sha256(value).hexdigest()}

    @staticmethod
    def json_digest(value):
        return hashlib.sha256(json.dumps(value, sort_keys=True,
                                        separators=(',', ':')).encode()).hexdigest()

    @classmethod
    def setUpClass(cls):
        missing = [key for key, value in cls.META.items() if value is None]
        if missing:
            raise AssertionError('Fill completed-retention META first: ' + ', '.join(missing))
        index = (FIXTURES / (cls.STEM + 'index.json')).read_bytes()
        with (FIXTURES / (cls.STEM + 'validation.json.gz')).open('rb') as stream:
            compressed = stream.read(cls.META['validation_gzip_bytes'] + 1)
        if cls.pin(compressed) != {'bytes': cls.META['validation_gzip_bytes'],
                                   'sha256': cls.META['validation_gzip_sha256']}:
            raise AssertionError('ordinary member compressed validation changed')
        with gzip.GzipFile(fileobj=io.BytesIO(compressed), mode='rb') as stream:
            validation = stream.read(cls.META['validation_bytes'] + 1)
        for label, raw in (('index', index), ('validation', validation)):
            if cls.pin(raw) != {'bytes': cls.META[label + '_bytes'],
                                'sha256': cls.META[label + '_sha256']}:
                raise AssertionError('ordinary member ' + label + ' changed')
        cls.index, cls.validation = json.loads(index), json.loads(validation)
        cls.originals = cls.index['original_records']
        cls.data = read_history(cls.STEM + 'index.json', cls.STEM + 'first.tar.xz',
                                cls.META['index_sha256'], cls.META['archive_bytes'],
                                cls.META['archive_sha256'], cls.META['expanded_bytes'])

    @classmethod
    def tearDownClass(cls):
        for name in ('data', 'originals', 'index', 'validation'):
            if hasattr(cls, name):
                delattr(cls, name)

    def raw(self, name):
        row = self.originals[name]
        value = self.data[row['record']]
        self.assertEqual(self.pin(value), {key: row[key] for key in ('bytes', 'sha256')})
        return value

    def decoded(self, name):
        return json.loads(self.raw(name))

    def windows(self, run):
        return [row for row in self.validation['windows'] if row['run'] == run]

    def root_for(self, run):
        if run == 'totality-core':
            return '/private/tmp/qleisli-member-totality-diagnostic-first'
        if run == 'v9-tail3':
            return '/private/tmp/qleisli-member-v9-tail-validation-third'
        if run == 'v9-tail2':
            return '/private/tmp/qleisli-member-v9-tail-validation-second'
        version, kind = run.split('-', 1)
        suffix = 'diagnostic-first' if kind == 'diagnostic' else (
            'tail-validation-first' if kind == 'tail' else 'validation-first')
        return '/private/tmp/qleisli-member-' + version + '-' + suffix

    @staticmethod
    def is_tail(run):
        return run in ('v9-tail', 'v9-tail2', 'v9-tail3')

    def expected(self, run):
        count, passed = self.RUNS[run]
        if run == 'totality-core':
            return [(i, name, passed or j < count - 1)
                    for j, (i, name) in enumerate(zip(range(19, 19 + count), self.TOTALITY_ORDER))]
        names = [self.MEMBERS] if run.endswith('diagnostic') else list(
            self.ORDER[24:] if self.is_tail(run) else self.ORDER[:count])
        start = 25 if self.is_tail(run) else 1
        return [(i, name, passed or j < count - 1)
                for j, (i, name) in enumerate(zip(range(start, start + count), names))]

    def original_source_name(self, path):
        # String association only. Never resolve/open a historical path.
        if path.startswith(self.AUTHORING):
            return 'authoring/' + path[len(self.AUTHORING):]
        if path.startswith(self.REPAIR):
            return 'test-repair/' + path[len(self.REPAIR):]
        if path.startswith(self.REPAIR2):
            return 'test-repair2/' + path[len(self.REPAIR2):]
        if path.startswith(self.REPAIR3):
            return 'test-repair3/' + path[len(self.REPAIR3):]
        if path.startswith(self.TOTALITY_REPAIR):
            return 'totality-repair/' + path[len(self.TOTALITY_REPAIR):]
        return None

    def reference(self, name):
        self.assertNotIn(name, self.originals)
        row = self.validation['external_records'][name]
        self.assertEqual(set(row), {'source', 'bytes', 'sha256', 'original_mode'})
        self.assertIs(type(row['bytes']), int)
        self.assertGreaterEqual(row['bytes'], 0)
        self.assertRegex(row['sha256'], r'^[0-9a-f]{64}$')
        self.assertIs(type(row['original_mode']), int)
        self.assertTrue(PurePosixPath(row['source']).is_absolute())
        return row

    def check_outcome(self, window):
        expected = {index: (name, passed) for index, name, passed in self.expected(window['run'])}
        self.assertIn(window['index'], expected)
        name, passed = expected[window['index']]
        self.assertEqual(window['module'], name)
        self.assertIs(type(window['exit_code']), int)
        self.assertEqual(window['exit_code'], 0 if passed else 1)
        self.assertIs(window['pass'], passed)

    def check_window(self, window, plan=None):
        self.check_outcome(window)
        run, module, index = window['run'], window['module'], window['index']
        diagnostic = run.endswith('diagnostic')
        name = f'{index:02d}-' + module.replace('.', '-')
        prefix = run if diagnostic else run + '/' + name
        root = self.root_for(run)
        relative = module.replace('.', '/')
        source = root + '/src/' + relative + '.lean'
        argv = [self.LEAN, '-j1', '-DautoImplicit=false', '-DwarningAsError=true',
                '-o', root + '/lib/' + relative + '.olean', source]
        self.assertEqual((window['window'], window['prefix']), (name, prefix))
        self.assertEqual(window['kind'], 'diagnostic' if diagnostic else
                         'tail' if self.is_tail(run) else 'totality' if run == 'totality-core' else 'full')
        self.assertEqual(window['argv'], argv)
        self.assertEqual(window['cwd'], root + '/src')
        self.assertEqual(window['derivation'], self.DERIVED)
        self.assertIs(window['full_window_equal'], True)  # Recorded derived assertion only.
        self.assertIs(window['stable'], True)
        self.assertIsNone(window['stop_reason'])
        self.assertEqual((window['rss_group_limit_kib'], window['heavy_job_concurrency']), (3145728, 1))
        self.assertIs(type(window['peak_rss_kib']), int)
        self.assertGreater(window['peak_rss_kib'], 0)
        self.assertLessEqual(window['peak_rss_kib'], 3145728)
        self.assertIn(type(window['seconds']), (int, float))
        self.assertTrue(0 <= window['seconds'] < float('inf'))
        self.assertRegex(window['root_state_sha256'], r'^[0-9a-f]{64}$')
        self.assertEqual(window['plan_record'], prefix + '/monitor/plan.json')
        if plan is None:
            plan = self.decoded(window['plan_record'])
        self.assertEqual((plan['argv'], plan['cwd']), (argv, root + '/src'))
        self.assertEqual(plan['time_limit_seconds'], 900)
        self.assertEqual(plan['rss_group_limit_kib'], 3145728)
        self.assertEqual(window['source_record'], prefix + '/monitor/explicit-inputs/' + relative.split('/')[-1] + '.lean')
        raw = self.raw(window['source_record'])
        self.assertEqual(window['source_pin'], self.pin(raw))
        for state in (window['before'], window['after']):
            self.assertEqual(set(state), {'head', 'kernel', 'explicit_inputs'})
            self.assertEqual(state['head'], self.HEAD)
            self.assertRegex(state['kernel'], r'^[0-9a-f]{64}$')
            self.assertEqual(state['explicit_inputs'], {source: self.pin(raw)['sha256']})
        self.assertEqual(window['before'], window['after'])
        for field, suffix in (('report_reference', '/monitor/report.json'),
                              ('before_reference', '/monitor/before.json')):
            self.assertEqual(window[field], prefix + suffix)
            self.reference(window[field])
        manifest = self.decoded(run + '/input-manifest.json')
        self.assertEqual(manifest['head'], self.HEAD)
        self.assertEqual(self.raw(run + '/input-manifest.json'),
                         self.raw('runners/' + run + '/input-manifest.json'))
        if diagnostic:
            selected = manifest['source']
            self.assertEqual(window['inputs_record'], prefix + '/inputs.json')
            inputs = self.decoded(window['inputs_record'])
            self.assertEqual((inputs['argv'], inputs['cwd']), (argv, root + '/src'))
            self.assertEqual({k: inputs['source'][k] for k in ('bytes', 'sha256')}, self.pin(raw))
        else:
            self.assertEqual(window['inputs_reference'], prefix + '/inputs.json')
            self.reference(window['inputs_reference'])
            selected = (manifest['modules'][module]['source'] if module in manifest['modules']
                        else manifest['support_sources'][module])
            outputs = self.decoded(prefix + '/outputs.json')
            self.assertEqual({k: outputs['source_after'][k] for k in ('bytes', 'sha256')}, self.pin(raw))
            self.assertEqual(outputs['source_after']['path'], source)
        self.assertEqual({k: selected[k] for k in ('bytes', 'sha256')}, self.pin(raw))
        retained = self.original_source_name(selected['path'])
        if retained is not None:
            self.assertEqual(raw, self.raw(retained))
        elif module in ('CachedCompiledImports', 'AllCompiledImports'):
            self.assertEqual(raw, self.raw('runners/' + run + '/sources/' + module + '.lean'))
        observer = self.raw(prefix + '/monitor/observer.py.txt')
        self.assertEqual(self.pin(observer), {k: manifest['monitor'][k] for k in ('bytes', 'sha256')})
        result_name = prefix + '/result.json'
        if result_name in self.originals:
            result = self.decoded(result_name)
            self.assertIs(result['pass'], window['pass'])
            self.assertEqual(result['observer_exit_code'], 0 if window['pass'] else 1)
            if diagnostic:
                self.assertIs(result['inputs_stable'], True)
                self.assertEqual(result['report_pin']['sha256'], self.reference(window['report_reference'])['sha256'])
            else:
                self.assertEqual((result['index'], result['module']), (index, module))
                self.assertEqual(result['report_sha256'], self.reference(window['report_reference'])['sha256'])

    def check_failure_binding(self, failure, window, copies):
        self.assertIs(window['pass'], False)
        self.assertEqual(failure['fields'], {key: window[key] for key in
                         ('exit_code', 'pass', 'stable', 'stop_reason', 'seconds', 'peak_rss_kib')})
        records = failure['records']
        self.assertEqual([PurePosixPath(pin['path']).name for pin in records],
                         ['report.json', 'plan.json', 'stdout', 'stderr'])
        for pin in records:
            basename = PurePosixPath(pin['path']).name
            record = window['prefix'] + '/monitor/' + basename
            source = self.root_for(window['run']) + '/' + window['window'] + '/monitor/' + basename
            self.assertEqual((pin['path'], pin['resolved'], pin['link']), (source, source, None))
            retained = self.reference(record) if basename == 'report.json' else self.originals[record]
            self.assertEqual({key: pin[key] for key in ('bytes', 'sha256')},
                             {key: retained[key] for key in ('bytes', 'sha256')})
            self.assertEqual(pin['mode'], retained['original_mode'])
        for stream in ('stdout', 'stderr'):
            self.assertEqual(self.raw(copies + stream + '.txt'),
                             self.raw(window['prefix'] + '/monitor/' + stream))

    def test_complete_original_bytes_modes_map_and_scope(self):
        self.assertEqual((self.index['format'], self.index['version']), ('qleisli.inert-content-addressed-history', 1))
        self.assertEqual(len(self.data), self.META['archive_members'])
        self.assertEqual(sum(map(len, self.data.values())), self.META['expanded_bytes'])
        self.assertEqual(len(self.originals), self.META['original_files'])
        self.assertEqual(sum(row['bytes'] for row in self.originals.values()), self.META['original_bytes'])
        self.assertEqual(self.json_digest(self.originals), self.META['original_map_sha256'])
        authoring = {name: {k: row[k] for k in ('bytes', 'sha256', 'original_mode')}
                     for name, row in self.originals.items() if name.startswith('authoring/')}
        self.assertEqual(self.json_digest(authoring), self.META['authoring_original_map_sha256'])
        self.assertEqual({row['record'] for row in self.originals.values()}, set(self.data) - {'original-records.json'})
        self.assertEqual(len(self.data) - 1, self.META['unique_objects'])
        self.assertEqual(json.loads(self.data['original-records.json']),
                         {'format': 'qleisli.inert-original-records', 'version': 1, 'records': self.originals})
        for name, row in self.originals.items():
            path = PurePosixPath(name)
            self.assertFalse(path.is_absolute())
            self.assertNotIn('..', path.parts)
            self.assertEqual(str(path), name)
            self.assertFalse(name.endswith(('.olean', '.olean.server', '.olean.private', '.ilean', '.ir', '.pyc')))
            self.assertIs(type(row['original_mode']), int)
            self.assertGreaterEqual(row['original_mode'], 0)
            self.assertLessEqual(row['original_mode'], 0o777)
            self.assertEqual(row['record'], 'objects/' + row['sha256'])
            self.raw(name)
        v = self.validation
        self.assertEqual((v['format'], v['version'], v['packet']), ('qleisli.inert-retention-proposal', 1, 'history'))
        for field in ('original_files', 'original_bytes', 'unique_objects', 'archive_members', 'expanded_bytes'):
            self.assertEqual(v[field], self.META[field])
        for field, suffix in (('index', 'index.json'), ('archive', 'first.tar.xz')):
            self.assertEqual(v[field], {'path': self.STEM + suffix, 'bytes': self.META[field + '_bytes'],
                                        'sha256': self.META[field + '_sha256']})
        self.assertEqual(self.json_digest(v['external_records']), self.META['external_records_sha256'])
        for name in v['external_records']:
            self.reference(name)
        self.assertEqual(v['state'], 'Retained historical observations; not current proof validity or full source-window replay.')
        self.assertEqual(v['limitations'], [
            'Full original before/report inventories are unchanged external records, not archived members.',
            'Compact window fields are explicitly derived and cannot independently recheck the omitted root inventories.',
            'Cached/generated binary payloads are omitted; their recorded identities do not attest a fresh import rebuild.',
            'No saved command is executed, no source preservation or new acceptance/guarantee/Issue completion is claimed.'])

    def test_first_uncompiled_provenance_candidates_and_totality_only_repair(self):
        first = self.decoded('authoring/first-provenance.json')
        self.assertEqual(first['status'], 'uncompiled-source-review-candidate')
        self.assertEqual(first['executed_commands'], [])
        self.assertEqual(first['source_commit'], self.HEAD)
        self.assertEqual(len(first['files']), 11)
        for version in range(1, 10):
            provenance = first if version == 1 else self.decoded(f'authoring/candidate-v{version}-provenance.json')
            self.assertEqual(provenance['source_commit'], self.HEAD)
            self.assertIn('uncompiled', provenance['status'].lower())
            for name, pin in provenance['files'].items():
                self.assertEqual(self.pin(self.raw('authoring/' + name)), {k: pin[k] for k in ('bytes', 'sha256')})
            candidate = 'first-candidate' if version == 1 else f'candidate-v{version}'
            self.raw('authoring/' + candidate + '/lean-kernel/QleisliKernel/SourceTypes/Members.lean')
        patch = first['integration_patch']
        self.assertEqual(self.pin(self.raw('authoring/' + patch['path'])), {k: patch[k] for k in ('bytes', 'sha256')})
        self.assertEqual({name.rsplit('/', 1)[-1] for name in self.originals if name.startswith('authoring/first-sources/')},
                         {'client.qli', 'comments.qli', 'duplicate.qli', 'facade.qli', 'nested.qli', 'owner.qli', 'unsupported-header.qli'})
        owner = self.raw('authoring/first-sources/owner.qli')
        self.assertIn(b'\r\n', owner)
        self.assertIn('日本語'.encode(), owner)
        self.assertIn(b'r.hidden', self.raw('authoring/first-sources/client.qli'))
        self.assertIn(b'client.bad is intentionally unauthorized', self.raw('authoring/FIRST-CONTRACT.md'))
        totality = self.decoded('totality-repair/provenance.json')
        self.assertEqual((totality['format'], totality['version'], totality['status'], totality['source_commit']),
                         ('qleisli.member-checkOrdered-totality-repair', 1,
                          'uncompiled executable totality repair', self.HEAD))
        self.assertEqual(totality['previous_candidate'], self.AUTHORING + 'candidate-v9')
        base = 'lean-kernel/QleisliKernel/SourceTypes/'
        self.assertEqual(set(totality['files']), {base + name + '.lean' for name in
                                               ('Lexer', 'Declarations', 'LocatedFacts', 'Members')})
        self.assertEqual(totality['changed'], [base + 'LocatedFacts.lean'])
        old_definition = '''def checkOrdered (bytes : ByteArray) (lower : Nat) : List LocatedToken → Bool
  | [] => true
  | token :: tokens =>
    decide (lower ≤ token.span.startByte ∧ TokenBytes bytes token) &&
      checkOrdered bytes token.span.endByte tokens'''.encode()
        new_definition = '''def checkOrdered (bytes : ByteArray) (lower : Nat) (tokens : List LocatedToken) : Bool :=
  (tokens.foldr (fun token next lower =>
    decide (lower ≤ token.span.startByte ∧ TokenBytes bytes token) &&
      next token.span.endByte) (fun _ => true)) lower'''.encode()
        for name, pin in totality['files'].items():
            old = self.raw('authoring/candidate-v9/' + name)
            retained = 'totality-repair/candidate/' + name
            new = self.raw(retained)
            source = self.TOTALITY_REPAIR + 'candidate/' + name
            self.assertEqual((pin['path'], pin['resolved'], pin['link']), (source, source, None))
            self.assertEqual({key: pin[key] for key in ('bytes', 'sha256')}, self.pin(new))
            self.assertEqual(pin['mode'], self.originals[retained]['original_mode'])
            if name.endswith('/LocatedFacts.lean'):
                self.assertEqual(old.count(old_definition), 1)
                self.assertEqual(new, old.replace(old_definition, new_definition, 1))
                self.assertEqual(new, self.raw('totality-core/19-QleisliKernel-SourceTypes-LocatedFacts/monitor/explicit-inputs/LocatedFacts.lean'))
            else:
                self.assertEqual(new, old)
        delta = self.raw('totality-repair/delta.patch')
        self.assertTrue(delta.startswith(('--- ' + self.AUTHORING + 'candidate-v9/' + base + 'LocatedFacts.lean\n+++ ' +
                                         self.TOTALITY_REPAIR + 'candidate/' + base + 'LocatedFacts.lean\n').encode()))
        self.assertIn(b'+  (tokens.foldr (fun token next lower =>', delta)
        self.assertIn(b' theorem checkOrdered_sound ', delta)
        self.check_failure_binding(totality['failure'], self.windows('v9-tail3')[-1],
                                   'totality-repair/tail3-audit-failure-')
        failure = self.raw('totality-repair/tail3-audit-failure-stdout.txt')
        self.assertIn(b'LocatedFacts.checkOrdered._unsafe_rec', failure)
        self.assertIn(b'partial project declaration', failure)

    def test_exact_run_outcomes_and_cumulative_fresh_output_fingerprints(self):
        self.assertEqual(self.validation['expected_stage_order'], list(self.ORDER))
        self.assertIs(self.validation['final_full_window_included'], True)
        self.assertIs(self.validation['tail_window_included'], True)
        self.assertIs(self.validation['tail2_window_included'], True)
        self.assertIs(self.validation['tail3_window_included'], True)
        self.assertIs(self.validation['core_window_included'], True)
        self.assertEqual([row['run'] for row in self.validation['runs']], list(self.RUNS))
        self.assertEqual(len(self.validation['windows']), 77)
        for run, (count, passed) in self.RUNS.items():
            windows = self.windows(run)
            self.assertEqual([(w['index'], w['module'], w['pass']) for w in windows], self.expected(run))
            summary_name = run + ('/result.json' if run.endswith('diagnostic') else '/report.json')
            summary = self.decoded(summary_name)
            self.assertIs(summary['pass'], passed)
            scope = 'diagnostic-only' if run.endswith('diagnostic') else (
                'four-stage-tail-after-prefix24' if self.is_tail(run) else
                'three-stage-totality-diagnostic-after-prefix18' if run == 'totality-core' else
                'fresh-full28-attempt')
            row = next(r for r in self.validation['runs'] if r['run'] == run)
            self.assertEqual(row, {'run': run, 'scope': scope, 'summary_record': summary_name,
                                  'pass': passed, 'observed_stage_count': count,
                                  'module_order': [w['module'] for w in windows],
                                  'manifest_record': run + '/input-manifest.json', 'final_full28_pass': False})
            if run.endswith('diagnostic'):
                self.assertEqual(summary['scope'], 'single-module diagnostic only; no full28 pass')
            else:
                self.assertEqual(summary['status'], 'bounded-diagnostic-pass' if passed else 'failed')
                self.assertEqual([(r['index'], r['module'], r['pass']) for r in summary['stages']], self.expected(run))
                if passed:
                    self.assertEqual((summary['completed_stages'], summary['planned_stages']), (3, 3))
                    self.assertEqual(summary['scope'], 'three-stage totality diagnostic after separately pinned18-stage unaffected prefix; no full28 or example pass')
                else:
                    self.assertEqual(summary['stages'][-1]['status'], 'failed')
            prior = {}
            for window in windows:
                self.check_outcome(window)
                self.assertNotIn('prior_fresh_outputs', window)
                self.assertEqual(window['prior_fresh_output_count'], len(prior))
                self.assertEqual(window['prior_fresh_outputs_sha256'], self.json_digest(prior))
                if not run.endswith('diagnostic') and window['pass']:
                    outputs = self.decoded(window['prefix'] + '/outputs.json')['artifacts']
                    self.assertTrue(outputs)
                    self.assertFalse(set(prior) & set(outputs))
                    for pin in outputs.values():
                        self.assertIsNone(pin['link'])
                    prior.update(outputs)
            self.assertEqual(len({w['root_state_sha256'] for w in windows}), 1)

    def test_source_command_plan_result_bindings(self):
        for window in self.validation['windows']:
            with self.subTest(run=window['run'], index=window['index']):
                self.check_window(window)

    def test_failed_windows_cannot_be_promoted_or_redirected(self):
        for run in ('v5-full', 'v6-full', 'v7-full', 'v8-diagnostic', 'v9-full', 'v9-tail', 'v9-tail2', 'v9-tail3'):
            promoted = dict(self.windows(run)[-1], exit_code=0, **{'pass': True})
            with self.assertRaises(AssertionError):
                self.check_outcome(promoted)
        changed = json.loads(json.dumps(self.windows('totality-core')[-1]))
        plan = self.decoded(changed['plan_record'])
        changed['argv'][-1] = plan['argv'][-1] = changed['argv'][-1].replace('MemberFullAudit', 'CachedCompiledImports')
        with self.assertRaises(AssertionError):
            self.check_window(changed, plan)

    def test_reused_prefix_and_cached_artifact_fingerprints(self):
        for run in self.RUNS:
            m = self.decoded(run + '/input-manifest.json')
            seeded = self.is_tail(run) or run == 'totality-core'
            if seeded:
                count = 18 if run == 'totality-core' else 24
                prefix = self.windows('v9-full')[:count]
                seeds = {w['module']: self.decoded(w['prefix'] + '/outputs.json')['artifacts'] for w in prefix}
                self.assertEqual(list(seeds), list(self.ORDER[:count]))
                captured_sources = {p['path']: p for w in prefix for p in
                                    [self.decoded(w['prefix'] + '/outputs.json')['source_after']]}
                self.assertEqual(m['seed_artifacts'], seeds)
                self.assertEqual({p['path']: p for p in m['seed_source_pins']}, captured_sources)
                self.assertEqual(m['seed_root_state_sha256'], prefix[0]['root_state_sha256'])
                if run == 'totality-core':
                    self.assertEqual(m['diagnostic_order'], list(self.TOTALITY_ORDER))
                    self.assertNotIn('tail_order', m)
                else:
                    self.assertEqual(m['tail_order'], list(self.ORDER[24:]))
            if run.endswith('diagnostic'):
                cached = self.decoded(run + '/inputs.json')['artifacts']
            else:
                cached = {}
                originals = [(module.replace('.', '/') + pin['suffix'], pin)
                             for module in m['cached_order'] for pin in m['modules'][module]['cache']]
                if seeded:
                    originals += [(rel, pin) for artifacts in m['seed_artifacts'].values() for rel, pin in artifacts.items()]
                for rel, pin in originals:
                    cached[rel] = {'path': self.root_for(run) + '/lib/' + rel, 'resolved': pin['resolved'],
                                   'link': pin['path'], **{k: pin[k] for k in ('bytes', 'mode', 'sha256')}}
            self.assertTrue(all(pin['link'] is not None for pin in cached.values()))
            for window in self.windows(run):
                self.assertEqual(window['cached_artifact_count'], len(cached))
                self.assertEqual(window['cached_artifacts_sha256'], self.json_digest(cached))
                if seeded:
                    self.assertEqual(window['root_state_sha256'], m['seed_root_state_sha256'])

    def test_cached_import_inventory_totality_audit_and_historical_probes(self):
        cached = self.windows('v9-full')[0]
        self.check_outcome(cached)
        report = self.decoded(cached['prefix'] + '/compiled-imports.json')
        self.assertEqual(self.json_digest(report), self.META['cached_compiled_report_sha256'])
        self.assertEqual((report['format'], report['status']), ('qleisli.member-v9-exact-compiled-imports', 'pass'))
        manifest = self.decoded('v9-full/input-manifest.json')
        self.assertEqual((len(manifest['fresh_order']), len(manifest['cached_order']), len(manifest['test_order'])), (19, 168, 6))
        self.assertEqual([r['module'] for r in report['modules']], manifest['cached_order'])
        self.assertEqual(len(report['modules']), 168)
        self.assertFalse(any(w['module'] == 'AllCompiledImports' for w in self.validation['windows']))
        self.assertEqual(len(set(report['loaded_modules'])), len(report['loaded_modules']))
        for row in report['modules']:
            self.assertEqual(row['source'], row['module'].replace('.', '/') + '.lean')
            self.assertIs(type(row['is_module']), bool)
            self.assertIn(row['module'], report['loaded_modules'])
            for imported in row['imports']:
                for flag in ('exported', 'meta', 'all'):
                    self.assertIs(type(imported[flag]), bool)
        for module in report['loaded_modules']:
            self.assertTrue(module in manifest['cached_order'] or module.split('.')[0] in ('Init', 'Std', 'Lean'))
        emitted = [json.loads(line) for line in self.raw(cached['prefix'] + '/monitor/stdout').splitlines()
                   if line.startswith(b'{')]
        self.assertEqual([r for r in emitted if r.get('format') == report['format']], [report])
        self.check_outcome(self.windows('totality-core')[-1])
        audit = self.raw('totality-core/21-MemberFullAudit/monitor/stdout').decode()
        marker = self.META['audit_marker']
        self.assertTrue(marker.startswith('Audited ') and 'member-reader import modules; axioms used:' in marker)
        self.assertEqual(audit.count(marker), 1)
        self.assertEqual(audit.count('Audited '), 1)
        axioms = marker.split('axioms used:', 1)[1]
        self.assertEqual(axioms.replace('[', '').replace(']', '').replace(',', ' ').split(),
                         ['propext', 'Classical.choice', 'Quot.sound'])
        audit_source = self.raw('authoring/preparation-v5/MemberFullAudit.lean')
        self.assertEqual(audit_source, self.raw('totality-core/21-MemberFullAudit/monitor/explicit-inputs/MemberFullAudit.lean'))
        for marker in (b'info.isUnsafe', b'info.isPartial', b'isNoncomputable', b'getImplementedBy?',
                       b'getExternAttrData?', b'.axiomInfo', b'collectAxioms', b'run_cmd'):
            self.assertIn(marker, audit_source)
        probe = self.raw('v9-full/24-MemberBoundaryProbes/monitor/stdout')
        for marker in (b'readOriginal_facts', b'readOriginal_boundary', b'checkOrdered_sound',
                       b'Boundary', b'ReaderBindings', b'PartMember', b'member_refines'):
            self.assertIn(marker, probe)
        remaining = self.raw('v9-tail3/26-MemberSmallExamples/monitor/stdout').decode().strip()
        self.assertEqual(remaining, str(self.META['remaining_work']))
        self.assertEqual(remaining, '1979563')
        self.assertIs(type(self.META['remaining_work']), int)
        self.assertTrue(0 <= self.META['remaining_work'] <= 2000000)

    def test_all_71_legacy_cases_survive_complete_except_equality_repair(self):
        old = self.raw('authoring/preparation-v5/MemberLegacyComparison.lean')
        repaired = self.raw('test-repair/MemberLegacyComparison.lean')
        final = self.raw('test-repair2/MemberLegacyComparison.lean')
        equality = '''

/-- Test-local total equality, including exact error text and complete success values. -/
local instance exceptDecidableEq {α : Type} [DecidableEq α] :
    DecidableEq (Except String α)
  | .error first, .error second =>
      if equal : first = second then .isTrue (by cases equal; rfl)
      else .isFalse (by intro result; cases result; exact equal rfl)
  | .ok first, .ok second =>
      if equal : first = second then .isTrue (by cases equal; rfl)
      else .isFalse (by intro result; cases result; exact equal rfl)
  | .error _, .ok _ => .isFalse (by intro result; cases result)
  | .ok _, .error _ => .isFalse (by intro result; cases result)
'''.encode()

        def normalize_proof_repair(raw):
            self.assertEqual(raw.count(equality), 1)
            return raw.replace(equality, b'', 1).replace(b':= by decide +kernel', b':= by decide_cbv')

        marker = b'-- Separate proofs keep first failures attributable and bound each reduction.'
        self.assertEqual(old.split(marker, 1)[1], repaired.split(marker, 1)[1])
        # Full byte equality after this exact proof-only normalization preserves
        # all statements, data and budgets, not just the number of examples.
        self.assertEqual(normalize_proof_repair(final), repaired)
        for raw in (old, repaired, final):
            self.assertEqual(raw.count(b'\nexample :'), 71)
        self.assertIn(b'| .error first, .error second => decide (first = second)', repaired)
        self.assertIn(b'| .ok first, .ok second => decide (first = second)', repaired)
        self.assertIn(b'| _, _ => false', repaired)
        self.assertIn(b'sameExcept (SourceTypes.lex source) (SourceTypesLegacy.lex source) &&', repaired)
        self.assertIn(b'sameExcept (newDecls source) (oldDecls source)', repaired)
        self.assertEqual(old, self.raw('v9-full/25-MemberLegacyComparison/monitor/explicit-inputs/MemberLegacyComparison.lean'))
        self.assertEqual(repaired, self.raw('v9-tail/25-MemberLegacyComparison/monitor/explicit-inputs/MemberLegacyComparison.lean'))
        self.assertEqual(final, self.raw('v9-tail2/25-MemberLegacyComparison/monitor/explicit-inputs/MemberLegacyComparison.lean'))
        self.assertEqual(final, self.raw('v9-tail3/25-MemberLegacyComparison/monitor/explicit-inputs/MemberLegacyComparison.lean'))
        small = self.raw('test-repair2/MemberSmallExamples.lean')
        self.assertEqual(normalize_proof_repair(small), self.raw('authoring/preparation-v5/MemberSmallExamples.lean'))
        self.assertEqual(small.count(b'\nexample :'), 7)
        self.assertEqual(small, self.raw('v9-tail2/26-MemberSmallExamples/monitor/explicit-inputs/MemberSmallExamples.lean'))
        generic_small = self.raw('test-repair3/MemberSmallExamples.lean')
        string_signature = ('local instance exceptDecidableEq {α : Type} [DecidableEq α] :\n'
                            '    DecidableEq (Except String α)').encode()
        generic_signature = ('local instance exceptDecidableEq {ε α : Type} [DecidableEq ε] [DecidableEq α] :\n'
                             '    DecidableEq (Except ε α)').encode()
        self.assertEqual(small.count(string_signature), 1)
        self.assertEqual(generic_small, small.replace(string_signature, generic_signature, 1))
        self.assertEqual(generic_small, self.raw('v9-tail3/26-MemberSmallExamples/monitor/explicit-inputs/MemberSmallExamples.lean'))
        repair3 = self.decoded('test-repair3/provenance.json')
        self.assertEqual((repair3['format'], repair3['version'], repair3['status'], repair3['source_commit']),
                         ('qleisli.member-v9-test-generic-except-repair', 1, 'uncompiled test-only repair', self.HEAD))
        self.assertEqual(repair3['unchanged_statement_count'], 7)
        self.assertIs(repair3['production_sources_changed'], False)
        for field, source, raw in (('before', self.REPAIR2 + 'MemberSmallExamples.lean', small),
                                   ('after', self.REPAIR3 + 'MemberSmallExamples.lean', generic_small)):
            pin = repair3[field]
            self.assertEqual((pin['path'], pin['resolved'], pin['link']), (source, source, None))
            self.assertEqual({key: pin[key] for key in ('bytes', 'sha256')}, self.pin(raw))
            self.assertEqual(pin['mode'], self.originals[self.original_source_name(source)]['original_mode'])
        delta = self.raw('test-repair3/delta.patch')
        self.assertTrue(delta.startswith(('--- ' + self.REPAIR2 + 'MemberSmallExamples.lean\n+++ ' +
                                         self.REPAIR3 + 'MemberSmallExamples.lean\n').encode()))
        for prefix, signature in ((b'-', string_signature), (b'+', generic_signature)):
            for line in signature.splitlines():
                self.assertIn(prefix + line + b'\n', delta)
        failed = self.windows('v9-tail2')[-1]
        self.assertEqual((failed['index'], failed['module'], failed['pass']), (26, 'MemberSmallExamples', False))
        self.check_failure_binding(repair3['failure'], failed, 'test-repair3/tail2-failure-')
        for stream in ('stdout', 'stderr'):
            self.assertEqual(self.raw('test-repair2/tail1-failure-' + stream + '.txt'),
                             self.raw('v9-tail/25-MemberLegacyComparison/monitor/' + stream))
        failed_stdout = self.raw('test-repair3/tail2-failure-stdout.txt')
        self.assertIn(b'1979563', failed_stdout.splitlines())
        self.assertIn(b'failed to synthesize', failed_stdout)
        self.assertIn(b'BEq', self.raw('v9-full/25-MemberLegacyComparison/monitor/stdout'))
        self.assertIs(self.windows('v9-full')[-1]['pass'], False)
        self.assertIs(self.windows('v9-tail')[0]['pass'], False)
        self.assertIs(self.windows('v9-tail2')[0]['pass'], True)
        self.assertIs(self.windows('v9-tail2')[-1]['pass'], False)
        self.assertIs(self.windows('v9-tail3')[1]['pass'], True)
        self.assertIs(self.windows('v9-tail3')[-1]['pass'], False)


if __name__ == '__main__':
    unittest.main()
