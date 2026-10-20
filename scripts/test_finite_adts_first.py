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
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import tarfile
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

    def test_exact_duplicated_extraction_uses_its_existing_canonical_fixture(self):
        import gzip
        reference = json.loads(self.data['native-v2-lean-validation/extract-stdout-reference.json'])
        packed = (ROOT / reference['canonical_gzip']).read_bytes()
        self.assertEqual(hashlib.sha256(packed).hexdigest(), reference['gzip_sha256'])
        actual = gzip.decompress(packed)
        self.assertEqual(len(actual), reference['observed_stdout_bytes'])
        self.assertEqual(hashlib.sha256(actual).hexdigest(), reference['observed_stdout_sha256'])
        self.assertTrue(reference['byte_identical_to_decompressed_canonical'])


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


if __name__ == '__main__':
    unittest.main()
