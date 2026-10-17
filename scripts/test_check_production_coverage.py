"""Migration coverage must fail closed on omitted or newly exposed paths."""
import copy
import json
from pathlib import Path
import tomllib
import unittest
from unittest.mock import patch
import check_production_coverage as coverage
from check_verification_inventory import variants


class ProductionCoverage(unittest.TestCase):
    def setUp(self):
        self.data = json.loads((coverage.ROOT/coverage.COVERAGE).read_text())
        self.inventory = json.loads((coverage.ROOT/coverage.INVENTORY).read_text())

    def test_current_review_accounts_for_all_groups_and_boundaries(self):
        result = coverage.check(coverage.ROOT, self.data, self.inventory)
        self.assertEqual(result['groups'], len(self.inventory['groups']))
        self.assertEqual(result['groups'], 45)
        self.assertEqual(result['public_boundaries'], 24)
        self.assertEqual(result['authority'], 'Lean')
        self.assertEqual(result['target_authority'], 'Lean')
        self.assertEqual(result['migration'], 'single-lean-acceptance-implemented')
        self.assertEqual(result['production_paths'], 26)
        self.assertEqual(result['native_modes'], 13)
        self.assertEqual(result['published_baseline'], '0.2.9')
        product = tomllib.loads((coverage.ROOT / 'Cargo.toml').read_text())['package']
        self.assertEqual(result['development_version'], product['version'])
        self.assertEqual(result['development_status'], 'unpublished')
        raw = next(row for row in self.inventory['enums'] if row['name'] == 'RawOp')
        self.assertEqual(
            set(raw['members']),
            set(variants((coverage.ROOT / raw['path']).read_text(), raw['name'])),
        )

    def test_removed_duplicated_or_unjustified_rows_reject(self):
        for change in [lambda d: d['groups'].pop(), lambda d: d['boundaries'].append(d['boundaries'][0]),
                       lambda d: d['groups'][0].update(blocker=''), lambda d: d['groups'][0].update(cutover_gates=[]),
                       lambda d: d['groups'][0].update(proof_gates=[]),
                       lambda d: d['migration'].update(status='complete'),
                       lambda d: d['boundaries'][0].update(status='untrusted-host'),
                       lambda d: d['boundaries'][0].update(status='component-only'),
                       lambda d: d['boundaries'][0].update(route_test=dict(path='tests/native_paths.rs', test='missing')),
                       lambda d: d['groups'][0].update(status='selected-dual'),
                       lambda d: d.update(authority='Rust'), lambda d: d.update(external_schemas_enabled=True),
                       lambda d: d['gates'][0].update(status='passed')]:
            data = copy.deepcopy(self.data)
            change(data)
            with self.subTest(change=change), self.assertRaises(ValueError):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_new_entrypoint_or_signature_requires_review(self):
        self.inventory['boundaries'][0]['entry_points'].append('new public entry')
        with self.assertRaisesRegex(ValueError, 'surface changed'):
            coverage.check(coverage.ROOT, self.data, self.inventory)
        self.data['surface_sha256'] = coverage.surface_identity(self.inventory)
        with self.assertRaisesRegex(ValueError, 'entry point'):
            coverage.check(coverage.ROOT, self.data, self.inventory)

    def test_proposals_documentation_and_execution_are_not_acceptance(self):
        paths = {row['id']: row for row in self.data['paths']}
        for name in ('raw-proposal', 'finite-proposal', 'source-documentation',
                     'sized-proposal', 'host-execution', 'hierarchy-execution',
                     'foreign-export', 'checked-views'):
            data = copy.deepcopy(self.data)
            row = next(row for row in data['paths'] if row['id'] == name)
            self.assertEqual(paths[name]['native_modes'], [])
            row['classification'] = 'native-acceptance'
            with self.subTest(path=name), self.assertRaisesRegex(ValueError, 'classification'):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_contract_protocol_cannot_inherit_the_ordinary_root(self):
        row = next(row for row in self.data['paths'] if row['id'] == 'contract-acceptance')
        row['native_modes'] = ['--qirf-native']
        with self.assertRaisesRegex(ValueError, 'classification or binding'):
            coverage.check(coverage.ROOT, self.data, self.inventory)

    def test_contract_bridge_does_not_widen_encoded_or_admitted_guarantees(self):
        for field, claim in (
            ('proof_scope', 'check_sound proves the encoded equation for the original root'),
            ('gaps', 'None; these declarations admit full QS, PR and RS'),
        ):
            data = copy.deepcopy(self.data)
            row = next(row for row in data['paths'] if row['id'] == 'contract-acceptance')
            row[field] = claim
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'native-contract proof scope'):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_missing_contract_bridge_or_review_declaration_rejects(self):
        for path, marker in (
            ('lean/Qleisli/NativeContract.lean', 'theorem check_sound'),
            ('tests/fixtures/constitution_v030/native-contract-bridge/Review.lean',
             '#print Qleisli.NativeContract.LeafMeaning'),
        ):
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, 'source binding changed'):
                self.check_changed_source(path, marker, 'removed declaration')

    def test_hierarchy_report_cannot_be_classified_as_ordinary_acceptance(self):
        row = next(row for row in self.data['paths'] if row['id'] == 'hierarchy-request')
        self.assertEqual(row['classification'], 'native-hierarchy-check')
        row['classification'] = 'native-acceptance'
        with self.assertRaisesRegex(ValueError, 'classification'):
            coverage.check(coverage.ROOT, self.data, self.inventory)

    def test_engineering_report_has_a_separate_native_mode_and_cannot_be_exact_acceptance(self):
        path = next(row for row in self.data['paths'] if row['id'] == 'engineering-pure-check')
        self.assertEqual(path['classification'], 'engineering-check')
        self.assertEqual(path['native_modes'], ['--engineering-pure-check'])
        self.assertEqual(path['boundaries'], ['engineering-pure'])
        for field, value in (('classification', 'native-acceptance'),
                             ('classification', 'native-hierarchy-check'),
                             ('native_modes', ['--qirf-contract'])):
            data = copy.deepcopy(self.data)
            row = next(row for row in data['paths'] if row['id'] == 'engineering-pure-check')
            row[field] = value
            with self.subTest(field=field, value=value), self.assertRaisesRegex(ValueError, 'classification or binding'):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_engineering_status_cannot_be_promoted_or_reused_for_existing_acceptance(self):
        for section, identifier, status in (
            ('groups', 'engineering-pure', 'native-execution'),
            ('boundaries', 'engineering-pure', 'native-execution'),
            ('groups', 'engineering-instrument', 'native-execution'),
            ('boundaries', 'engineering-instrument', 'native-execution'),
            ('groups', 'engineering-pure-tensor', 'native-execution'),
            ('boundaries', 'engineering-pure-tensor', 'native-execution'),
            ('groups', 'engineering-openqasm', 'native-execution'),
            ('boundaries', 'engineering-openqasm', 'native-execution'),
            ('groups', 'raw-core', 'engineering-check'),
            ('boundaries', 'qirf-native-v029', 'engineering-check'),
        ):
            data = copy.deepcopy(self.data)
            row = next(row for row in data[section] if row['id'] == identifier)
            row['status'] = status
            with self.subTest(section=section, identifier=identifier), self.assertRaisesRegex(ValueError, 'engineering-only status'):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_engineering_proof_scope_cannot_claim_source_resources_or_constitutional_discharge(self):
        for field, claim in (
            ('proof_scope', 'epsilon zero promotes the engineering report to exact source Meaning'),
            ('gaps', 'None; the report certifies cleanup, physical realization and QS/PR/RS'),
        ):
            data = copy.deepcopy(self.data)
            row = next(row for row in data['paths'] if row['id'] == 'engineering-pure-check')
            row[field] = claim
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'engineering-pure proof scope'):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_missing_engineering_original_byte_or_execution_view_binding_rejects(self):
        for path, marker in (
            ('lean-kernel/Protocol/EngineeringPure.lean', 'theorem checkRetained_bound'),
            ('lean-kernel/Protocol/ExecutionView/CheckedEngineeringPure.lean', 'theorem run_binding'),
            ('lean/Qleisli/NativeEngineeringPureProtocol.lean', 'theorem run_meaning'),
        ):
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, 'source binding changed'):
                self.check_changed_source(path, marker, 'removed declaration')

    def test_instrument_engineering_route_cannot_reuse_exact_or_inspection_acceptance(self):
        path = next(row for row in self.data['paths'] if row['id'] == 'engineering-instrument-check')
        self.assertEqual(path['classification'], 'engineering-check')
        self.assertEqual(path['native_modes'], ['--qirf-engineering-instrument-native'])
        for field, value in (
            ('classification', 'native-acceptance'),
            ('classification', 'native-hierarchy-check'),
            ('native_modes', ['--qirf-contract']),
            ('boundaries', ['engineering-pure']),
        ):
            data = copy.deepcopy(self.data)
            next(row for row in data['paths'] if row['id'] == path['id'])[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'classification or binding'):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_instrument_scope_cannot_promote_zero_phase_cleanup_resources_or_composition(self):
        for field, claim in (
            ('proof_scope', 'epsilon zero grants exact source Meaning and pure phase/control access'),
            ('proof_scope', 'the Gram contraction and tensor lemmas certify original QIRF native composed handles'),
            ('gaps', 'None; qirf-r8-instrument-v1 certifies hardware cleanup, resources and QS/PR/RS/EXACT'),
        ):
            data = copy.deepcopy(self.data)
            next(row for row in data['paths'] if row['id'] == 'engineering-instrument-check')[field] = claim
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'engineering-instrument proof scope'):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_instrument_original_roots_public_view_and_actual_meaning_proof_are_required(self):
        for path, marker in (
            ('lean-kernel/Protocol/EngineeringInstrument.lean', 'theorem checkRetained_bound'),
            ('lean-kernel/Protocol/EngineeringInstrument.lean', 'Qirf.read decoded.expectedText.toUTF8'),
            ('lean-kernel/Protocol/ExecutionView/EngineeringInstrument.lean', 'graph value.expected value.checked.expected'),
            ('lean-kernel/Protocol/ExecutionView/CheckedEngineeringInstrument.lean', 'supplied.data == expected.data'),
            ('lean-kernel/Protocol/ExecutionView/CheckedEngineeringInstrument.lean', '.inspection | .caller => throw .packet'),
            ('lean-kernel/Protocol/ExecutionView/CheckedEngineeringInstrument.lean', 'theorem run_binding'),
            ('src/interchange/execution_view/finite/engineering_instrument.rs', 'actual.execution_view_graph().write(w.writer)'),
            ('lean/Qleisli/NativeEngineeringInstrumentProtocol.lean', 'theorem run_meaning'),
        ):
            with self.subTest(path=path, marker=marker), self.assertRaisesRegex(ValueError, 'source binding changed'):
                self.check_changed_source(path, marker, 'removed binding')

    def test_internal_instrument_composition_requires_gram_and_axis_proofs(self):
        for path, marker in (
            ('lean/Qleisli/EngineeringInstrumentPureComparison.lean', 'actual_gram : actual.conjTranspose * actual = 1'),
            ('lean/Qleisli/EngineeringInstrumentComposition.lean', 'theorem gram_completeAdjoint_contraction'),
            ('lean/Qleisli/EngineeringInstrumentComposition.lean', 'theorem feedForward_gram'),
            ('lean/Qleisli/EngineeringInstrumentTensor.lean', 'def rightAxes '),
            ('lean/Qleisli/EngineeringInstrumentTensor.lean', 'theorem tensor_gram'),
        ):
            with self.subTest(path=path, marker=marker), self.assertRaisesRegex(ValueError, 'source binding changed'):
                self.check_changed_source(path, marker, 'removed premise or proof')

    def test_tensor_engineering_route_cannot_reuse_exact_or_single_component_mode(self):
        for field, value in (
            ('classification', 'native-acceptance'),
            ('native_modes', ['--engineering-pure-check']),
            ('boundaries', ['engineering-pure']),
        ):
            data = copy.deepcopy(self.data)
            next(row for row in data['paths'] if row['id'] == 'engineering-pure-tensor-check')[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'classification or binding'):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_tensor_scope_cannot_replace_composition_or_promote_zero(self):
        for field, claim in (
            ('proof_scope', 'whole-parent Frobenius checking alone certifies additive composition'),
            ('proof_scope', 'epsilon zero grants exact Meaning and target RS'),
            ('gaps', 'None; source, control and emitted-target preservation are complete'),
        ):
            data = copy.deepcopy(self.data)
            next(row for row in data['paths'] if row['id'] == 'engineering-pure-tensor-check')[field] = claim
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'engineering-pure-tensor proof scope'):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_tensor_originals_total_budget_and_reference_proof_are_required(self):
        for path, marker in (
            ('lean-kernel/Protocol/EngineeringPureTensor.lean', 'theorem checkRetained_bound'),
            ('lean-kernel/QleisliKernel/Qirf/EngineeringPureTensor.lean', 'guard (epsilon == request.epsilon)'),
            ('lean-kernel/Protocol/ExecutionView/CheckedEngineeringPureTensor.lean', 'supplied.data == expected.data'),
            ('lean-kernel/Protocol/ExecutionView/CheckedEngineeringPureTensor.lean', '.inspection | .caller => throw .packet'),
            ('lean/Qleisli/NativeEngineeringPureTensorProtocol.lean', 'theorem run_reference_bound'),
        ):
            with self.subTest(path=path, marker=marker), self.assertRaisesRegex(ValueError, 'source binding changed'):
                self.check_changed_source(path, marker, 'removed required binding')

    def test_target_engineering_requires_its_distinct_execution_mode_and_boundary(self):
        for field, value in (
            ('classification', 'native-acceptance'),
            ('native_modes', ['--qirf-native']),
            ('native_modes', ['--qirf-engineering-instrument-native']),
            ('boundaries', ['engineering-instrument']),
        ):
            data = copy.deepcopy(self.data)
            next(row for row in data['paths'] if row['id'] == 'engineering-openqasm-check')[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'classification or binding'):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_target_engineering_cannot_claim_source_export_resources_or_exact_promotion(self):
        for field, claim in (
            ('proof_scope', 'The bound proves exact source/export correspondence and target resources'),
            ('gaps', 'No remaining obligation; epsilon zero grants accepted programs and control'),
        ):
            data = copy.deepcopy(self.data)
            next(row for row in data['paths'] if row['id'] == 'engineering-openqasm-check')[field] = claim
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'engineering-openqasm proof scope'):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_target_bytes_word_original_ideal_and_full_reference_binding_are_required(self):
        for path, marker in (
            ('lean-kernel/QleisliKernel/Target/CanonicalOpenQasm.lean', 'theorem decode_original'),
            ('lean-kernel/QleisliKernel/Semantics/CanonicalTerminalQasm.lean', 'theorem logical_unit_consumed'),
            ('lean-kernel/QleisliKernel/Qirf/EngineeringOpenQasm.lean', 'exactWork (Exact.charge (1 + request.target.size))'),
            ('lean-kernel/QleisliKernel/Qirf/EngineeringOpenQasm.lean',
             'request.actualSignature == Semantics.CanonicalTerminalQasm.signature'),
            ('lean-kernel/Protocol/EngineeringOpenQasm.lean', 'Qirf.read decoded.expectedText.toUTF8'),
            ('lean-kernel/Protocol/ExecutionView/EngineeringOpenQasm.lean',
             'value.checked.target.original.data.toList'),
            ('lean-kernel/Protocol/ExecutionView/EngineeringOpenQasm.lean', 'value.checked.target.gates.map'),
            ('lean-kernel/Protocol/ExecutionView/CheckedEngineeringOpenQasm.lean',
             '.inspection | .caller => throw .packet'),
            ('lean/Qleisli/NativeEngineeringOpenQasmProtocol.lean', 'theorem run_complete_adjoint_bound'),
        ):
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, 'source binding changed'):
                self.check_changed_source(path, marker, 'removed required binding')

    def test_omitted_route_and_boundary_path_reject(self):
        for change in (lambda d: d['paths'].pop(),
                       lambda d: d['boundaries'][0]['paths'].pop()):
            data = copy.deepcopy(self.data)
            change(data)
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'path|route'):
                coverage.check(coverage.ROOT, data, self.inventory)

    def check_changed_source(self, name, old, new):
        read = Path.read_text
        selected = coverage.ROOT/name
        self.assertIn(old, selected.read_text())
        def altered(path, *args, **kwargs):
            text = read(path, *args, **kwargs)
            return text.replace(old, new, 1) if path == selected else text
        with patch.object(Path, 'read_text', altered):
            coverage.check(coverage.ROOT, self.data, self.inventory)

    def test_new_removed_and_redirected_native_modes_reject(self):
        line = '| "--qirf-native" => some QleisliKernel.Cli.runValidity'
        replacements = (
            line + '\n  | "--new-mode" => none',
            '',
            '| "--qirf-native" => some (QleisliKernel.Cli.runValidity true)',
        )
        for replacement in replacements:
            with self.subTest(replacement=replacement), self.assertRaisesRegex(ValueError, 'native mode'):
                self.check_changed_source('lean-kernel/Main.lean', line, replacement)

    def test_missing_bound_source_or_checker_declaration_reject(self):
        selected = coverage.ROOT/'lean-kernel/Protocol/NativeContract.lean'
        is_file = Path.is_file
        with patch.object(Path, 'is_file', lambda path: False if path == selected else is_file(path)):
            with self.assertRaisesRegex(ValueError, 'missing production source'):
                coverage.check(coverage.ROOT, self.data, self.inventory)
        with self.assertRaisesRegex(ValueError, 'source binding changed'):
            self.check_changed_source('lean-kernel/Protocol/NativeContract.lean', 'def check ', 'def renamed ')

    def test_missing_documentation_regression_rejects(self):
        with self.assertRaisesRegex(ValueError, 'missing production path regression'):
            self.check_changed_source('tests/cli.rs',
                                      'fn doc_reads_one_file_and_does_not_claim_type_checking()',
                                      'fn renamed_documentation_test()')

    def test_terminal_equation_requires_bound_kernel_full_bodies_and_shared_work(self):
        for marker in (
            'program.kernel()', 'FunctionEvidence::check_retained_with_kernel(',
            'equation.implementation() == &original', 'equation.specification() == &proposed',
            'work: Budget::new(DEFAULT_EXACT_WORK),', 'const MAX_LOCAL_EQUATIONS: usize = 7;',
        ):
            with self.subTest(marker=marker), self.assertRaisesRegex(ValueError, 'source binding changed'):
                self.check_changed_source('src/interop/export/normalization.rs', marker, 'removed binding')

    def test_terminal_target_word_requires_actual_operands_boundaries_and_atomic_replacement(self):
        for path, marker in [('src/interop/profile.rs', 'let mut normalization_barriers = [false; MAX_GATES + 1];'),
 ('src/interop/profile.rs',
  'super::export::finish(&mut circuit, &mut expansion, &normalization_barriers)?;'),
 ('src/interop/export.rs', 'expansion.normalizations.terminal(circuit, barriers)?;'),
 ('src/interop/export/normalization.rs', 'if barriers[index + 1] || barriers[index + 2] {'),
 ('src/interop/export/normalization.rs', '.charge(circuit.gates.len() + 1)'),
 ('src/interop/export/normalization.rs',
  'let mapped = |op: &GateOp| -> Result<CircuitStep, InteropError> {\n'
  '        let mut step = op.gate.step();'),
 ('src/interop/export/normalization.rs', '|| word[0].wires != word[1].wires'),
 ('src/interop/export/normalization.rs',
  'let mut original = std::mem::take(&mut circuit.gates).into_iter().enumerate();')]:
            self.assertEqual((coverage.ROOT / path).read_text().count(marker), 1)
            with self.subTest(path=path, marker=marker), self.assertRaisesRegex(ValueError, 'source binding changed'):
                self.check_changed_source(path, marker, 'removed terminal binding')

    def test_terminal_target_word_cannot_omit_new_native_and_negative_regressions(self):
        for path, name in [('src/interop/export/normalization.rs',
  'final_target_windows_retain_axes_order_and_nonpure_barriers'),
 ('src/interop/export/normalization.rs',
  'final_target_equation_failure_retains_the_original_gates'),
 ('src/interop/export/normalization.rs',
  'final_target_native_equations_share_full_receipts_and_preserve_all_columns'),
 ('tests/interop.rs', 'ordinary_inlined_hzh_exports_literal_x_across_pure_raw_steps'),
 ('tests/interop.rs', 'final_target_window_does_not_cross_fresh_preparation')]:
            with self.subTest(path=path, test=name), self.assertRaisesRegex(ValueError, 'missing production path regression'):
                self.check_changed_source(path, 'fn ' + name + '(', 'fn omitted_terminal_test(')

    def test_fixed_fourier_original_transport_requires_source_graph_and_fresh_checker(self):
        for path, marker in [('src/frontend/specialize/lower.rs',
  'pub fn source_trace_graph(&self) -> &[u8] {\n        &self.retained_source_proposal().graph'),
 ('src/frontend/specialize/lower.rs',
  '.check_instrument_native(original.payload(), original.comparison_request())'),
 ('src/frontend/specialize/lower.rs',
  'if actual_structural_work > 2_000_000\n'
  '                || checked.structural_work() > 2_000_000\n'
  '                || actual_exact_work > crate::contract::DEFAULT_EXACT_WORK\n'
  '                || checked.exact_work() > crate::contract::DEFAULT_EXACT_WORK'),
 ('src/frontend/specialize/lower.rs',
  'if forward_isometry && !zero_basis::materialized_without_repeat(operation)? {'),
 ('src/frontend/specialize/lower/zero_basis.rs',
  'operations::validate_bound(proposal, event, operation, defs, adjoint)'),
 ('src/frontend/specialize/lower/zero_basis/operations.rs',
  'matcher.bound(operation, id, &before, &after, adjoint, 0)'),
 ('src/interchange/hierarchical.rs',
  'pub(crate) fn checker(&self) -> &Path {\n        &self.checker'),
 ('src/frontend/specialize/lower/fourier_transport.rs', 'const RETAINED_BYTES: usize = 16 << 20;'),
 ('src/frontend/specialize/lower/fourier_transport.rs', 'const RETAINED_CELLS: usize = 100_000;'),
 ('src/frontend/specialize/lower/fourier_transport.rs', 'const REPLAY_WORK: usize = 2_000_000;'),
 ('src/frontend/specialize/lower/fourier_transport.rs',
  '!proposal.source.same_witness_source(&original.source)'),
 ('src/frontend/specialize/lower/fourier_transport.rs', 'expected.payload != proposal.payload'),
 ('src/frontend/specialize/lower/fourier_transport.rs', 'expected.bindings != transport.bindings'),
 ('src/frontend/specialize/lower/fourier_transport.rs',
  'bindings.retain(|binding| mapping.contains_key(&binding.original));')]:
            self.assertEqual((coverage.ROOT / path).read_text().count(marker), 1)
            with self.subTest(path=path, marker=marker), self.assertRaisesRegex(ValueError, 'source binding changed'):
                self.check_changed_source(path, marker, 'removed original transport binding')

    def test_fixed_fourier_source_transport_keeps_native_and_source_regressions(self):
        for path, name in [('src/frontend/specialize/lower/zero_basis/transform_tests.rs',
  'forward_preparation_operation_retains_its_original_source_interval'),
 ('src/frontend/specialize/lower/zero_basis/transform_tests.rs',
  'public_isometry_repetition_retains_its_effect_refusal'),
 ('src/frontend/specialize/lower/zero_basis/transform_tests.rs',
  'materialized_unitary_repetition_before_preparation_retains_its_profile_refusal'),
 ('src/frontend/specialize/lower/fourier_transport.rs',
  'fixed_fourier_transport_retains_every_original_source_root_and_selector'),
 ('src/frontend/specialize/lower/fourier_transport.rs',
  'outer_fixed_fourier_replacement_retains_subsumed_inner_source_obligations'),
 ('src/frontend/specialize/lower/fourier_transport.rs',
  'native_original_and_factored_fixed_fourier_keep_complex_reference_and_full_phase'),
 ('src/frontend/specialize/lower/fourier_transport.rs',
  'native_valid_x_cannot_replace_the_retained_fixed_fourier_h'),
 ('src/frontend/specialize/lower/fourier_transport.rs',
  'source_validation_requires_a_fresh_original_check_after_main_acceptance'),
 ('src/interchange/hierarchical/runtime.rs',
  'all_native_modes_retain_invoked_canonical_paths_after_alias_and_target_moves')]:
            with self.subTest(path=path, test=name), self.assertRaisesRegex(ValueError, 'missing production path regression'):
                self.check_changed_source(path, 'fn ' + name + '(', 'fn omitted_original_transport_test(')

    def test_prepared_hierarchy_requires_indexed_equivalence_and_paid_full_fallback(self):
        for path, marker in [('lean-kernel/QleisliKernel/Hierarchical/Artifact.lean', 'theorem prepare_proofEndpoints'),
         ('lean-kernel/QleisliKernel/Hierarchical/TypedRule.lean', 'theorem preparedOrdinary_eq'),
         ('lean-kernel/QleisliKernel/Hierarchical/NodeTyping.lean',
          'let charge := legacy - maps + selectedMapsCost artifact definition'),
         ('lean-kernel/QleisliKernel/Hierarchical/ContractTyping.lean',
          'let charge := legacy - value.mapsCost artifact + value.selectedMapsCost artifact'),
         ('lean-kernel/QleisliKernel/Hierarchical/Ports.lean', 'theorem shapeAfterHeaders_eq'),
         ('lean-kernel/QleisliKernel/Layout.lean', 'theorem identity_structureValid')]:
            with self.subTest(path=path, marker=marker), self.assertRaisesRegex(ValueError, 'source binding changed'):
                self.check_changed_source(path, marker, 'removed prepared binding')

    def test_trace_project_once_requires_actual_projection_precharge_and_original_checks(self):
        for path, marker in [('lean-kernel/QleisliKernel/Hierarchical/CircuitTrace.lean', 'theorem summarizeProjected_eq'),
         ('lean-kernel/QleisliKernel/Hierarchical/CircuitTrace.lean',
          'if state.visits + rawScan atoms d > remaining then .error .limit else\n'
          '    if state.visits + scan atoms d > remaining then .error .limit else'),
         ('lean-kernel/QleisliKernel/Hierarchical/CircuitTrace.lean',
          'scan atoms d + 8 * (1 + node.children.length) * (1 + events) * (1 + span)^2'),
         ('lean-kernel/QleisliKernel/Hierarchical/QpeSchedule.lean',
          'match CircuitTrace.inspect artifact (atoms candidate) candidate.traceOrder')]:
            with self.subTest(path=path, marker=marker), self.assertRaisesRegex(ValueError, 'source binding changed'):
                self.check_changed_source(path, marker, 'removed prepared binding')

    def test_historical_release_is_not_current_alpha_certification(self):
        for change in (
            lambda d: d['validation']['current_development'].update(status='published and verified'),
            lambda d: d['validation']['published_baseline'].update(version='0.3.0-alpha'),
            lambda d: d['validation'].update(proof_status='discharged'),
        ):
            data = copy.deepcopy(self.data)
            change(data)
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'status must remain separate'):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_new_boundary_requires_an_explicit_route_even_after_surface_refresh(self):
        boundary = copy.deepcopy(self.inventory['boundaries'][0])
        boundary['id'] = 'new-boundary'
        self.inventory['boundaries'].append(boundary)
        row = copy.deepcopy(self.data['boundaries'][0])
        row['id'] = 'new-boundary'
        self.data['boundaries'].append(row)
        self.data['surface_sha256'] = coverage.surface_identity(self.inventory)
        with self.assertRaisesRegex(ValueError, 'unreviewed public boundary route'):
            coverage.check(coverage.ROOT, self.data, self.inventory)


if __name__ == '__main__':
    unittest.main()
