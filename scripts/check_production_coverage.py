#!/usr/bin/env python3
"""Check reviewed production routes and historical release binding, not soundness.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import hashlib
import json
from pathlib import Path
import re
import sys
import tomllib
from check_verification_inventory import INVENTORY, test_names

ROOT = Path(__file__).resolve().parents[1]
COVERAGE = 'tests/fixtures/verification_v029/coverage.json'
GATES = {'S05-C1', 'S05-C2', 'S05-C3', 'S05-C4', 'S05-C5'}
CUTOVER = {'MIG-1', 'MIG-2', 'MIG-3', 'MIG-4', 'MIG-5'}
PUBLICATION = 'tests/fixtures/releases/v0.2.9/publication.json'
PUBLISHED_COMMIT = 'a77e68f4d3942cd75cb4c4710350aab9a99f8c8b'
CONTRACT_PROOF = {
    'proof_scope': (
        'Protocol.NativeContract.check_acceptance binds original QLV1 body/request bytes, decoded '
        'artifact and request, and continuous checking states. Qleisli.NativeContract.check_root_meaning '
        'and check_sound establish RootMeaning for all request kinds. For leaf requests, leaf_meaning '
        'establishes original-body instrument meaning for the bounded closed unitary fragment, exact '
        'requested matrix/signature/ordered ports, and an actual verification of the output port; '
        'leaf_reference_laws extends both whole-space inverse laws to any finite reference. '
        'For encoded requests, check_encoded_sound and encoded_meaning bind the original root BodyMeaning, '
        'exact Basis interface and Encoded equation; Wrapper.circuitMatrix_entries proves actual wrapper '
        'coefficients equal the original reconstructed matrix, including zero-width phase and axis order. '
        'encoded_reference extends the equation to every reference amplitude function. '
        'For control requests, ControlAcceptance binds decoded signature/axes to the reconstructed original '
        'action; control_meaning establishes original BodyMeaning, exact interface, unitarity and '
        'sector preservation. control_reference proves projector commutation for every joint amplitude '
        'and arbitrary reference. Finite project ctrl calls bind fresh native decisions to actual emitted '
        'call intervals and original ordered owner interfaces; selected-source integration, general '
        'source preservation and alias/resource obligations remain open.'
    ),
    'gaps': (
        'This separate protocol does not inherit NativeValidity.check_sound. General EffectSound/CPTP, source/compiler '
        'preservation, deployed-binary correspondence, Rust rematerialization, target/runtime preservation, '
        'clean-release and quantitative RS claims remain separate. These bridge theorems are not a new '
        'guarantee admission or S05 closure.'
    ),
}


def path_rule(classification, boundaries, modes, sources, tests):
    return dict(classification=classification, boundaries=boundaries.split(),
                native_modes=modes.split(),
                source_bindings=[dict(path=path, markers=markers) for path, markers in sources],
                tests=[dict(path=path, test=name) for path, name in tests])


# Reviewed declarations/dispatch markers, not a proof of the code they describe.
# Every inventory boundary and every Main.nativeMode must have an explicit rule.
PATHS = {
    'raw-proposal': path_rule('untrusted-proposal', 'raw qirf-native-v029', '', [
        ('src/interchange/native.rs', ['pub struct Proposal', 'pub fn from_raw(']),
    ], [('tests/native_acceptance.rs', 'native_handles_execute_bell_and_feedback_without_legacy_receipts')]),
    'finite-proposal': path_rule('untrusted-proposal', 'contract function finite-leaf', '', [
        ('src/contract/mod.rs', ['pub struct Circuit', 'pub struct Encoding', 'pub struct Contract']),
        ('src/contract/meaning.rs', ['pub fn permutation(', 'pub fn phase(', 'pub fn matrix(', 'pub fn target_ir(']),
        ('src/interchange/finite_leaf.rs', ['pub struct UnitaryBoundary']),
        ('src/interchange/finite_matrix.rs', ['pub fn encode(', 'pub fn decode(']),
    ], [('tests/semantic_contracts.rs', 'primitive_evidence_preserves_exact_phase')]),
    'ordinary-acceptance': path_rule('native-acceptance',
        'raw function qirf source foreign qirf-native-v028 qirf-native-v029', '--qirf-native', [
        ('src/interchange/native.rs', ['pub fn accept(', 'pub fn inspect(', '"--qirf-native"']),
        ('src/contract/function.rs', ['pub fn check(', '.function_evidence(']),
        ('src/contract/meaning.rs', ['pub fn check(', 'FunctionEvidence::']),
        ('src/frontend/compile/mod.rs', ['pub fn compile_project_with_kernel(', 'pub fn check_project_with_kernel(']),
        ('src/bin/qleisli/source_plan.rs', ['fn raw_execute(', 'native::Kernel::new(kernel).accept(proposal.proposal())', 'proposal.validate_source_steps(&checked)']),
        ('src/interchange/mod.rs', ['pub fn import(', 'pub fn convert(']),
        ('src/interop/openqasm.rs', ['pub fn import_openqasm3_with_kernel(']),
        ('lean-kernel/Cli/Validity.lean', ['Protocol.Validity.check']),
        ('lean-kernel/Protocol/Validity.lean', ['def check ', 'theorem check_acceptance', 'theorem check_ownershipSafe']),
        ('lean/Qleisli/NativeValidity.lean', ['theorem check_sound', 'theorem check_scopeSafe']),
    ], [('tests/native_paths.rs', 'native_report_retains_the_exact_artifact_request_and_reconstructed_program'),
        ('tests/function_evidence.rs', 'checks_two_raw_functions_and_retains_their_full_snapshots'),
        ('scripts/test_source_kernel.py', 'test_unused_body_native_rejection_blocks_every_source_action'),
        ('scripts/test_interop_native.py', 'test_all_actions_formats_use_real_native_checker'),
        ('tests/selected_source_cli.rs', 'selected_mixed_sources_keep_independent_distributions_and_scope'),
        ('tests/checked_operations.rs', 'canonical_inverse_application_preserves_ordinary_names_and_both_consumers'),
        ('tests/checked_operations.rs', 'canonical_power_literal_execution_keeps_ordinary_names_in_both_consumers'),
        ('tests/checked_operations.rs', 'canonical_control_finite_keeps_ordered_axes_and_ordinary_names'),
        ('tests/checked_operations.rs', 'canonical_control_finite_preserves_zero_width_phase_and_owner'),
        ('tests/checked_operations.rs', 'canonical_constructed_inverse_finite_keeps_order_and_zero_power_effects'),
        ('tests/checked_operations.rs', 'canonical_constructed_inverse_finite_preserves_scalar_and_refuses_false_meaning'),
        ('tests/qli_corpus.rs', 'canonical_control_migration_keeps_fixed_qpe_phase_and_reference_outcomes'),
        ('tests/quantum_unit_source.rs', 'canonical_power_original_program_and_symbolic_counts_preserve_z_phase'),
        ('tests/quantum_unit_source.rs', 'canonical_power_noncommuting_order_and_nested_inverse_have_independent_action'),
        ('tests/quantum_unit_source.rs', 'canonical_power_zero_width_scalar_and_control_keep_exact_phase'),
        ('tests/quantum_unit_source.rs', 'selected_z_direct_inverse_and_control_preserve_reference_phase'),
        ('tests/quantum_unit_source.rs', 'selected_z_interference_matches_finite_and_rejects_wrong_interfaces'),
        ('tests/quantum_unit_source.rs', 'complete_preserved_z_operation_probe_passes_raw_with_explicit_hierarchy_limit'),
        ('src/frontend/specialize/raw/preservation.rs', 'source_z_replay_rejects_native_valid_x_substitution'),
        ('tests/exclusive_access.rs', 'reassembled_owner_and_callee_binders_do_not_restore_old_snapshot'),
        ('tests/exclusive_access.rs', 'exact_owner_shape_and_actual_body_effect_are_required'),
        ('tests/exclusive_access.rs', 'both_source_paths_preserve_ctrl_phase_kickback_and_an_entangled_reference'),
        ('tests/exclusive_access.rs', 'finite_ctrl_rejects_actual_sector_changes_and_unused_lying_calls'),
        ('tests/exclusive_access.rs', 'finite_ctrl_checks_nested_calls_and_keeps_zero_width_phase')]),
    'contract-acceptance': path_rule('native-acceptance', 'contract finite-leaf', '--qirf-contract', [
        ('src/interchange/native/contracts.rs', ['fn check_encoded(', 'fn check_leaf(', '"--qirf-contract"']),
        ('lean-kernel/Cli/Validity.lean', ['Protocol.NativeContract.check']),
        ('lean-kernel/Protocol/NativeContract.lean', ['def check ', 'QleisliKernel.Qirf.checkContract',
         'QleisliKernel.Qirf.check ', 'structure Acceptance ', 'structure LeafAcceptance ',
         'structure ControlAcceptance ', 'QleisliKernel.Qirf.ControlAccess.check', 'theorem check_acceptance']),
        ('lean-kernel/QleisliKernel/Qirf/Contract.lean', ['theorem checkContract_bound']),
        ('lean/Qleisli/Qirf.lean', ['theorem reconstruct_semantics', 'theorem check_semantics']),
        ('lean/Qleisli/NativeContract.lean', ['structure LeafMeaning ', 'theorem check_root_meaning',
         'theorem leaf_meaning', 'theorem leaf_reference_laws', 'theorem check_sound',
         'structure EncodedMeaning ', 'theorem encoded_meaning', 'theorem check_encoded_sound',
         'theorem encoded_reference', 'structure ControlMeaning ', 'theorem control_meaning',
         'theorem control_reference']),
        ('lean/Qleisli/NativeContractWrapper.lean', ['theorem circuitMatrix_entries',
         'theorem check_encoded_original', 'theorem check_reference_original']),
        ('tests/fixtures/constitution_v030/native-contract-wrapper/Review.lean', [
         '#check @Qleisli.NativeContract.Wrapper.circuitMatrix_entries',
         '#check @Qleisli.NativeContract.check_encoded_sound']),
        ('tests/fixtures/constitution_v030/native-contract-bridge/Review.lean', [
         '#check @QleisliKernel.Protocol.NativeContract.check_acceptance',
         '#check @Qleisli.NativeContract.check_sound', '#print Qleisli.NativeContract.LeafMeaning']),
    ], [('tests/semantic_contracts.rs', 'primitive_evidence_preserves_exact_phase'),
        ('tests/finite_leaf.rs', 'reconstruct_hadamard_in_both_formats_and_bind_complete_bytes'),
        ('scripts/test_native_verification.py', 'test_control_requests')]),
    'source-documentation': path_rule('documentation', 'source', '', [
        ('src/bin/qleisli.rs', ['if options.command == "doc"', 'render_markdown(&source)']),
        ('src/frontend/documentation.rs', ['pub fn render_markdown(']),
    ], [('tests/cli.rs', 'doc_reads_one_file_and_does_not_claim_type_checking')]),
    'foreign-export': path_rule('host-transformation', 'foreign', '', [
        ('src/interop/mod.rs', ['pub fn export_openqasm3(program: &AcceptedProgram)', 'pub fn export_qir_base(program: &AcceptedProgram)']),
    ], [('scripts/test_interop_native.py', 'test_all_actions_formats_use_real_native_checker')]),
    'source-configuration': path_rule('configuration', 'source-edition-configuration', '', [
        ('src/frontend/project.rs', ['pub fn load(', 'pub fn load_with_policy(', 'pub fn read_source_file(']),
    ], [('tests/review_v021.rs', 'grouped_imports_expand_to_existing_leaves_with_docs_spans_and_resolution')]),
    'hierarchy-configuration': path_rule('configuration', 'hierarchy-inspect', '', [
        ('src/interchange/hierarchical.rs', ['pub fn new(']),
    ], [('tests/hierarchical_host.rs', 'native_request_binds_reindexed_shared_powers_and_exact_meaning_bytes')]),
    'host-execution': path_rule('host-execution', 'execution qirf-native-v029', '', [
        ('src/sim.rs', ['pub fn run_closed(']),
        ('src/sim/sampling.rs', ['pub fn sample_closed<']),
        ('src/host.rs', ['pub fn run_trials<']),
    ], [('tests/sampling.rs', 'stochastic_samples_match_independent_bell_and_reset_feedback_contracts')]),
    'hierarchy-execution': path_rule('host-execution', 'hierarchy-execution sized-source-proposal', '', [
        ('src/interchange/hierarchical/execution.rs', ['pub fn execute_pure(', 'pub fn execute_instrument(', 'pub fn sample_normalized_shots<']),
    ], [('tests/hierarchical_execution.rs', 'small_source_clients_match_independent_complex_reference_branches')]),
    'sized-proposal': path_rule('untrusted-proposal', 'sized-source-proposal', '', [
        ('src/frontend/check/body/places.rs', ['fn selected_place(', 'fn disjoint_places(',
         'self.require_access_unitary(name, scope, span)?',
         'CallArguments::Places(&prepared)', 'self.obligation(span, ObligationKind::ControlSectors)?']),
        ('src/frontend/specialize/projection.rs', ['indexed quantum access lowering is not yet implemented']),
        ('src/bin/qleisli.rs', ['source_plan::run(&args)']),
        ('src/frontend/compile/mod.rs', ['pub use super::specialize::{']),
        ('src/bin/qleisli/source_plan.rs', ['fn prepare(', 'fn execute(', 'prepared.payload()', 'untrusted-proposal', 'source_meaning_verified']),
        ('src/frontend/specialize.rs', ['pub fn parse(', 'pub fn instantiate(',
         'pub struct BasisBinding', 'pub fn instantiate_with_types(', 'pub fn with_types(',
         'pub fn finite_meaning_target(']),
        ('src/bin/qleisli/source_plan/options.rs', ['"type" =>', '"operation-type" =>',
         'never ordinary input']),
        ('src/frontend/specialize/raw.rs', ['pub struct RawSourceProposal', 'pub fn validate_source_steps(', 'native::Proposal::from_raw',
         'fn register_bit(', 'self.reserve_operations(3, span)?']),
        ('src/frontend/specialize/lower.rs', ['fn native_operation(', 'leaf.payload()', 'finite_matrix::encode(leaf.meaning())', 'entry.key == key']),
        ('src/frontend/specialize/elaborate.rs', ['pub fn lower_raw_operation(', 'pub fn lower_raw_operation_at(', 'pub fn lower_raw_with_kernel(', 'definitions: Arc<[SourceDefinition]>']),
        ('src/frontend/raw_state.rs', ['pub(crate) struct RawState', 'pub(crate) fn cnot(', 'pub(crate) fn measure_z(']),
        ('src/frontend/specialize/raw/preservation.rs', ['pub(super) fn validate_subject(', 'fn operation(', 'RawOp::ClassicalAnd', 'RawOp::ClassicalXor']),
    ], [('tests/sized_source.rs', 'untrusted_lowering_retains_source_and_rejects_unproved_effect_retiming'),
        ('tests/exclusive_access.rs', 'selected_register_access_preserves_exact_axes_and_untouched_reference'),
        ('tests/exclusive_access.rs', 'selected_register_replay_rejects_native_valid_wrong_partitions_and_axis_order'),
        ('tests/exclusive_access.rs', 'selected_generic_register_access_retains_original_static_bounds'),
        ('tests/exclusive_access.rs', 'indexed_places_retain_original_axis_and_owner_occurrences'),
        ('tests/exclusive_access.rs', 'indexed_places_check_symbolic_bounds_and_ordered_selected_types'),
        ('tests/exclusive_access.rs', 'indexed_places_refuse_unproved_bounds_overlap_and_changed_interfaces'),
        ('tests/exclusive_access.rs', 'indexed_place_obligations_cover_unused_branches_and_empty_loops'),
        ('tests/exclusive_access.rs', 'indexed_place_profiles_refuse_unconnected_lowering_explicitly'),
        ('tests/exclusive_access.rs', 'symbolic_place_overlap_requires_original_binder_guards'),
        ('tests/exclusive_access.rs', 'selected_register_access_keeps_zero_width_phase_and_inverse_axis'),
        ('tests/sized_cli.rs', 'sized_cli_emits_only_an_untrusted_proposal_without_a_kernel'),
        ('tests/selected_source_cli.rs', 'selected_open_signature_checks_and_proposals_do_not_claim_closed_execution'),
        ('tests/selected_source_cli.rs', 'selected_caller_h_request_rejects_x_once_without_a_raw_retry'),
        ('tests/ordinary_booleans.rs', 'all_four_truth_rows_match_independent_constants_in_both_profiles'),
        ('tests/ordinary_booleans.rs', 'ordinary_register_pack_rows_and_nested_copies_have_independent_ordered_results'),
        ('tests/ordinary_booleans.rs', 'zero_register_and_nat_helpers_copy_and_drop_without_quantum_owners'),
        ('tests/ordinary_booleans.rs', 'copied_measured_registers_preserve_bell_correlation_and_eager_effects'),
        ('tests/ordinary_booleans.rs', 'ordinary_basis_substitutions_keep_register_and_product_tags'),
        ('tests/ordinary_booleans.rs', 'quantum_provider_calls_retain_unused_ordinary_register_computation'),
        ('tests/ordinary_booleans.rs', 'register_type_coercions_and_quantum_copy_drop_still_reject'),
        ('tests/ordinary_booleans.rs', 'retained_register_source_rejects_another_native_accepted_artifact'),
        ('src/frontend/specialize/raw/preservation.rs', 'ordinary_register_replay_rejects_native_valid_order_and_computation_faults'),
        ('src/frontend/specialize/raw/preservation.rs', 'ordinary_register_storage_is_charged_before_emission'),
        ('tests/mixed_booleans.rs', 'pending_first_argument_keeps_entangled_owner_during_later_argument_measurement'),
        ('tests/mixed_booleans.rs', 'representable_phases_match_independent_exact_targets_and_interference'),
        ('src/frontend/specialize/raw.rs', 'raw_source_replay_rejects_native_valid_semantic_and_structural_mutations'),
        ('tests/basis_polymorphism.rs', 'all_first_opaque_rejections_reach_their_actual_rules_before_binding'),
        ('tests/checked_operations.rs', 'canonical_inverse_checks_unused_zero_count_generic_access'),
        ('tests/checked_operations.rs', 'canonical_power_zero_and_unused_still_require_apply_and_a_valid_count'),
        ('tests/checked_operations.rs', 'canonical_power_zero_evaluates_its_argument_and_bounded_counts_reject'),
        ('tests/checked_operations.rs', 'canonical_control_rejects_alias_arity_type_and_missing_access'),
        ('tests/checked_operations.rs', 'canonical_control_zero_power_evaluates_effectful_arguments_in_source_order'),
        ('tests/quantum_unit_source.rs', 'canonical_inverse_unit_scalar_retains_independent_reference_request'),
        ('tests/classical_functions.rs', 'original_meaning_request_checks_the_actual_provider_bytes_and_exact_phase'),
        ('tests/classical_functions.rs', 'finite_source_targets_preserve_product_tree_and_refuse_width_substitution'),
        ('tests/classical_functions.rs', 'source_meaning_signature_effect_and_budget_guards_precede_native_io'),
        ('tests/classical_functions.rs', 'unused_provider_leaf_checks_its_body_without_replacing_caller_identity'),
        ('tests/classical_functions.rs', 'repeated_unused_binding_checks_composite_action_and_preserves_its_original_caller'),
        ('tests/classical_functions.rs', 'repeated_scalar_binding_keeps_exact_phase_and_zero_repeat_capability_preflight'),
        ('src/frontend/specialize/raw.rs', 'source_meaning_gate_rejects_a_native_valid_replaced_provider'),
        ('src/frontend/specialize/raw.rs', 'checked_operation_bytes_are_used_by_the_actual_emitted_hierarchy'),
        ('tests/basis_polymorphism.rs', 'selected_cli_type_and_provider_bindings_are_separate_from_runtime_basis'),
        ('tests/basis_polymorphism.rs', 'same_algorithm_retains_small_reference_action_and_unit_scalar_phase'),
        ('tests/exclusive_access.rs', 'global_calls_preserve_exact_coefficient_and_external_reference'),
        ('tests/exclusive_access.rs', 'zero_width_owner_keeps_phase_and_cannot_be_duplicated'),
        ('tests/exclusive_access.rs', 'closed_static_branches_and_empty_fold_thread_updated_carry')]),
    'source-meaning-check': path_rule('native-acceptance', 'finite-leaf sized-source-proposal', '--qirf-contract', [
        ('src/frontend/specialize/raw.rs', ['pub struct SourceMeaningCheck', 'pub fn check_finite_meaning',
         'pub struct CheckedSourceMeanings', 'program.checked.interface(definition.original).statics',
         'program.meaning_targets[&id].finite(span)?', 'budget',
         'OperationSite::Step(caller, step)', 'operation.meanings.iter()',
         'lower_operation_site(source, site.clone(), depth)?',
         'finite_leaf::check_with_kernel', 'self.replay(leaf.program())?',
         'original operation binding is absent during replay',
         'accepted.artifact() != self.payload', 'self.replay(accepted)',
         'preservation::validate_subject_with_kernel(source, subject, operation, raw, Some(kernel))',
         'pub(super) fn lower_with_kernel(', 'retained.entry(definition.original).or_default().push(calls)',
         'covered &= calls.contains', 'accepted.native_exact_work()',
         'preservation::validate_subject_with_control_work(']),
        ('src/frontend/specialize/raw/preservation.rs', ['Quantum(TokenId, Arc<[WireId]>)',
         'Primitive::Split', 'Primitive::Join',
         'Raw split changes its owner or exact ordered partition',
         'Raw join changes or aliases its ordered owners',
         'register repartition changes its source owner or split axis',
         'register repartition changes or aliases its ordered owners',
         'self.control_call(step, &inputs, &output, first_instruction, site)?',
         'self.raw.operations[first..self.cursor].to_vec()',
         '.check_control_owners(&call, &signatures, &axes, self.control_work)']),
        ('src/interchange/finite_leaf.rs', ['pub(crate) fn check_with_kernel(', 'kernel.check_leaf(payload, boundary, meaning)']),
        ('src/frontend/check/body/operations.rs', ['self.obligation(span, ObligationKind::ControlSectors)?']),
        ('src/frontend/specialize/elaborate.rs', ['pub fn check_operation_meanings', 'pub(super) fn require_unrefined',
         'pub(super) fn require_control_evidence', 'checked.obligations.iter().find']),
        ('src/frontend/specialize/lower.rs', ['source.require_control_evidence()?']),
        ('src/bin/qleisli/source_plan.rs', ['source.has_operation_meanings()', '.check_operation_meanings(']),
    ], [('tests/classical_functions.rs', 'original_meaning_request_checks_the_actual_provider_bytes_and_exact_phase'),
        ('tests/classical_functions.rs', 'original_annotations_check_every_nested_and_unused_provider_before_lowering'),
        ('tests/classical_functions.rs', 'original_meaning_ids_do_not_unify_same_named_targets_in_distinct_modules'),
        ('tests/classical_functions.rs', 'nested_repeated_binding_is_compared_with_its_own_original_annotation'),
        ('tests/classical_functions.rs', 'selected_cli_checks_original_annotations_and_rejects_raw_bypass'),
        ('tests/classical_functions.rs', 'explicit_checked_op_checks_unused_and_zero_repeat_children'),
        ('tests/classical_functions.rs', 'explicit_checked_op_direct_step_and_forwarded_requests_are_not_overwritten'),
        ('tests/classical_functions.rs', 'selected_cli_checks_explicit_requests_without_a_refined_formal'),
        ('tests/classical_functions.rs', 'explicit_scalar_request_is_checked_before_adjoint_and_keeps_exact_phase'),
        ('tests/classical_functions.rs', 'packaged_product_meanings_preserve_swapped_axes_and_zero_width_factor_phase'),
        ('tests/classical_functions.rs', 'packaged_zero_and_nary_bases_keep_their_exact_native_signature'),
        ('src/frontend/specialize/raw/preservation.rs', 'packaged_product_replay_rejects_native_valid_axis_and_owner_substitutions'),
        ('tests/classical_functions.rs', 'unused_provider_leaf_checks_its_body_without_replacing_caller_identity'),
        ('src/frontend/specialize/raw.rs', 'repeated_subject_replay_rejects_its_native_valid_base_artifact'),
        ('tests/classical_functions.rs', 'source_meaning_signature_effect_and_budget_guards_precede_native_io'),
        ('src/frontend/specialize/raw.rs', 'source_meaning_gate_rejects_a_native_valid_replaced_provider'),
        ('src/frontend/specialize/elaborate.rs', 'public_source_control_roles_reach_replay_as_obligations_not_authority'),
        ('src/frontend/specialize/elaborate.rs', 'transformed_source_replay_cannot_erase_control_obligations'),
        ('tests/exclusive_access.rs', 'selected_nonexecuted_control_obligations_refuse_before_transport'),
        ('tests/exclusive_access.rs', 'selected_control_requires_checker_and_one_bounded_budget'),
        ('tests/exclusive_access.rs', 'selected_control_cannot_erase_inactive_original_calls_or_bad_zero_power_providers'),
        ('tests/exclusive_access.rs', 'selected_control_retains_exact_scalar_phase_and_diagonal_meaning'),
        ('tests/selected_source_cli.rs', 'selected_raw_control_checks_without_weakening_emission'),
        ('src/frontend/specialize/elaborate.rs', 'native_replay_checks_actual_call_sectors_instead_of_effect_annotation'),
        ('src/frontend/specialize/elaborate.rs', 'native_control_replay_checks_only_the_consumed_call_and_has_no_fallback'),
        ('src/frontend/specialize/elaborate.rs', 'native_replay_refuses_h_on_control_and_preserves_unit_scalar_phase')]),
    'checked-views': path_rule('checked-view', 'contract function named-qpe-components', '', [
        ('src/contract/mod.rs', ['pub fn check_binding(', 'pub fn check_entry(']),
        ('src/contract/function.rs', ['pub fn check_binding(']),
        ('src/interchange/hierarchical.rs', ['pub fn instrument(', 'pub fn candidate(']),
    ], [('tests/function_evidence.rs', 'checks_two_raw_functions_and_retains_their_full_snapshots')]),
    'finite-component': path_rule('lean-component', 'lean-finite-component-v024', '', [
        ('lean-kernel/QleisliKernel/Finite.lean', ['def check ', 'def checkAll ']),
        ('lean-kernel/Protocol/FiniteCodec.lean', ['def readMatrix ']),
    ], [('tests/semantic_contracts.rs', 'primitive_evidence_preserves_exact_phase')]),
    'phase-components': path_rule('lean-component', 'native-components', '', [
        ('lean-kernel/Cli/Finite.lean', ['def run ', 'def runDag ', 'def runLayout ', 'def runLayoutDag ', 'def runPhaseLayout ']),
    ], [('tests/hierarchical_host.rs', 'native_request_binds_reindexed_shared_powers_and_exact_meaning_bytes')]),
}

# Each dedicated hierarchy protocol has its own request, checker and result;
# none is silently covered by the QLV1 ordinary-root theorem.
for _id, _boundaries, _mode, _method, _cli, _check, _test in [
    ('hierarchy-inspect', 'hierarchy-inspect', '--hierarchy-pending', 'inspect_native', 'runHierarchy', 'Hierarchical.Conditional.checkAll', ('tests/hierarchical_host.rs', 'native_request_binds_reindexed_shared_powers_and_exact_meaning_bytes')),
    ('hierarchy-request', 'hierarchy-inspect sized-source-proposal', '--hierarchy-request-pending', 'check_against_native', 'runHierarchyRequest', 'Hierarchical.Root.checkAll', ('tests/hierarchical_host.rs', 'native_request_binds_reindexed_shared_powers_and_exact_meaning_bytes')),
    ('hierarchy-fourier', 'hierarchy-inspect sized-source-proposal', '--hierarchy-fourier-pending', 'check_against_native', 'runHierarchyFourier', 'Hierarchical.FourierRoot.checkAll', ('tests/sized_source.rs', 'reordered_fourier_roots_and_inverses_preserve_native_phase_and_reference')),
    ('hierarchy-instrument', 'instrument-composition sized-source-proposal', '--instrument-pending', 'check_instrument_native', 'runInstrument', 'Hierarchical.Instrument.checkAll', ('tests/hierarchical_host.rs', 'native_instrument_binds_all_stages_and_reconstructs_finite_obligations')),
    ('hierarchy-qpe', 'named-qpe-components sized-source-proposal', '--qpe-instrument-pending', 'check_qpe_instrument_native', 'runQpeInstrument', 'Hierarchical.QpeInstrument.checkAll', ('tests/hierarchical_qpe_host.rs', 'native_qpe_instrument_binds_provider_phase_hadamards_and_all_boundaries')),
]:
    PATHS[_id] = path_rule('native-hierarchy-check', _boundaries, _mode, [
        ('src/interchange/hierarchical.rs', [f'pub fn {_method}(', 'pub struct NativeChecked']),
        ('src/interchange/hierarchical/runtime.rs', [f'"{_mode}"']),
        ('lean-kernel/Cli/Hierarchical.lean', [f'def {_cli} ', _check, 'Protocol.HierarchicalFinite.checkLeaves']),
        ('lean/Qleisli/NativeHierarchy.lean', ['theorem checkLeaves_semantics']),
    ], [_test])

NATIVE_DISPATCH = {
    '--qirf-native': 'QleisliKernel.Cli.runValidity',
    '--qirf-contract': '(QleisliKernel.Cli.runValidity true)',
    '--hierarchy-pending': 'QleisliKernel.Cli.runHierarchy',
    '--hierarchy-request-pending': 'QleisliKernel.Cli.runHierarchyRequest',
    '--hierarchy-fourier-pending': 'QleisliKernel.Cli.runHierarchyFourier',
    '--instrument-pending': 'QleisliKernel.Cli.runInstrument',
    '--qpe-instrument-pending': 'QleisliKernel.Cli.runQpeInstrument',
    '--readout-check': 'QleisliKernel.Cli.runReadout',
    '--preparation-check': 'QleisliKernel.Cli.runPreparation',
}
for _id, _mode, _parser, _check, _test in [
    ('readout-component', '--readout-check', 'parseReadout', 'Readout.check', ('scripts/test_hierarchical_readout.py', 'test_native_branches')),
    ('preparation-component', '--preparation-check', 'parsePreparation', 'Preparation.check', ('scripts/test_hierarchical_preparation.py', 'test_zero_reference')),
]:
    PATHS[_id] = path_rule('lean-component', _id, _mode, [
        ('lean-kernel/Cli/Hierarchical.lean', [f'Protocol.Hierarchical.{_parser}', f'Hierarchical.{_check}']),
    ], [_test])


def boundary_paths(boundary):
    return sorted(name for name, rule in PATHS.items() if boundary in rule['boundaries'])


def boundary_status(boundary):
    categories = {PATHS[name]['classification'] for name in boundary_paths(boundary)}
    statuses = {'native-execution' if category in {'native-acceptance', 'native-hierarchy-check'} else
                'lean-component' if category == 'lean-component' else 'untrusted-host'
                for category in categories}
    return next(iter(statuses)) if len(statuses) == 1 else 'mixed-boundary'


# Reviewed routes; source loading and simulation cannot mint accepted handles.
ROUTES = {'raw': ('tests/native_paths.rs', 'raw_exports_conversions_and_native_reports_share_the_original_byte_gate'), 'contract': ('tests/semantic_contracts.rs', 'primitive_evidence_preserves_exact_phase'), 'function': ('tests/function_evidence.rs', 'checks_two_raw_functions_and_retains_their_full_snapshots'), 'qirf': ('tests/native_paths.rs', 'raw_exports_conversions_and_native_reports_share_the_original_byte_gate'), 'finite-leaf': ('tests/finite_leaf.rs', 'reconstruct_hadamard_in_both_formats_and_bind_complete_bytes'), 'source': ('scripts/test_source_kernel.py', 'test_unused_body_native_rejection_blocks_every_source_action'), 'foreign': ('scripts/test_interop_native.py', 'test_all_actions_formats_use_real_native_checker'), 'native-components': ('tests/hierarchical_host.rs', 'native_request_binds_reindexed_shared_powers_and_exact_meaning_bytes'), 'hierarchy-inspect': ('tests/hierarchical_host.rs', 'native_request_binds_reindexed_shared_powers_and_exact_meaning_bytes'), 'execution': ('tests/sampling.rs', 'stochastic_samples_match_independent_bell_and_reset_feedback_contracts'), 'readout-component': ('scripts/test_hierarchical_readout.py', 'test_native_branches'), 'preparation-component': ('scripts/test_hierarchical_preparation.py', 'test_zero_reference'), 'instrument-composition': ('tests/hierarchical_host.rs', 'native_instrument_binds_all_stages_and_reconstructs_finite_obligations'), 'hierarchy-execution': ('tests/hierarchical_execution.rs', 'small_source_clients_match_independent_complex_reference_branches'), 'sized-source-proposal': ('tests/sized_source.rs', 'rust_source_proposals_check_natively_and_preserve_small_system_coefficients'), 'named-qpe-components': ('tests/hierarchical_qpe_host.rs', 'native_qpe_instrument_binds_provider_phase_hadamards_and_all_boundaries'), 'source-edition-configuration': ('tests/review_v021.rs', 'grouped_imports_expand_to_existing_leaves_with_docs_spans_and_resolution'), 'lean-finite-component-v024': ('tests/semantic_contracts.rs', 'primitive_evidence_preserves_exact_phase'), 'qirf-native-v028': ('tests/native_paths.rs', 'native_report_retains_the_exact_artifact_request_and_reconstructed_program'), 'qirf-native-v029': ('tests/native_acceptance.rs', 'native_handles_execute_bell_and_feedback_without_legacy_receipts')}


def surface_identity(inventory):
    # Include full hashes where the bounded Rust signature scanner does not
    # describe public interfaces (CLI/Python/Lean). No changed path is inferred
    # covered just because another API uses the same implementation.
    value = {key: inventory[key] for key in ('enums', 'boundaries', 'capacities')}
    value['sources'] = [{key: row[key] for key in ('path', 'group', 'surface')} |
                        ({} if row['surface'] and row['surface']['functions'] else {'sha256': row['sha256']})
                        for row in inventory['sources']]
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def check(root, data=None, inventory=None):
    data = json.loads((root/COVERAGE).read_text()) if data is None else data
    inventory = json.loads((root/INVENTORY).read_text()) if inventory is None else inventory
    def require(value, message):
        if not value:
            raise ValueError(message)
    require(data['format'] == 'qleisli.vm29-coverage' and data['version'] == 2, 'unknown coverage format')
    require(data['authority'] == 'Lean' and data['external_schemas_enabled'] is False,
            'production acceptance is Lean-only; schemas remain disabled')
    require(data['migration'] == {
        'decision': 'https://github.com/MGYamada/Qleisli/issues/276',
        'target_version': '0.2.9', 'target_authority': 'Lean',
        'status': 'single-lean-acceptance-implemented', 'soundness_target': '0.5.0',
        'cutover_criteria': sorted(CUTOVER),
    }, 'unreviewed migration decision or completion claim')
    publication = json.loads((root/PUBLICATION).read_text())
    require(publication['release'] == '0.2.9' and publication['status'] == 'published and verified'
            and publication['source']['commit'] == PUBLISHED_COMMIT,
            'published baseline no longer matches its immutable release record')
    product_version = tomllib.loads((root/'Cargo.toml').read_text())['package']['version']
    require(data['validation'] == {
        'published_baseline': dict(version='0.2.9', status='published and verified',
                                   record=PUBLICATION, source_commit=PUBLISHED_COMMIT),
        'current_development': dict(version=product_version, status='unpublished',
                                    validation='separate current-tree checks; no inherited release certification'),
        'proof_status': 'S05-C1-C5 open; no constitutional guarantee discharged by this inventory',
    }, 'publication, current development and proof status must remain separate')
    require(data['surface_sha256'] == surface_identity(inventory), 'public surface changed; review VM29 coverage')
    groups = {g['id'] for g in inventory['groups']}
    rows = data['groups']
    require(len(rows) == len(groups) and {r['id'] for r in rows} == groups, 'missing, duplicate or extra coverage group')
    boundaries = {b['id']: b for b in inventory['boundaries']}
    entries = data['boundaries']
    require(len(entries) == len(boundaries) and {r['id'] for r in entries} == set(boundaries), 'missing, duplicate or extra public boundary')
    for row in rows + entries:
        require(row['status'] in {'untrusted-host', 'lean-component', 'native-execution', 'mixed-boundary'}, 'unknown migration status')
        require(isinstance(row['blocker'], str) and row['blocker'].strip(), 'missing explicit migration blocker')
        require(set(row['proof_gates']) == GATES, 'incomplete proof obligations')
        require(set(row['cutover_gates']) == CUTOVER, 'incomplete legacy-removal criteria')
        require(bool(row['evidence']), 'missing coverage evidence')
        for name in row['evidence']:
            path = (root/name).resolve()
            require(path.is_relative_to(root.resolve()) and path.is_file() and 'docs-old' not in path.parts,
                    'missing or retired coverage evidence: ' + name)
    require(set(ROUTES) == set(boundaries), 'unreviewed public boundary route')
    require({boundary for rule in PATHS.values() for boundary in rule['boundaries']} == set(boundaries),
            'public boundary missing detailed route classification')
    paths = data['paths']
    require(len(paths) == len(PATHS) and {row['id'] for row in paths} == set(PATHS),
            'missing, duplicate or extra production path')
    for row in paths:
        rule = PATHS[row['id']]
        require({key: row[key] for key in rule} == rule, 'unreviewed production path classification or binding: ' + row['id'])
        for key in ('entry_path', 'checked_artifact', 'checker', 'proof_scope', 'gaps'):
            require(isinstance(row.get(key), str) and row[key].strip(), 'missing production path scope: ' + row['id'])
        if row['id'] == 'contract-acceptance':
            require({key: row[key] for key in CONTRACT_PROOF} == CONTRACT_PROOF,
                    'unreviewed native-contract proof scope')
        for source in rule['source_bindings']:
            path = root/source['path']
            require(path.is_file(), 'missing production source: ' + source['path'])
            text = path.read_text()
            require(all(marker in text for marker in source['markers']),
                    'production source binding changed: ' + source['path'])
        for test in rule['tests']:
            require((root/test['path']).is_file() and test['test'] in test_names(root/test['path']),
                    'missing production path regression: ' + test['path'] + ':' + test['test'])
    # The entire explicit native dispatch list must be accounted for. Unknown
    # additions and removals fail even when no public boundary changed yet.
    main = (root/'lean-kernel/Main.lean').read_text()
    require('private def nativeMode ' in main and '\ndef main ' in main,
            'unreviewed native dispatch structure')
    dispatch = main.split('private def nativeMode ', 1)[1].split('\ndef main ', 1)[0]
    modes = re.findall(r'^\s*\| "(--[^"\n]+)" => ([^\n]+)', dispatch, re.M)
    reviewed_modes = [mode for rule in PATHS.values() for mode in rule['native_modes']]
    require(len(modes) == len(dict(modes))
            and dict(modes) == {mode: 'some ' + handler for mode, handler in NATIVE_DISPATCH.items()}
            and set(dict(modes)) == set(reviewed_modes),
            'unreviewed native mode coverage')
    for row in entries:
        require(row['entry_points'] == boundaries[row['id']]['entry_points'], 'unreviewed public entry point')
        route = ROUTES[row['id']]
        require(row['status'] == boundary_status(row['id']) and row['paths'] == boundary_paths(row['id']),
                'reviewed selected route was omitted or misclassified')
        require(row.get('selection') and row.get('legacy') == 'removed; no Rust acceptance fallback', 'selection/removal scope must be explicit')
        require(row.get('route_test') == dict(path=route[0], test=route[1]), 'unreviewed selected-path regression')
        require(route[1] in test_names(root/route[0]), 'missing selected-path regression')
    require(not (root/'src/verify.rs').exists() and not (root/'src/interchange/dual.rs').exists(),
            'retired Rust acceptance implementation remains')
    require({g['id'] for g in data['gates']} == GATES and len(data['gates']) == len(GATES), 'missing transfer gate')
    require(all(g['status'] == 'open' and g['acceptance'].strip() for g in data['gates']),
            'gate closure needs proof/specification review, not a metadata edit')
    return dict(groups=len(rows), public_boundaries=len(entries),
                public_source_files=sum(bool(s['surface']) for s in inventory['sources']),
                constructor_variants=sum(len(e['members']) for e in inventory['enums']),
                authority='Lean', migration=data['migration']['status'], target_authority='Lean',
                production_paths=len(paths), native_modes=len(modes),
                published_baseline='0.2.9', development_version=product_version,
                development_status='unpublished',
                open_gates=sorted(GATES))


def main():
    try:
        print(json.dumps(check(ROOT), indent=2))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
