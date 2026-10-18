#!/usr/bin/env python3
"""Check reviewed production routes and historical release binding, not soundness.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
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
        'ExecutionView.Native.contract_binding connects the actual QLV2 entry to its selected original/compare gate. '
        'CheckedContract and CheckedCaller bind typed requests, both retained roots and caller caches to exact QDV1 comparisons. '
        'Protocol.NativeContract.check_acceptance binds original QLV1 body/request bytes, decoded '
        'artifact and request, and continuous checking states. Qleisli.NativeContract.check_root_meaning '
        'and check_sound establish RootMeaning for all request kinds. For leaf requests, leaf_meaning '
        'establishes original-body instrument meaning for the bounded closed unitary fragment, exact '
        'requested matrix/signature/ordered ports, and an actual verification of the output port; '
        'leaf_reference_laws extends both whole-space inverse laws to any finite reference. '
        'For pure-leaf requests, pure_leaf_meaning binds the original body, dependency graph, '
        'separate exact domain/codomain, ordered ports, requested matrix and exact Gram identity; '
        'pure_leaf_reference preserves inner products with arbitrary joint reference amplitudes. '
        'Ordinary and selected Raw adapters check actual emitted intervals against these requests; '
        'private original-body/source records grant neither an inverse API nor a source-preservation proof. '
        'For encoded requests, check_encoded_sound and encoded_meaning bind the original root BodyMeaning, '
        'exact Basis interface and Encoded equation; Wrapper.circuitMatrix_entries proves actual wrapper '
        'coefficients equal the original reconstructed matrix, including zero-width phase and axis order. '
        'encoded_reference extends the equation to every reference amplitude function. '
        'For control requests, ControlAcceptance binds decoded signature/axes to the reconstructed original '
        'action; control_meaning establishes original BodyMeaning, exact interface, unitarity and '
        'sector preservation. control_reference proves projector commutation for every joint amplitude '
        'and arbitrary reference. Finite project and supported selected Raw ctrl calls bind fresh native '
        'decisions to actual emitted call intervals and original ordered owner interfaces; general source '
        'preservation, unsupported hierarchy/operator cases and wider alias/resource obligations remain open. '
        'For instrument requests, instrument_meaning binds both original QIRF roots and dependency graphs, '
        'complete Kraus sums, untruncated dimensions and requested complete signature equality to exact '
        'unnormalized public outcome maps on every joint matrix and finite external reference. '
        'A private Rust paired handle retains original accepted artifacts, complete types and source identity. '
        'Both concrete observing adapters freshly check actual emitted intervals and retain private '
        'pair/call sidecars without changing whole-root request disclosure. Selected Raw replay checks '
        'the original implementation, input owner and ordered result before a fresh native equation; '
        'hierarchy and checker-free lowering refuse these calls. Full source preservation remains open.'
    ),
    'gaps': (
        'This separate protocol does not inherit NativeValidity.check_sound. General EffectSound/CPTP, source/compiler '
        'preservation, deployed-binary correspondence, Rust rematerialization, target/runtime preservation, '
        'clean-release and quantitative RS claims remain separate. These bridge theorems are not a new '
        'guarantee admission or S05 closure.'
    ),
}
ENGINEERING_PURE_PROOF = {
    'proof_scope': (
        'CheckedEngineeringPure.run_binding retains the actual QLV2 execution packet, the original QLV1 '
        'body/request bytes, both freshly decoded graphs and the exact QDV1 comparison. '
        'Protocol.EngineeringPure.checkRetained_bound connects those decoded fields to one shared-work '
        'engineering computation. NativeEngineeringPureProtocol.run_meaning and run_reference_square '
        'bind both original pure bodies, their own independent exact matrix equations and Gram checks '
        'to the phase-sensitive Euclidean operator inequality on every finite joint reference input. '
        'The sufficient witness is a bounded exact R8 Frobenius-square comparison. Separate pure '
        'composition lemmas require their stated isometry and ordered-interface premises; the native '
        'request profile remains single-component-v1. The private Rust engineering report retains '
        'both original artifacts, request bytes and selected checker path, and grants no exact '
        'cross-body equation or accepted-program conversion, including at epsilon zero.'
    ),
    'gaps': (
        'This is an engineering check, not exact source correspondence, an inverse/control capability, '
        'cleanup evidence, an instrument bound, a target resource certificate or a constitutional '
        'guarantee admission. qirf-r8-pure-v1 names an IR profile, not a physical target. Source/compiler, '
        'decoder/walker, deployed-binary/native-compiler and runtime preservation remain separate. '
        'The selected checker path is not binary attestation. Native composition, instrument metrics, '
        'actual emitted-resource binding and separate sampling/algorithmic/numerical error claims '
        'remain open. This path does not inherit NativeValidity.check_sound or close S05-C1-C5, '
        'QS, PR, RS or EXACT obligations.'
    ),
}
ENGINEERING_INSTRUMENT_PROOF = {
    'proof_scope': (
        'CheckedEngineeringInstrument.run_binding and Native.engineeringInstrument_binding retain the actual '
        'QLV2 execution packet, original QLV1 body/request bytes, both freshly decoded graphs, full typed '
        'request and exact QDV1 comparison. Protocol.EngineeringInstrument.checkRetained_bound connects '
        'them to one continuous-work engineering check. NativeEngineeringInstrumentProtocol.run_meaning '
        'binds both original bodies/dependencies, exact Kraus completeness, untruncated dimensions, complete '
        'signature equality and ordered public-output projections to CompleteAdjointBound on every finite '
        'joint reference and every public-outcome observable family. The sufficient exact R8 Choi coefficient '
        'majorants retain all unnormalized hidden histories and residual coherences; no probability-only or '
        'postselected comparison is used. Separate internal mathematical lemmas derive complete adjoint '
        'contraction from full Kraus Gram equations, pure-to-instrument 2-delta bounds from literal pure '
        'gaps and both isometry equations, and additive feed-forward/ordered tensor bounds with explicit '
        'reference-axis regrouping. Their complete component Gram and interface premises remain explicit. '
        'The native profile remains single-component-v1. Private Rust reports retain both original artifacts, '
        'request bytes and selected checker path; epsilon zero grants no exact accepted-program conversion.'
    ),
    'gaps': (
        'This engineering instrument check grants no exact source correspondence, pure phase agreement, '
        'inverse/control capability, cleanup, target-resource certificate or constitutional guarantee. '
        'qirf-r8-instrument-v1 is an IR profile, not a hardware realization. Independent composition lemmas '
        'do not establish original source/QIRF feed-forward or tensor preservation, native composed '
        'certificate generation/consumption or actual emitted-resource binding. Source/compiler, decoder/walker, '
        'native-compiler/deployed-binary and runtime preservation remain separate; checker-path retention '
        'is not binary attestation. Sampling, algorithmic-resolution and numerical-runtime error categories '
        'are not claimed. Exact InstrumentContract acceptance remains separate and unchanged. This route '
        'does not inherit NativeValidity.check_sound or close S05-C1-C5, QS, PR, RS or EXACT obligations.'
    ),
}

ENGINEERING_PURE_TENSOR_PROOF = {
    'proof_scope': (
        'CheckedEngineeringPureTensor.run_binding retains the actual execution-only QLV2 packet, '
        'original parent body/request bytes and exact QDV1 comparison of the typed context and six '
        'freshly decoded graphs. Protocol.EngineeringPureTensor.checkRetained_bound connects these '
        'fields to one continuous-work core execution. NativeEngineeringPureTensor.check_meaning '
        'binds all six original bodies/dependencies, complete ordered type trees, exact matrix and '
        'Gram equations, both independently computed low-first parent tensors and canonical additive '
        'component budgets. NativeEngineeringPureTensorProtocol.run_meaning and run_reference_bound '
        'connect the actual native computation to the literal parent Euclidean operator bound for '
        'every finite external reference. The explicit total budget equals the checked sum; no '
        'whole-parent Frobenius inequality replaces composition. The private immutable Rust report '
        'retains all six artifacts, request and selected checker path, including at epsilon zero.'
    ),
    'gaps': (
        'Engineering-only ordered two-component tensor comparison; no exact cross-parent Meaning, '
        'accepted-program conversion, inverse/control access, cleanup, instrument bound, actual '
        'emitted-target/resource certificate or constitutional admission. Recursive/sequential/control '
        'and instrument native composition, source/compiler and emitted-target preservation, '
        'decoder/walker, native-compiler/deployed-binary and runtime correspondence remain separate. '
        'The IR target profile is not hardware and checker-path retention is not binary attestation. '
        'Sampling/algorithmic-resolution/numerical-runtime error categories remain unclaimed. This '
        'route does not inherit NativeValidity.check_sound or close S05-C1-C5, QS, PR, RS or EXACT.'
    ),
}


ENGINEERING_OPENQASM_PROOF = {'proof_scope': 'CheckedEngineeringOpenQasm.run_binding retains the actual execution-only QLV2 packet, '
                'original target body/request bytes and exact QDV1 comparison of the full typed context, '
                'literal target bytes, independently decoded ordered word, generated actual graph and '
                'freshly decoded ideal graph. Protocol.EngineeringOpenQasm.checkRetained_bound connects the '
                'original ideal read and target core to one continuous-work computation. '
                'Target.CanonicalOpenQasm.decode_original binds the literal target bytes; the independent '
                'Semantics.CanonicalTerminalQasm mapping retains and explicitly consumes the zero-width Unit '
                'owner. CanonicalOpenQasmGates.gate_matrix and gate_meaning bind all eight literal complex '
                'gate matrices before observation. NativeEngineeringOpenQasm.check_meaning and '
                'NativeEngineeringOpenQasmProtocol.run_meaning/run_complete_adjoint_bound bind both actual '
                'original bodies/dependencies, exact Kraus completeness, full Unit -> classical Bit '
                'signatures and ordered public outcomes to CompleteAdjointBound on every finite reference '
                "and observable at the caller's literal epsilon. The immutable private Rust report retains "
                'original target, ideal, request and selected checker path without an accepted-program '
                'conversion, including at epsilon zero.',
 'gaps': 'Engineering-only canonical closed one-qubit target profile; the declared standard-gate '
         'mathematical meaning is an explicit specification assumption. This checks the target-bound '
         'complete-adjoint relation, not source/export preservation, exact source correspondence, general '
         'OpenQASM, hardware, coherent control/inverse, cleanup, target resources or constitutional '
         'admission. Composition and synthesis/resource certificates, source/compiler/export correctness, '
         'decoder/walker/native-compiler/deployed-binary/runtime correspondence remain separate. '
         'Checker-path retention is not binary attestation. Sampling, algorithmic-resolution and '
         'numerical-runtime errors are not claimed. This route does not inherit NativeValidity.check_sound '
         'or close S05-C1-C5, QS, PR, RS or EXACT obligations.'}


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
        ('src/interchange/pure_leaf.rs', ['pub struct PureBoundary']),
        ('src/interchange/finite_matrix.rs', ['pub fn encode(', 'pub fn decode(']),
    ], [('tests/semantic_contracts.rs', 'primitive_evidence_preserves_exact_phase')]),
    'ordinary-acceptance': path_rule('native-acceptance',
        'raw function qirf source foreign qirf-native-v028 qirf-native-v029', '--qirf-native', [
        ('src/interchange/native.rs', ['pub fn accept(', 'pub fn inspect(', '"--qirf-native"']),
        ('src/contract/function.rs', ['pub fn check(', '.function_evidence(']),
        ('src/contract/meaning.rs', ['pub fn check(', 'FunctionEvidence::']),
        ('src/frontend/compile/mod.rs', ['pub fn compile_project_with_kernel(', 'pub fn check_project_with_kernel(']),
        ('src/frontend/compile/lower/function_contract.rs', ['fn function_contract_evidence(', 'FunctionEvidence::check_retained_with_kernel']),
        ('src/bin/qleisli/source_plan.rs', ['fn raw_execute(', 'native::Kernel::new(kernel).accept(proposal.proposal())', 'proposal.validate_source_steps(&checked)']),
        ('src/interchange/mod.rs', ['pub fn import(', 'pub fn convert(']),
        ('src/interop/openqasm.rs', ['pub fn import_openqasm3_with_kernel(']),
        ('lean-kernel/Cli/Validity.lean', ['Native.ordinary bytes']),
        ('lean-kernel/Protocol/ExecutionView/Native.lean', ['def ordinary ', 'theorem ordinary_original', 'theorem ordinary_root_safe']),
        ('src/interchange/native/binding.rs', ['fn check_bound(', 'prepared.bind(native)', 'Self::submit_subject']),
        ('lean-kernel/Protocol/Validity.lean', ['def check ', 'theorem check_acceptance', 'theorem check_ownershipSafe']),
        ('lean/Qleisli/NativeValidity.lean', ['theorem check_sound', 'theorem check_scopeSafe']),
    ], [('tests/native_paths.rs', 'native_report_retains_the_exact_artifact_request_and_reconstructed_program'),
        ('tests/function_evidence.rs', 'checks_two_raw_functions_and_retains_their_full_snapshots'),
        ('tests/selected_function_contracts.rs', 'unused_generic_body_keeps_its_closed_function_contract_in_both_adapters'),
        ('tests/selected_function_contracts.rs', 'declared_finite_meaning_keeps_its_request_on_both_adapters'),
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
        ('src/interchange/native/contracts.rs', ['fn check_encoded(', 'fn check_leaf(', 'fn check_pure_leaf(', 'fn check_instrument(', '"--qirf-contract"']),
        ('src/interchange/pure_leaf.rs', ['pub struct CheckedPureLeaf', 'pub fn check_pure(',
         'pub struct SourcePureEquation', 'kernel.check_pure_leaf(payload, boundary, meaning)?']),
        ('src/frontend/compile/operations/pure.rs', ['fn pure_provider_program(', 'SourcePureEquation::bind(',
         'crate::frontend::pure::check(']),
        ('src/frontend/compile/lower/operations.rs', ['fn apply_operation(', 'self.raw.operations[start..].to_vec()',
         'crate::frontend::pure::check(']),
        ('src/frontend/specialize/raw/preservation.rs', ['fn meaning_interval(', 'pure_leaf::check_with_kernel(']),
        ('lean-kernel/QleisliKernel/Qirf/PureLeaf.lean', ['def check ', 'Raw.BranchFunction.reconstruct',
         'Exact.Matrix.isometryWork actual', 'theorem check_postcondition']),
        ('lean/Qleisli/NativePureLeaf.lean', ['theorem pure_leaf_meaning', 'theorem pure_leaf_reference']),
        ('src/contract/instrument.rs', ['struct InstrumentEvidence ', 'struct InstrumentCall ', 'fn check_call(',
         'implementation.artifact()', 'specification.artifact()']),
        ('src/frontend/instrument.rs', ['fn signature<N>', 'ResultAtom::Quantum', 'signature.validate(budget)']),
        ('src/frontend/compile/lower/function_contract.rs', ['fn apply_instrument_contract(',
         'self.raw.operations[first..].to_vec()', '.check_call(', 'fn instrument_contract_evidence(']),
        ('src/frontend/specialize/raw/contracts.rs', ['fn instrument_pair(', 'fn provider_accepted(',
         'InstrumentEvidence::check(', 'retain_instrument_calls(']),
        ('src/frontend/specialize/raw/preservation.rs', ['fn instrument_call(', '.check_call(',
         'self.raw.operations[first..self.cursor].to_vec()', 'fn check_subject_with_meanings(']),
        ('src/frontend/specialize/raw.rs', ['instrument_calls:', 'preservation::check_subject_with_meanings(']),
        ('src/interchange/native.rs', ['source_instruments:', 'source_instrument_calls:', 'fn retain_instruments(', 'fn retain_instrument_calls(']),
        ('lean-kernel/Cli/Validity.lean', ['Native.contract bytes']),
        ('lean-kernel/Protocol/ExecutionView/Native.lean', ['def contract ', 'theorem contract_binding']),
        ('lean-kernel/Protocol/NativeContract.lean', ['def check ', 'def checkRetained ',
         'inductive RequestRetained ', 'theorem check_projection', 'theorem checkRetained_acceptance',
         'QleisliKernel.Qirf.checkContractRetained',
         'QleisliKernel.Qirf.check ', 'structure Acceptance ', 'structure LeafAcceptance ',
         'structure ControlAcceptance ', 'QleisliKernel.Qirf.ControlAccess.check', 'theorem check_acceptance']),
        ('lean-kernel/Protocol/InstrumentContract.lean', ['def decode ', 'def check ', 'def checkRetained ',
         'structure Retained ', 'theorem check_projection', 'theorem checkRetained_bound', 'structure Acceptance ',
         'expectedText.toUTF8', 'theorem check_acceptance']),
        ('lean-kernel/QleisliKernel/Qirf/InstrumentContract.lean', ['def interface ', 'def check ',
         'Validity.checkRoot actual actualOrder', 'Validity.checkRoot expected expectedOrder',
         'Raw.InstrumentEquality.compare', 'theorem check_acceptance']),
        ('lean-kernel/QleisliKernel/Qirf/Contract.lean', ['def checkContractRetained ',
         'theorem checkContract_projection', 'theorem checkContractRetained_bound', 'theorem checkContract_bound']),
        ('lean-kernel/QleisliKernel/Qirf/ControlAccess.lean', ['def checkRetained ', 'def checkOwnersRetained ',
         'theorem check_projection', 'theorem checkOwners_projection',
         'theorem checkRetained_bound', 'theorem checkOwnersRetained_bound']),
        ('lean/Qleisli/Qirf.lean', ['theorem reconstruct_semantics', 'theorem check_semantics']),
        ('lean/Qleisli/NativeContract.lean', ['structure LeafMeaning ', 'theorem check_root_meaning',
         'theorem leaf_meaning', 'theorem leaf_reference_laws', 'theorem check_sound',
         'structure EncodedMeaning ', 'theorem encoded_meaning', 'theorem check_encoded_sound',
         'theorem encoded_reference', 'structure ControlMeaning ', 'theorem control_meaning',
         'theorem control_reference', 'structure InstrumentMeaning ', 'theorem instrument_meaning']),
        ('lean/Qleisli/QirfInstrumentContract.lean', ['theorem reconstruct_denotes',
         'theorem reconstruct_kraus_complete', 'theorem check_dimensions', 'theorem check_instrument']),
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
        ('tests/pure_leaf.rs', 'original_preparation_and_complete_receipt_binding'),
        ('tests/pure_leaf.rs', 'observation_cannot_be_hidden_behind_pure_effects_or_unreturned_results'),
        ('tests/pure_leaf.rs', 'fresh_dependency_body_check_rejects_substitution_and_stale_evidence'),
        ('tests/rectangular_meanings.rs', 'rectangular_composition_preserves_an_entangled_caller'),
        ('tests/rectangular_meanings.rs', 'ordinary_project_equal_width_distinct_trees_and_inverse'),
        ('scripts/test_native_verification.py', 'test_control_requests'),
        ('scripts/test_native_verification.py', 'test_instrument_requests'),
        ('src/contract/instrument.rs', 'instrument_receipts_bind_original_bytes_and_fresh_call_decisions'),
        ('src/contract/instrument.rs', 'instrument_signature_preflights_frontiers_depth_and_zero_width_types'),
        ('tests/function_contracts.rs', 'observing_contracts_compare_complete_instruments_on_the_emitted_call'),
        ('tests/function_contracts.rs', 'observing_contracts_reject_public_relabeling_and_wrong_residual_channels'),
        ('tests/function_contracts.rs', 'observing_contracts_check_nested_calls_branches_and_hidden_discard_histories'),
        ('tests/selected_function_contracts.rs', 'observing_specialization_checks_calls_and_unused_original_obligations'),
        ('tests/selected_function_contracts.rs', 'observing_specialization_keeps_nested_equations_empty_values_and_references'),
        ('tests/selected_function_contracts.rs', 'observing_specialization_rechecks_changed_reference_dependencies_and_output_order'),
        ('src/frontend/specialize/raw/preservation.rs', 'observing_replay_rejects_native_valid_rewrites_and_rechecks_actual_calls'),
        ('tests/reference_meanings.rs', 'fixed_fourier_reference_meanings_match_independent_exact_coefficients')]),
    'source-documentation': path_rule('documentation', 'source', '', [
        ('src/bin/qleisli.rs', ['if options.command == "doc"', 'render_markdown(&source)']),
        ('src/frontend/documentation.rs', ['pub fn render_markdown(']),
    ], [('tests/cli.rs', 'doc_reads_one_file_and_does_not_claim_type_checking')]),
    'foreign-export': path_rule('host-transformation', 'foreign', '', [
        ('src/interop/mod.rs', ['pub fn export_openqasm3(program: &AcceptedProgram)', 'pub fn export_qir_base(program: &AcceptedProgram)']),
        ('src/interop/profile.rs', ['pub(super) fn extract(', 'ExpansionBudget::for_program(program)',
         'super::export::steps(', '&mut expansion']),
        ('src/interop/export.rs', ['pub(super) fn steps(',
         'contracts::Cursor::new(steps, wires.len(), expansion)?', 'step(circuit, scratch, &merged, wires)?']),
        ('src/interop/export/contracts.rs', ['pub(in crate::interop) struct ExpansionBudget', 'fn reserve(',
         'evidence.expanded_steps()', 'budget.reserve(steps)?', 'body: evidence.circuit().steps()',
         'inverse: frame.inverse ^ *adjoint', 'crate::contract::invert_steps(']),
        ('src/interop/export/normalization.rs', ['program.kernel()',
         'FunctionEvidence::check_retained_with_kernel(', 'equation.signature() == &signature',
         'equation.implementation() == &original', 'equation.specification() == &proposed',
         'work: Budget::new(DEFAULT_EXACT_WORK),', 'const MAX_LOCAL_EQUATIONS: usize = 7;',
         'fn candidate(', 'first.controls != middle.controls', 'phases != &[0, 4]']),
    ], [('scripts/test_interop_native.py', 'test_all_actions_formats_use_real_native_checker'),
        ('tests/interop.rs', 'ordinary_contract_export_preserves_t_phase_and_nested_adjoint'),
        ('tests/interop.rs', 'ordinary_contract_export_keeps_reference_axes_and_reordered_owners'),
        ('tests/interop.rs', 'controlled_ordinary_contract_export_returns_scratch_exactly'),
        ('tests/interop.rs', 'adjacent_contract_phases_merge_before_assigning_workspace'),
        ('tests/interop.rs', 'uncontrolled_unit_contract_phase_is_not_erased_by_export'),
        ('tests/interop.rs', 'ordinary_contract_adjoint_reverses_noncommuting_body_order'),
        ('src/interop/export/contracts.rs', 'expansion_reservation_is_shared_across_raw_operations'),
        ('src/interop/export/contracts.rs', 'malformed_mapping_of_checked_dependency_returns_an_error'),
        ('src/interop/export/normalization.rs', 'candidate_requires_exact_adjacent_phase_target_and_ordered_controls'),
        ('src/interop/export/normalization.rs', 'equation_failure_keeps_the_original_window_and_shared_budget'),
        ('src/interop/export/normalization.rs', 'existing_native_equation_refuses_wrong_phase_or_control_subjects'),
        ('src/interop/export/normalization.rs', 'actual_retained_hzh_and_adjoint_preserve_all_columns_controls_and_reference'),
        ('tests/interop.rs', 'ordinary_hzh_words_export_existing_x_cx_ccx_with_full_phase'),
        ('tests/interop.rs', 'ordinary_swap_keeps_three_normalized_cnot_windows_and_readout_order')]),
    'source-configuration': path_rule('configuration', 'source-edition-configuration', '', [
        ('src/frontend/project.rs', ['pub fn load(', 'pub fn load_with_policy(', 'pub fn read_source_file(',
         'pub fn from_modules(', 'pub fn module_manifest(', 'fn validate_edition_context(', 'fn charge_manifest(']),
        ('src/frontend/project/manifest.rs', ['pub fn select(', 'pub fn manifest(', 'load_anchored_with_manifest']),
        ('src/frontend/project/edition.rs', ['pub struct EditionManifest', 'fn read_anchored(', 'fn capture(']),
        ('src/edition.rs', ['pub enum Edition', 'impl FromStr for Edition']),
        ('src/frontend/compile/mod.rs', ['project.validate_edition_context()']),
    ], [('tests/review_v021.rs', 'grouped_imports_expand_to_existing_leaves_with_docs_spans_and_resolution'),
        ('tests/editions.rs', 'qrate_selection_retains_its_exact_manifest_without_reselecting_later_edits'),
        ('tests/editions.rs', 'nested_sources_keep_their_own_original_manifest_association'),
        ('tests/editions.rs', 'explicit_in_memory_project_has_no_fabricated_file_manifest'),
        ('tests/editions.rs', 'retained_manifest_bytes_share_the_existing_aggregate_capacity_once'),
        ('src/frontend/compile/mod.rs', 'source_preparation_rejects_a_substituted_edition_inventory'),
        ('src/edition.rs', 'only_an_explicit_supported_identity_parses')]),
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
         'CallArguments::Places(&prepared)', 'self.obligation(span, ObligationKind::ControlSectors, scope)?']),
        ('src/frontend/specialize/elaborate/places.rs', ['fn partition_step(', 'fn place_call(', 'RuntimeInputs::Values(values)', 'records.into_iter().zip(returned).rev()']),
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
        ('tests/exclusive_access.rs', 'indexed_place_profiles_preserve_the_common_judgment_before_transport'),
        ('tests/exclusive_access.rs', 'selected_place_replay_rejects_native_valid_paired_partition_faults'),
        ('tests/exclusive_access.rs', 'selected_place_inverse_keeps_original_phase_axis'),
        ('tests/exclusive_access.rs', 'selected_indexed_places_preserve_exact_axis_phase_and_reference'),
        ('tests/exclusive_access.rs', 'joint_places_reassemble_updated_values_in_original_axis_order'),
        ('tests/exclusive_access.rs', 'slices_keep_empty_views_and_scalar_phase_during_joint_access'),
        ('tests/exclusive_access.rs', 'selected_slices_apply_nontrivial_actions_in_half_open_axis_order'),
        ('tests/exclusive_access.rs', 'selected_place_control_rechecks_bound_provider_and_shared_work'),
        ('tests/exclusive_access.rs', 'selected_places_thread_updated_parents_through_static_branches_and_folds'),
        ('tests/exclusive_access.rs', 'selected_places_mix_distinct_whole_parents_and_selected_owners'),
        ('tests/exclusive_access.rs', 'selected_places_apply_original_bound_operations_and_check_actual_ctrl_body'),
        ('tests/selected_source_cli.rs', 'selected_static_places_choose_raw_before_native_acceptance'),
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
        ('src/frontend/specialize/raw/contracts.rs', ['ObligationKind::FunctionEquality', 'FunctionEvidence::check_retained_with_kernel',
         'MeaningEvidence::check_retained_with_kernel', 'RetainedIdentity::shared', 'finite_leaf::check_with_kernel']),
        ('src/frontend/specialize/raw.rs', ['pub struct SourceMeaningCheck', 'pub fn check_finite_meaning',
         'pub struct CheckedSourceMeanings', 'program.checked.interface(definition.original).statics',
         'program.meaning_targets[&id].expression(span)?', 'target.finite()', 'budget',
         'OperationSite::Step(caller, step)', 'operation.meanings.iter()',
         'lower_operation_site(source, site.clone(), depth, checking)?',
         'finite_leaf::check_with_kernel', 'self.replay_with_work(leaf.program(), budget)?',
         'original operation binding is absent during replay',
         'accepted.artifact() != self.payload', 'self.replay(accepted)',
         'self.meanings.as_deref().map_or(&[], Vec::as_slice)',
         'pub(super) fn lower_with_kernel(', 'retained.entry(definition.original).or_default().push(calls)',
         'covered &= calls.contains', 'accepted.native_exact_work()',
         'preservation::validate_subject_with_meanings(',
         'fn lower_refined_with_control(', 'fn lower_controlled_source(',
         'let meanings = check_operation_meanings(source, kernel, budget)?.leaves',
         'proposal.meanings = Some(meanings)']),
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
        ('src/frontend/check/body/operations.rs', ['self.obligation(span, ObligationKind::ControlSectors, scope)?']),
        ('src/frontend/specialize/elaborate.rs', ['pub fn check_operation_meanings', 'pub(super) fn require_unrefined',
         'pub(super) fn require_control_evidence', 'checked.obligations.iter().find',
         'pub fn check_function_contracts(', 'pub fn has_function_contracts(', 'fn require_function_contracts(']),
        ('src/frontend/specialize/lower.rs', ['source.require_control_evidence()?']),
        ('src/bin/qleisli/source_plan.rs', ['source.has_operation_meanings()', '.check_operation_meanings(']),
        ('src/frontend/meaning.rs', ['pub(super) fn materialize(', 'Node::Reference',
         'FunctionEvidence::check_retained_with_kernel', 'original reference artifact is absent']),
    ], [('src/frontend/specialize/raw.rs', 'control_audit_collects_new_meanings_in_the_expanded_original_graph'),
        ('tests/reference_meanings.rs', 'reference_operation_bindings_retain_requests_in_raw_and_hierarchy'),
        ('tests/reference_meanings.rs', 'mixed_composition_and_tensor_keep_order_and_low_axes'),
        ('tests/reference_meanings.rs', 'scalar_unit_reference_keeps_exact_phase_and_zero_axis_owner'),
        ('tests/reference_meanings.rs', 'reference_does_not_erase_unused_generic_or_zero_repeat_lying_contracts'),
        ('src/frontend/specialize/raw/contracts.rs', 'reference_operation_replay_rejects_equal_matrix_receipt_substitution'),
        ('tests/selected_function_contracts.rs', 'first_hhh_source_runs_unchanged_through_both_adapters_and_cli'),
        ('tests/selected_function_contracts.rs', 'identity_and_negative_h_fail_exact_equations_in_both_adapters'),
        ('tests/selected_function_contracts.rs', 'unused_and_zero_count_contracts_are_not_erased'),
        ('tests/selected_function_contracts.rs', 'absent_kernel_exhausted_budget_and_wrong_tree_fail_closed'),
        ('src/frontend/specialize/raw/contracts.rs', 'source_contract_replay_rejects_same_matrix_different_native_pair'),
        ('src/frontend/specialize/raw.rs', 'finite_meaning_replay_charges_control_sectors_to_the_callers_budget'),
        ('tests/general_operation_arrows.rs', 'source_control_and_meaning_share_actual_audit_bodies_and_exact_requests'),
        ('tests/classical_functions.rs', 'original_meaning_request_checks_the_actual_provider_bytes_and_exact_phase'),
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
    'engineering-pure-check': path_rule('engineering-check', 'engineering-pure', '--engineering-pure-check', [
        ('src/interchange/mod.rs', ['pub mod engineering_pure;']),
        ('src/interchange/engineering_pure.rs', ['pub struct DyadicBound', 'pub struct EngineeringPureRequest',
         'pub struct EngineeringPureReport', 'pub fn check_with_kernel(', 'pub fn check_serialized_with_kernel(',
         'Arc::ptr_eq(&self, &decision.subject)']),
        ('src/interchange/engineering_pure/runtime.rs', ['fn response(', 'qleisli.engineering-pure-native 1',
         '"--engineering-pure-check"', '"engineering-checked", "execution"']),
        ('src/interchange/execution_view/finite/engineering_pure.rs', ['pub(in crate::interchange) fn complete(',
         '"engineering-pure-request"', 'actual.execution_view_graph().write(w.writer)',
         'ideal.execution_view_graph().write(w.writer)']),
        ('src/bin/qleisli.rs', ['arg == "engineering"', 'engineering::run(&args[1..])']),
        ('src/bin/qleisli/engineering.rs', ['fn execute(',
         'check_serialized_with_kernel(&kernel, &actual, &request)',
         'source correspondence, instrument bound and target resource bound: not established']),
        ('src/bin/qleisli/digest.rs', ['pub(super) fn sha256(']),
        ('lean-kernel/Cli/EngineeringPure.lean', ['def runEngineeringPure ', 'CheckedEngineeringPure.run bytes',
         'qleisli.engineering-pure-native 1', 'engineering-checked']),
        ('lean-kernel/Protocol/EngineeringPure.lean', ['def prepare ', 'structure PreparedBinding ',
         'def checkRetained ', 'theorem checkRetained_bound', 'Qirf.read prepared.body',
         'Qirf.read decoded.expectedText.toUTF8', 'QleisliKernel.Qirf.EngineeringPure.check request']),
        ('lean-kernel/Protocol/ExecutionView/EngineeringPure.lean', ['def engineeringPureRequest ',
         'def engineeringPure ', 'graph value.actual value.checked.actual.root',
         'graph value.ideal value.checked.ideal.root']),
        ('lean-kernel/Protocol/ExecutionView/CheckedEngineeringPure.lean', ['def check ', 'theorem check_binding',
         'supplied.data == expected.data', '.inspection | .caller => throw .packet', 'theorem run_binding']),
        ('lean-kernel/QleisliKernel/Qirf/EngineeringPure.lean', ['def check ', 'PureLeaf.check request.actual.artifact',
         'PureLeaf.check request.ideal.artifact', 'Engineering.Pure.checkMatrices actual.actual ideal.actual']),
        ('lean-kernel/QleisliKernel/Engineering/Pure.lean', ['def checkMatrices ', 'normSqDifferenceWork actual ideal']),
        ('lean/Qleisli/Semantics/EngineeringPure.lean', ['noncomputable def gapCLM ', 'def OperatorBound ']),
        ('lean/Qleisli/EngineeringPure.lean', ['theorem checkMatrices_bound', 'theorem checkMatrices_reference_square']),
        ('lean/Qleisli/NativeEngineeringPure.lean', ['theorem check_meaning', 'theorem check_reference_square']),
        ('lean/Qleisli/NativeEngineeringPureProtocol.lean', ['theorem run_meaning', 'theorem run_reference_square']),
        ('lean/Qleisli/EngineeringPureComposition.lean', ['theorem checked_sequential_reference_bound',
         'theorem checked_tensor_reference_bound', 'theorem checked_controlled_reference_bound']),
    ], [('src/interchange/engineering_pure/tests.rs', 'native_bound_retains_original_bodies_and_zero_stays_engineering'),
        ('src/interchange/engineering_pure/tests.rs', 'native_refuses_tight_bounds_stale_meanings_phase_and_owner_substitution'),
        ('src/interchange/engineering_pure/tests.rs', 'every_typed_context_and_both_original_graph_fields_are_compared_by_lean'),
        ('src/interchange/engineering_pure/tests.rs', 'hidden_observation_reset_and_discard_cannot_receive_pure_engineering_labels'),
        ('src/interchange/engineering_pure/tests.rs', 'rectangular_original_preparations_are_compared_at_their_distinct_ports'),
        ('src/interchange/engineering_pure/runtime.rs', 'engineering_reply_is_strict_and_separate_from_exact_acceptance'),
        ('src/interchange/engineering_pure/runtime.rs', 'incompatible_missing_failed_and_timed_out_checkers_never_fall_back'),
        ('tests/engineering_pure_cli.rs', 'engineering_cli_checks_original_artifacts_and_reports_only_the_declared_bound')]),
    'engineering-instrument-check': path_rule('engineering-check', 'engineering-instrument', '--qirf-engineering-instrument-native', [
        ('src/interchange/mod.rs', ['pub mod engineering_instrument;']),
        ('src/interchange/engineering_instrument.rs', ['pub struct EngineeringInstrumentRequest',
         'pub struct EngineeringInstrumentReport', 'pub fn check_with_kernel(', 'pub fn check_serialized_with_kernel(',
         'Arc::ptr_eq(&self, &decision.subject)', 'const CLAIM_KIND: &str = "engineering-instrument-bound"']),
        ('src/interchange/engineering_instrument/runtime.rs', ['fn response(', 'qleisli.engineering-instrument-native 1',
         '"--qirf-engineering-instrument-native"', '"engineering-checked", "execution"']),
        ('src/interchange/execution_view/finite/engineering_instrument.rs', ['pub(in crate::interchange) fn complete(',
         '"engineering-instrument-request", 14', 'actual.execution_view_graph().write(w.writer)',
         'expected.execution_view_graph().write(w.writer)']),
        ('src/bin/qleisli/engineering.rs', ['arg == "compare-instrument"', 'super::engineering_instrument::run(args)']),
        ('src/bin/qleisli/engineering_instrument.rs', ['fn execute(',
         'check_serialized_with_kernel(&kernel, &actual, &request)',
         'pure phase agreement, coherent control, inverse, clean release and target resource bounds: not established']),
        ('scripts/test_engineering_instrument_cli.py', ['def baseline(', 'def live(',
         'qleisli.engineering-instrument-native-first-capture']),
        ('lean-kernel/Cli/EngineeringInstrument.lean', ['def runEngineeringInstrument ', 'Native.engineeringInstrument bytes',
         'qleisli.engineering-instrument-native 1', 'engineering-checked']),
        ('lean-kernel/Protocol/EngineeringInstrument.lean', ['def prepare ', 'structure PreparedBinding ',
         'def checkRetained ', 'theorem checkRetained_bound', 'Qirf.read prepared.body',
         'Qirf.read decoded.expectedText.toUTF8', 'QleisliKernel.Qirf.EngineeringInstrument.check request']),
        ('lean-kernel/Protocol/ExecutionView/EngineeringInstrument.lean', ['def engineeringInstrumentRequest ',
         'def engineeringInstrument ', 'graph value.actual value.checked.actual',
         'graph value.expected value.checked.expected']),
        ('lean-kernel/Protocol/ExecutionView/CheckedEngineeringInstrument.lean', ['def check ', 'theorem check_binding',
         'supplied.data == expected.data', '.inspection | .caller => throw .packet', 'theorem run_binding']),
        ('lean-kernel/Protocol/ExecutionView/Native.lean', ['def engineeringInstrument ', 'theorem engineeringInstrument_binding']),
        ('lean-kernel/QleisliKernel/Qirf/EngineeringInstrument.lean', ['def check ', 'Validity.checkRoot request.actual',
         'Validity.checkRoot request.expected', 'Raw.Instrument.reconstruct', 'Raw.InstrumentEquality.prepare',
         'Engineering.Instrument.checkHistories', 'theorem check_acceptance']),
        ('lean-kernel/QleisliKernel/Engineering/Instrument.lean', ['def checkHistories ', 'theorem checkHistories_conditions']),
        ('lean/Qleisli/Semantics/EngineeringInstrument.lean', ['noncomputable def adjointWithReference ',
         'def CompleteAdjointBound ']),
        ('lean/Qleisli/EngineeringInstrument.lean', ['theorem checkHistories_bound']),
        ('lean/Qleisli/NativeEngineeringInstrument.lean', ['structure BodyMeaning ', 'structure Meaning ',
         'theorem check_meaning', 'reconstruct_kraus_complete']),
        ('lean/Qleisli/NativeEngineeringInstrumentProtocol.lean', ['theorem run_meaning']),
        ('lean/Qleisli/Semantics/EngineeringInstrumentComposition.lean', ['def GramComplete ',
         'noncomputable def feedForward ', 'noncomputable def tensor ']),
        ('lean/Qleisli/EngineeringInstrumentPureComparison.lean', ['theorem pure_gap_completeAdjointBound',
         'actual_gram : actual.conjTranspose * actual = 1', 'ideal_gram : ideal.conjTranspose * ideal = 1']),
        ('lean/Qleisli/EngineeringInstrumentComposition.lean', ['theorem gram_completeAdjoint_contraction',
         'theorem feedForward_gram', 'theorem feedForward_bound']),
        ('lean/Qleisli/EngineeringInstrumentTensor.lean', ['def leftAxes ', 'def rightAxes ',
         'theorem tensor_gram', 'theorem tensor_bound']),
    ], [('src/interchange/engineering_instrument/tests.rs', 'native_nonzero_and_zero_reports_keep_original_bytes_and_engineering_status'),
        ('src/interchange/engineering_instrument/tests.rs', 'native_refuses_tight_incomplete_reordered_witnesses_and_hidden_observation_labels'),
        ('src/interchange/engineering_instrument/tests.rs', 'every_view_context_and_original_graph_field_requires_fresh_native_agreement'),
        ('src/interchange/engineering_instrument/tests.rs', 'original_dependency_meanings_are_reconstructed_instead_of_reusing_summaries'),
        ('src/interchange/engineering_instrument/tests.rs', 'residual_coherences_and_reference_correlations_are_not_probability_only_bounds'),
        ('src/interchange/engineering_instrument/tests.rs', 'strict_request_rejects_unknown_missing_open_and_cross_kind_data'),
        ('src/interchange/engineering_instrument/runtime.rs', 'engineering_reply_is_strict_and_separate_from_exact_acceptance'),
        ('src/interchange/engineering_instrument/runtime.rs', 'incompatible_missing_failed_and_timed_out_checkers_never_fall_back'),
        ('tests/engineering_instrument_cli.rs', 'original_instrument_api_cli_sources_and_actual_failures_remain_intact'),
        ('tests/engineering_instrument_cli.rs', 'instrument_cli_checks_residual_reference_maps_and_reports_only_declared_bounds')]),
}

PATHS['engineering-pure-tensor-check'] = path_rule(
    'engineering-check', 'engineering-pure-tensor', '--engineering-pure-tensor-check', [
        ('src/interchange/mod.rs', ['pub mod engineering_pure_tensor;']),
        ('src/interchange/engineering_pure_tensor.rs', [
            'pub struct EngineeringPureTensorRequest', 'pub struct EngineeringPureTensorReport',
            'pub fn check_with_kernel(', 'pub fn check_serialized_with_kernel(',
            'Arc::ptr_eq(&self, &decision.subject)',
            'const CLAIM_KIND: &str = "engineering-pure-tensor-bound"']),
        ('src/interchange/engineering_pure_tensor/runtime.rs', [
            'fn response(', 'qleisli.engineering-pure-tensor-native 1',
            '"--engineering-pure-tensor-check"', '"engineering-checked", "execution"']),
        ('src/interchange/execution_view/finite/engineering_pure_tensor.rs', [
            'pub(in crate::interchange) fn complete(', '"engineering-pure-tensor-request", 16',
            'program.execution_view_graph().write(w.writer)']),
        ('src/bin/qleisli/engineering.rs', ['arg == "compare-pure-tensor"']),
        ('src/bin/qleisli/engineering_pure_tensor.rs', ['fn execute(']),
        ('scripts/test_engineering_pure_tensor_native.py', ['def retained(', 'def live(']),
        ('lean-kernel/Cli/EngineeringPureTensor.lean', [
            'def runEngineeringPureTensor ', 'CheckedEngineeringPureTensor.run bytes',
            'qleisli.engineering-pure-tensor-native 1', 'engineering-checked']),
        ('lean-kernel/Protocol/EngineeringPureTensor.lean', [
            'def decode ', 'def Retained.request ', 'def checkRetained ', 'theorem checkRetained_bound',
            'Qirf.read prepared.body', 'Qirf.read decoded.expectedText.toUTF8',
            'Qirf.read decoded.left.actualText.toUTF8', 'Qirf.read decoded.left.idealText.toUTF8',
            'Qirf.read decoded.right.actualText.toUTF8', 'Qirf.read decoded.right.idealText.toUTF8']),
        ('lean-kernel/Protocol/ExecutionView/EngineeringPureTensor.lean', [
            'def engineeringPureTensorRequest ', 'def engineeringPureTensor ',
            'graph value.actual value.checked.parentActual.root',
            'graph value.ideal value.checked.parentIdeal.root',
            'graph value.leftActual value.checked.left.actual.root',
            'graph value.leftIdeal value.checked.left.ideal.root',
            'graph value.rightActual value.checked.right.actual.root',
            'graph value.rightIdeal value.checked.right.ideal.root']),
        ('lean-kernel/Protocol/ExecutionView/CheckedEngineeringPureTensor.lean', [
            'def check ', 'theorem check_binding', 'supplied.data == expected.data',
            '.inspection | .caller => throw .packet', 'theorem run_binding']),
        ('lean-kernel/QleisliKernel/Qirf/EngineeringPureTensor.lean', [
            'def check ', 'EngineeringPure.check request.left', 'EngineeringPure.check request.right',
            'PureLeaf.check request.parentActual.artifact', 'PureLeaf.check request.parentIdeal.artifact',
            'guard (parentActual.actual == actualTensor)', 'guard (parentIdeal.actual == idealTensor)',
            'guard (epsilon == request.epsilon)', 'theorem check_postcondition']),
        ('lean/Qleisli/NativeEngineeringPureTensor.lean', [
            'structure Meaning ', 'theorem check_meaning', 'theorem checked_reference_bound']),
        ('lean/Qleisli/NativeEngineeringPureTensorProtocol.lean', [
            'theorem run_meaning', 'theorem run_reference_bound']),
    ], [('src/interchange/engineering_pure_tensor/tests.rs',
         'native_tensor_composes_component_bounds_without_parent_frobenius')])

PATHS['engineering-openqasm-check'] = path_rule(
    'engineering-check', 'engineering-openqasm', '--engineering-openqasm-check',
    [('src/interchange/mod.rs', ['pub mod engineering_openqasm;']),
 ('src/interchange/engineering_openqasm.rs',
  ['pub struct EngineeringOpenQasmRequest',
   'pub struct EngineeringOpenQasmReport',
   'pub fn check_with_kernel(',
   'pub fn check_serialized_with_kernel(',
   'Arc::ptr_eq(&self, &decision.subject)',
   'target::Decoded::new(target)?',
   'const CLAIM_KIND: &str = "engineering-target-instrument-bound"']),
 ('src/interchange/engineering_openqasm/runtime.rs',
  ['fn response(',
   'qleisli.engineering-openqasm-native 1',
   '"--engineering-openqasm-check"',
   '"engineering-checked", "execution"']),
 ('src/interchange/engineering_openqasm/target.rs',
  ['const MAX_TARGET_BYTES: usize = 1024', 'const MAX_TARGET_GATES: usize = 8', 'fn operation(']),
 ('src/interchange/execution_view/finite/engineering_openqasm.rs',
  ['pub(in crate::interchange) fn complete(',
   '"engineering-openqasm-request", 14',
   'w.list(target,',
   'w.list(gates,',
   'actual.write(w.writer)?',
   'ideal.execution_view_graph().write(w.writer)']),
 ('src/bin/qleisli/engineering.rs', ['arg == "compare-openqasm3"']),
 ('src/bin/qleisli/engineering_openqasm.rs',
  ['fn execute(', 'target_artifact_sha256', 'source_preservation_verified']),
 ('scripts/test_engineering_openqasm_native.py', ['def retained(', 'def live(', 'def independent_oracle(']),
 ('scripts/test_engineering_openqasm_cli.py', ['def baseline(', 'def live(']),
 ('lean-kernel/Cli/EngineeringOpenQasm.lean',
  ['def runEngineeringOpenQasm ',
   'CheckedEngineeringOpenQasm.run bytes',
   'qleisli.engineering-openqasm-native 1',
   'engineering-checked']),
 ('lean-kernel/QleisliKernel/Semantics/CanonicalTerminalQasm.lean',
  ['def gateOp ',
   'def program ',
   'theorem logical_unit_input',
   'theorem logical_unit_consumed',
   'theorem terminal_result']),
 ('lean-kernel/QleisliKernel/Target/CanonicalOpenQasm.lean',
  ['def maxBytes : Nat := 1024', 'def maxGates : Nat := 8', 'def decode ', 'theorem decode_original']),
 ('lean-kernel/QleisliKernel/Target/CanonicalOpenQasmGates.lean',
  ['theorem gate_matrix',
   'theorem wrong_y_phase_refused',
   'theorem wrong_s_direction_refused',
   'theorem wrong_t_direction_refused']),
 ('lean-kernel/QleisliKernel/Qirf/EngineeringOpenQasm.lean',
  ['def actualArtifact ',
   'def Request.instrument ',
   'def check ',
   'exactWork (Exact.charge (1 + request.target.size))',
   'request.actualSignature == Semantics.CanonicalTerminalQasm.signature',
   'EngineeringInstrument.check (request.instrument target)',
   'theorem check_postcondition']),
 ('lean-kernel/Protocol/EngineeringOpenQasm.lean',
  ['def decode ',
   'def Retained.request ',
   'def checkRetained ',
   'theorem checkRetained_bound',
   'Qirf.read decoded.expectedText.toUTF8']),
 ('lean-kernel/Protocol/ExecutionView/EngineeringOpenQasm.lean',
  ['def engineeringOpenQasmRequest ',
   'def engineeringOpenQasm ',
   'value.checked.target.original.data.toList',
   'value.checked.target.gates.map',
   'graph (Qirf.EngineeringOpenQasm.actualArtifact value.checked.target)',
   'graph value.expected value.checked.instrument.expected']),
 ('lean-kernel/Protocol/ExecutionView/CheckedEngineeringOpenQasm.lean',
  ['def check ',
   'theorem check_binding',
   'supplied.data == expected.data',
   '.inspection | .caller => throw .packet',
   'theorem run_binding']),
 ('lean/Qleisli/CanonicalOpenQasmGates.lean', ['theorem gate_meaning']),
 ('lean/Qleisli/NativeEngineeringOpenQasm.lean', ['structure Meaning ', 'theorem check_meaning']),
 ('lean/Qleisli/NativeEngineeringOpenQasmProtocol.lean',
  ['theorem run_meaning', 'theorem run_complete_adjoint_bound'])],
    [('src/interchange/engineering_openqasm/tests.rs',
  'native_checks_actual_backend_target_bytes_against_an_original_ideal_and_zero_stays_engineering'),
 ('src/interchange/engineering_openqasm/tests.rs',
  'altered_original_ideal_tight_bound_or_cell_witness_refuses_without_fallback'),
 ('src/interchange/engineering_openqasm/tests.rs',
  'native_binds_literal_target_gate_word_typed_context_and_both_original_graphs'),
 ('src/interchange/engineering_openqasm/runtime.rs',
  'incompatible_missing_failed_and_timed_out_checkers_never_fall_back'),
 ('tests/engineering_openqasm_cli.rs',
  'openqasm_cli_checks_literal_target_and_original_ideal_with_honest_scope')])

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
        ('lean-kernel/Cli/Hierarchical.lean', [f'def {_cli} ', 'Native.hierarchy mode bytes']),
        ('lean-kernel/Protocol/ExecutionView/Native.lean', ['def hierarchy ', 'theorem hierarchy_binding']),
        ('lean-kernel/Protocol/ExecutionView/CheckedHierarchy.lean', [_check.removeprefix('Hierarchical.'), 'HierarchyView.reconstructLeaves', 'native core.extra']),
        ('lean/Qleisli/NativeHierarchy.lean', ['theorem checkLeaves_semantics']),
    ], [_test])

# General same-artifact prepared predicates remain equivalent to the complete
# original checks. These bindings preserve their actual proof/context and paid
# fallback routes; trace descriptions remain unaccepted data.
PATHS['hierarchy-inspect']['source_bindings'].extend(
    [{'path': 'lean-kernel/QleisliKernel/Hierarchical/Artifact.lean',
      'markers': ['def ProofEndpoints (artifact : Artifact) : Prop :=',
                  'theorem prepare_proofEndpoints']},
     {'path': 'lean-kernel/QleisliKernel/Hierarchical/Power.lean',
      'markers': ['def preparedIdentityEquation',
                  'theorem preparedIdentityEquation_eq',
                  'let .identity := input.body | none\n'
                  '    let .identity := output.body | none\n'
                  '    return proof.kind == Kind.equation']},
     {'path': 'lean-kernel/QleisliKernel/Hierarchical/TypedRule.lean',
      'markers': ['structure PreparedContext (artifact : Artifact) : Prop',
                  'theorem preparedContext_of_checkAll',
                  'theorem preparedOrdinary_eq',
                  'def checkPrepared',
                  'let scan := initial + 16 * proof.premises.size',
                  '16 * (1 + proof.premises.size)',
                  'theorem checkPrepared_conditions']},
     {'path': 'lean-kernel/QleisliKernel/Hierarchical/Conditional.lean',
      'markers': ['(TypedRule.checkPrepared artifact context)',
                  'TypedRule.preparedContext_of_checkAll artifact order typed typing',
                  'theorem checkAll_conditions']},
     {'path': 'lean-kernel/QleisliKernel/Hierarchical/NodeTyping.lean',
      'markers': ['private theorem preparedConditions_eq',
                  'portsAfterHeaders false definition.interface.inputs callee.interface.inputs '
                  'input',
                  'let probe := mapAttempts Ports.identityScanCharge artifact definition',
                  'let attempt := mapAttempts Ports.identityAttemptCharge artifact definition',
                  'let charge := legacy - maps + selectedMapsCost artifact definition']},
     {'path': 'lean-kernel/QleisliKernel/Hierarchical/ContractTyping.lean',
      'markers': ['private theorem subjectAfterHeaders_eq',
                  'let probe := value.mapAttempts Ports.identityScanCharge artifact',
                  'let attempt := value.mapAttempts Ports.identityAttemptCharge artifact',
                  'let charge := legacy - value.mapsCost artifact + value.selectedMapsCost '
                  'artifact']},
     {'path': 'lean-kernel/QleisliKernel/Hierarchical/Ports.lean',
      'markers': ['def positionalIdentity',
                  'theorem shapeAfterHeaders_eq',
                  'identityAttemptCharge source destination map +\n'
                  '    if positionalIdentity source destination map then 0 else workCharge source '
                  'destination map',
                  'private theorem dropping_a_zero_owner_is_rejected',
                  'private theorem equal_width_reordered_type_tree_is_rejected',
                  'private theorem owner_axis_disagreement_is_rejected',
                  'private theorem classical_bases_are_complete_types']},
     {'path': 'lean-kernel/QleisliKernel/Layout.lean',
      'markers': ['theorem range_permutation', 'theorem identity_structureValid']}]
)
PATHS['hierarchy-inspect']['tests'].extend(
    [{'path': 'tests/hierarchical_host.rs',
      'test': 'native_phase_fault_remains_an_obligation_under_zero_repeat'},
     {'path': 'tests/hierarchical_host.rs',
      'test': 'native_actual_counts_premises_and_encodings_are_checked'}]
)
PATHS['hierarchy-qpe']['source_bindings'].extend(
    [{'path': 'lean-kernel/QleisliKernel/Hierarchical/CircuitTrace.lean',
      'markers': ['def summarizeProjected',
                  'theorem summarizeProjected_eq',
                  'Wiring.scan d + 32 * (1 + d.interface.scan + Wiring.bodySize d + atoms.size)',
                  '32 * (sideFields d.interface.inputs + sideFields d.interface.outputs) +\n'
                  '    8 * span^2 + 8 * (1 + d.interface.scan) * span',
                  'if state.visits + rawScan atoms d > remaining then .error .limit else\n'
                  '    if state.visits + scan atoms d > remaining then .error .limit else',
                  'match summarizeProjected state.cache node d with',
                  'rw [summarizeProjected_eq atoms state.cache index d node projected] at computed',
                  'scan atoms d + 8 * (1 + node.children.length) * (1 + events) * (1 + span)^2']},
     {'path': 'lean-kernel/QleisliKernel/Hierarchical/QpeRoot.lean',
      'markers': ['let checked ← Conditional.checkAll packet.artifact packet.order',
                  'theorem checkAll_conditions']},
     {'path': 'lean-kernel/QleisliKernel/Hierarchical/QpeSchedule.lean',
      'markers': ['match CircuitTrace.inspect artifact (atoms candidate) candidate.traceOrder',
                  'theorem inspect_derives']}]
)
PATHS['hierarchy-qpe']['tests'].extend(
    [{'path': 'src/frontend/specialize/qpe.rs',
      'test': 'native_named_qpe_commuting_fourier_variants_have_the_same_outcome'},
     {'path': 'src/frontend/specialize/qpe.rs',
      'test': 'native_named_qpe_from_rust_source_checks_phase_reference_and_provider_mutation'},
     {'path': 'tests/hierarchical_qpe_host.rs',
      'test': 'qpe_host_rejects_missing_duplicate_and_substituted_runtime_obligations'}]
)

NATIVE_DISPATCH = {
    '--qirf-native': 'QleisliKernel.Cli.runValidity',
    '--qirf-contract': '(QleisliKernel.Cli.runValidity true)',
    '--engineering-openqasm-check': 'QleisliKernel.Cli.runEngineeringOpenQasm',
    '--engineering-pure-check': 'QleisliKernel.Cli.runEngineeringPure',
    '--engineering-pure-tensor-check': 'QleisliKernel.Cli.runEngineeringPureTensor',
    '--qirf-engineering-instrument-native': 'QleisliKernel.Cli.runEngineeringInstrument',
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


# Public source permissions and actual native artifact effects remain distinct.
# These ordinary regressions exercise existing routes; no new native mode or
# acceptance authority is introduced by the public-effect API migration (#355).
for _path, _tests in {
    'ordinary-acceptance': [
        'public_observe_identity_retains_actual_unitary_raw_and_same_module_precision',
        'classical_public_interface_body_replacement_keeps_both_source_paths_stable',
        'explicit_pure_labels_never_hide_observation_reset_or_discard',
    ],
    'contract-acceptance': [
        'internal_pure_contract_remains_usable_under_broader_public_provider_bounds',
        'dormant_external_observe_obligations_cannot_reuse_an_internal_pure_pair',
    ],
    'sized-proposal': [
        'external_quantum_annotation_needs_are_fixed_by_the_public_contract',
        'provider_cache_order_keeps_external_isometry_bounds_and_actual_raw_separate',
        'host_selected_public_providers_use_public_bounds_even_when_unused',
    ],
}.items():
    PATHS[_path]['tests'].extend(
        {'path': 'tests/public_effects.rs', 'test': name} for name in _tests)


# Closed finite instances, dormant controls and the narrow zero-basis adapter
# bind to existing reviewed routes. Local computed equations use the existing
# native leaf gate; their public provenance views issue no fresh acceptance.
for _path, _extension in {'ordinary-acceptance': {'source_bindings': [{'path': 'src/frontend/check/plans/body_statics.rs',
                                              'markers': ['fn original_body_static',
                                                          'locals.original_table_is(owner, '
                                                          'table)']},
                                             {'path': 'src/frontend/compile/instances.rs',
                                              'markers': ['fn prepare_instance(',
                                                          'conditional_naturals',
                                                          'fn enter_instance(']},
                                             {'path': 'src/frontend/compile/instances/bindings.rs',
                                              'markers': ['fn bind_source_instance_partial(',
                                                          'fn evaluate_source_static(']},
                                             {'path': 'src/frontend/compile/instances/provider.rs',
                                              'markers': ['fn materialize_instance(',
                                                          'self.check_dormant_instance',
                                                          'BodyState::Ready']},
                                             {'path': 'src/frontend/compile/lower/operations.rs',
                                              'markers': ['fn call_instance(',
                                                          'check_dormant_instance']},
                                             {'path': 'src/frontend/compile/lower/statics.rs',
                                              'markers': ['fn static_branch(', 'fn static_fold(']},
                                             {'path': 'src/frontend/compile/lower/runtime_transforms.rs',
                                              'markers': ['fn runtime_transform(',
                                                          'ResolvedUse::Local',
                                                          'BodyStaticKind::Operation']}],
                         'tests': [{'path': 'tests/general_static_runtime.rs',
                                    'test': 'original_basis_instances_keep_unit_empty_register_bit_and_word_distinct'},
                                   {'path': 'tests/general_static_runtime.rs',
                                    'test': 'static_fold_initializes_once_and_uses_original_index_in_selected_arm'},
                                   {'path': 'tests/general_static_runtime.rs',
                                    'test': 'direct_symbolic_counts_and_specialized_adjoint_retain_exact_phase'},
                                   {'path': 'tests/general_static_runtime.rs',
                                    'test': 'concrete_fold_index_calls_recheck_bound_ctrl_inside_their_empty_callee_fold'},
                                   {'path': 'tests/general_static_runtime.rs',
                                    'test': 'outer_zero_repetition_does_not_hide_an_invalid_inner_count'},
                                   {'path': 'tests/general_static_runtime.rs',
                                    'test': 'classical_static_headers_keep_their_existing_source_contract'},
                                   {'path': 'tests/dormant_primitive_access.rs',
                                    'test': 'dormant_primitive_x_refuses_at_its_original_action_like_a_direct_call'},
                                   {'path': 'src/frontend/compile/instances/tests.rs',
                                    'test': 'closed_provider_reuses_issued_identity_only_for_the_same_fresh_native_body'},
                                   {'path': 'src/frontend/compile/dormant/tests.rs',
                                    'test': 'inactive_carry_checks_bound_ops_with_the_actual_original_nat_owner_type'},
                                   {'path': 'src/frontend/check/plans/body_statics/tests.rs',
                                    'test': 'posttransfer_access_rejects_a_different_checked_collection_with_identical_ids'}]},
 'sized-proposal': {'source_bindings': [{'path': 'src/frontend/specialize/lower/zero_basis.rs',
                                         'markers': ['fn classify(',
                                                     'fn needs_replay(',
                                                     'fn validate_call_event(',
                                                     'fn validate(proposal:']},
                                        {'path': 'src/frontend/specialize/lower/preservation.rs',
                                         'markers': ['fn validate_pure_definition(',
                                                     'fn pure_root(',
                                                     'fn reserve_pure_trace(']}],
                    'tests': [{'path': 'src/frontend/specialize/lower/zero_basis/tests.rs',
                               'test': 'zero_basis_maps_preserve_distinct_empty_atoms_and_native_owner_obligations'},
                              {'path': 'src/frontend/specialize/lower/zero_basis/tests.rs',
                               'test': 'a_native_valid_extra_scalar_cannot_use_an_unchanged_zero_interval_as_source_evidence'},
                              {'path': 'src/frontend/specialize/lower/zero_basis/tests.rs',
                               'test': 'pure_atomic_helpers_bind_their_original_child_root_and_complete_caller_frame'},
                              {'path': 'src/frontend/specialize/lower/zero_basis/tests.rs',
                               'test': 'original_source_obligations_survive_omitted_interval_and_pure_trace_tables'},
                              {'path': 'src/frontend/specialize/lower/zero_basis/tests.rs',
                               'test': 'zero_basis_composition_retains_intervals_and_nonzero_tables_keep_profile_refusal'},
                              {'path': 'src/frontend/specialize/lower/preservation/isometry_tests.rs',
                               'test': 'zero_basis_preparation_keeps_exact_phase_reference_and_physical_initialization'}]},
 'contract-acceptance': {'source_bindings': [{'path': 'src/frontend/compile/lower/dormant_access.rs',
                                              'markers': ['fn check_action(', 'fn refuse(']},
                                             {'path': 'src/frontend/compile/lower/computed_phase.rs',
                                              'markers': ['fn computed_phase_proposal(',
                                                          'fn computed_unitary_leaf(',
                                                          'fn computed_canonical_witness(',
                                                          'finite_leaf::check_with_kernel',
                                                          'SourceUnitaryEquation::bind',
                                                          'fn '
                                                          'computed_canonical_transport_bound(']}],
                         'tests': [{'path': 'tests/dormant_primitive_access.rs',
                                    'test': 'dormant_zero_width_primitive_actions_each_require_a_fresh_native_request'},
                                   {'path': 'tests/computed_derived_source.rs',
                                    'test': 'ordinary_z_t_and_unrelated_wrappers_use_native_normalization'},
                                   {'path': 'tests/computed_derived_source.rs',
                                    'test': 'scalar_on_the_zero_predicate_is_preserved_on_unit_data'},
                                   {'path': 'tests/computed_derived_source.rs',
                                    'test': 'non_diagonal_and_false_meaning_and_outer_reference_are_refused'},
                                   {'path': 'tests/computed_derived_source.rs',
                                    'test': 'expanded_ordinary_t_chain_reports_its_source_work_limit'},
                                   {'path': 'src/frontend/compile/lower/computed_phase.rs',
                                    'test': 'native_normalization_rejects_same_relative_phase_with_wrong_global_scalar'},
                                   {'path': 'tests/computed_derived_source.rs',
                                    'test': 'compact_205_ordinary_t_actions_bind_complete_body_to_exact_emitted_use'},
                                   {'path': 'tests/computed_derived_source.rs',
                                    'test': 'consecutive_proposal_chunks_compose_in_source_order'},
                                   {'path': 'src/frontend/compile/lower/computed_phase.rs',
                                    'test': 'canonical_transport_bound_covers_all_eight_actions_and_u32_ids'},
                                   {'path': 'src/frontend/compile/lower/computed_phase.rs',
                                    'test': 'native_canonical_witness_refuses_altered_use_and_owner_frame'}]},
 'checked-views': {'source_bindings': [{'path': 'src/interchange/finite_leaf.rs',
                                        'markers': ['pub struct SourceUnitaryEquation',
                                                    'pub fn implementation(&self) -> '
                                                    '&CheckedUnitaryLeaf',
                                                    'pub fn specification(&self) -> '
                                                    '&CheckedUnitaryLeaf',
                                                    'pub fn names(&self)',
                                                    'pub fn sources(&self)']},
                                       {'path': 'src/interchange/native.rs',
                                        'markers': ['pub fn source_computed_normalizations(']}],
                   'tests': []}}.items():
    PATHS[_path]['source_bindings'].extend(_extension['source_bindings'])
    PATHS[_path]['tests'].extend(_extension['tests'])
PATHS['checked-views']['boundaries'].extend(['source', 'finite-leaf'])

# Inert original-source closure and storage accounting; no new native mode or proof claim.
for _path, _extension in {'ordinary-acceptance': {'source_bindings': [{'path': 'src/frontend/compile/sources.rs',
                                              'markers': ['pub(super) fn retained_sources(',
                                                          'fn root(',
                                                          'original_table_is(key, table)',
                                                          'fn operation(',
                                                          'origin.equation.source_view()',
                                                          'fn raw(',
                                                          'expected != source.source']},
                                             {'path': 'src/frontend/compile/operations.rs',
                                              'markers': ['self.retained_sources(module, span, '
                                                          '&roots, bindings, &[program.raw()])?']},
                                             {'path': 'src/frontend/compile/lower/function_contract.rs',
                                              'markers': ['&[implementation, specification, '
                                                          'caller]',
                                                          'RetainedIdentity::interned(']}],
                         'tests': [{'path': 'src/frontend/compile/sources.rs',
                                    'test': 'original_closure_keeps_nat_meaning_and_inactive_edges_but_not_unused_imports'},
                                   {'path': 'src/frontend/compile/sources.rs',
                                    'test': 'local_operation_shadow_does_not_retain_its_global_diagnostic_candidate'},
                                   {'path': 'src/frontend/compile/sources.rs',
                                    'test': 'foreign_equal_shaped_lexical_origin_is_not_a_current_source_root'},
                                   {'path': 'tests/source_snapshots.rs',
                                    'test': 'unrelated_large_sources_do_not_become_ordinary_gate_dependencies'},
                                   {'path': 'tests/function_contracts.rs',
                                    'test': 'observing_contract_receipts_keep_each_original_caller_module'},
                                   {'path': 'tests/repair_diagnostics.rs',
                                    'test': 'snapshot_limit_errors_explain_the_retained_sources'},
                                   {'path': 'tests/cli_sampling.rs',
                                    'test': 'cli_new_default_has_an_explicit_legacy_escape'}]},
 'contract-acceptance': {'source_bindings': [{'path': 'src/frontend/compile/operations/pure.rs',
                                              'markers': ['self.retained_sources(module, span, '
                                                          '&roots, bindings, &[body.raw()])?',
                                                          'let origin = Arc::new(PureOrigin {']},
                                             {'path': 'src/frontend/compile/lower/computed_phase.rs',
                                              'markers': ['let sources = '
                                                          'self.compiler.retained_sources(',
                                                          '&self.bindings,']}],
                         'tests': [{'path': 'tests/source_snapshots.rs',
                                    'test': 'bound_pure_actual_retains_its_original_source_through_a_generic_provider'}]},
 'checked-views': {'source_bindings': [{'path': 'src/contract/function.rs',
                                        'markers': ['pub(crate) enum SourceView',
                                                    'pub(crate) struct SourceSnapshot',
                                                    'RetainedIdentity::Interned',
                                                    'budget.charge_source_row(row)?']},
                                       {'path': 'src/contract/exact.rs',
                                        'markers': ['pub(crate) fn charge_source_row(',
                                                    'Arc::ptr_eq(seen, row)',
                                                    'self.source_rows.push(Arc::clone(row))']},
                                       {'path': 'src/interchange/pure_leaf.rs',
                                        'markers': ['pub fn sources(&self)',
                                                    'self.sources.exposed()']},
                                       {'path': 'src/interchange/mod.rs',
                                        'markers': ['fn evidence_fields(',
                                                    'for (path, text) in snapshot.iter()',
                                                    'pub(crate) fn function_snapshot_key(']},
                                       {'path': 'src/interchange/execution_view/finite.rs',
                                        'markers': ['fn sources(',
                                                    'for (path, text) in sources.iter()',
                                                    'w.sources(identity.2)']}],
                   'tests': [{'path': 'src/contract/function.rs',
                              'test': 'overlapping_interned_closures_charge_shared_rows_once_without_exposing_copies'},
                             {'path': 'src/contract/function.rs',
                              'test': 'interned_source_storage_preserves_native_snapshot_and_proposal_bytes'},
                             {'path': 'src/interchange/execution_view/finite/tests.rs',
                              'test': 'identity_storage_views_preserve_exact_qdv_bytes_and_source_order'},
                             {'path': 'tests/source_snapshots.rs',
                              'test': 'shared_receipts_keep_exact_bindings_and_outlive_source_changes'}]}}.items():
    PATHS[_path]['source_bindings'].extend(_extension['source_bindings'])
    PATHS[_path]['tests'].extend(_extension['tests'])


def boundary_paths(boundary):
    return sorted(name for name, rule in PATHS.items() if boundary in rule['boundaries'])


def boundary_status(boundary):
    categories = {PATHS[name]['classification'] for name in boundary_paths(boundary)}
    statuses = {'native-execution' if category in {'native-acceptance', 'native-hierarchy-check'} else
                'engineering-check' if category == 'engineering-check' else
                'lean-component' if category == 'lean-component' else 'untrusted-host'
                for category in categories}
    return next(iter(statuses)) if len(statuses) == 1 else 'mixed-boundary'


# Reviewed routes; source loading and simulation cannot mint accepted handles.
# Completed zero-width source composites retain explicit source/witness faults.
# These are regression references; presence is not native validation or proof.
PATHS['sized-proposal']['tests'].extend([
    dict(path='src/frontend/specialize/lower/zero_basis/transform_tests.rs',
         test='named_zero_basis_transforms_retain_all_original_empty_owner_intervals'),
    dict(path='src/frontend/specialize/lower/zero_basis/transform_tests.rs',
         test='preparation_operation_retains_its_explicit_hierarchy_refusal'),
    dict(path='src/frontend/specialize/lower/zero_basis/transform_tests.rs',
         test='zero_repetitions_bind_the_original_child_and_literal_count'),
    dict(path='src/frontend/specialize/lower/zero_basis/transform_tests.rs',
         test='native_valid_identity_cannot_replace_the_original_zero_repeat_child_root'),
    dict(path='src/frontend/specialize/lower/zero_basis/transform_tests.rs',
         test='native_valid_direction_and_polarity_changes_remain_different_source_actions'),
    dict(path='src/frontend/specialize/lower/zero_basis/transform_tests/composite_tests.rs',
         test='all_original_composite_constructors_retain_structural_table_dependencies'),
    dict(path='src/frontend/specialize/lower/zero_basis/transform_tests/composite_tests.rs',
         test='native_valid_other_constructor_trees_cannot_replace_the_original_source'),
    dict(path='src/frontend/specialize/lower/zero_basis/transform_tests/composite_tests.rs',
         test='native_execution_preserves_composite_full_phase_with_an_untouched_reference'),
    dict(path='src/frontend/specialize/lower/zero_basis/transform_tests/composite_tests.rs',
         test='original_composites_keep_distinct_zero_width_arrow_endpoints'),
    dict(path='src/frontend/specialize/lower/zero_basis/transform_tests/native_source_tests.rs',
         test='checked_finite_overrides_keep_actual_bytes_and_each_original_zero_interval'),
    dict(path='src/frontend/specialize/lower/zero_basis/transform_tests/native_source_tests.rs',
         test='a_zero_repeat_override_cannot_erase_its_original_dormant_source_child'),
    dict(path='src/frontend/specialize/lower/zero_basis/transform_tests/native_source_tests.rs',
         test='reference_meaning_override_retains_both_original_raw_and_actual_receipt_wrapper'),
    dict(path='src/frontend/specialize/lower/zero_basis/transform_tests/native_source_tests.rs',
         test='reference_override_compares_complete_nested_receipt_snapshots_after_native_decode'),
    dict(path='src/frontend/specialize/lower/zero_basis/transform_tests/native_source_tests.rs',
         test='checked_source_witness_cannot_move_to_a_fresh_equal_shaped_source_collection'),
    dict(path='src/frontend/specialize/lower/zero_basis/transform_tests/native_source_tests.rs',
         test='retained_witness_ceiling_rejects_before_extending_the_existing_aggregate'),
])


# Exact final target-word bindings; existence is not native validation.
_terminal_foreign_sources = {'src/interop/profile.rs': ['let mut normalization_barriers = [false; MAX_GATES + 1];',
                            'RawOp::Init0 { .. } | RawOp::MeasureZ { .. } | RawOp::Discard { .. }',
                            'normalization_barriers[circuit.gates.len()] = true;',
                            'super::export::finish(&mut circuit, &mut expansion, '
                            '&normalization_barriers)?;'],
 'src/interop/export.rs': ['pub(super) fn finish(',
                           'expansion.normalizations.terminal(circuit, barriers)?;',
                           'fold_phases(circuit);'],
 'src/interop/export/normalization.rs': ['pub(super) fn terminal(',
                                         'if circuit.gates.len() > MAX_GATES || circuit.qubits > '
                                         'MAX_QUBITS {',
                                         '.charge(circuit.gates.len() + 1)',
                                         'if barriers[index + 1] || barriers[index + 2] {',
                                         'terminal_candidate(&circuit.gates[index..index + 3])?',
                                         'self.check(&window, &replacement)?;',
                                         'let mut original = std::mem::take(&mut '
                                         'circuit.gates).into_iter().enumerate();',
                                         'fn terminal_candidate(',
                                         'let mapped = |op: &GateOp| -> Result<CircuitStep, '
                                         'InteropError> {\n'
                                         '        let mut step = op.gate.step();',
                                         '|| word[0].wires != word[1].wires',
                                         '|| word[0].wires != word[2].wires']}
for _source in PATHS['foreign-export']['source_bindings']:
    _source['markers'].extend(_terminal_foreign_sources.get(_source['path'], []))
PATHS['foreign-export']['tests'].extend(
    dict(path=_path, test=_test) for _path, _test in [('src/interop/export/normalization.rs',
  'final_target_windows_retain_axes_order_and_nonpure_barriers'),
 ('src/interop/export/normalization.rs',
  'final_target_equation_failure_retains_the_original_gates'),
 ('src/interop/export/normalization.rs',
  'final_target_native_equations_share_full_receipts_and_preserve_all_columns'),
 ('tests/interop.rs', 'ordinary_inlined_hzh_exports_literal_x_across_pure_raw_steps'),
 ('tests/interop.rs', 'final_target_window_does_not_cross_fresh_preparation')])

# Retained original fixed-Fourier correspondence remains untrusted proposal work.
_sized_original_preparation = {'path': 'src/frontend/specialize/lower/zero_basis/transform_tests.rs',
 'test': 'preparation_operation_retains_its_explicit_hierarchy_refusal'}
if PATHS['sized-proposal']['tests'].count(_sized_original_preparation) != 1:
    raise ValueError('reviewed old preparation refusal is missing or duplicated')
PATHS['sized-proposal']['tests'][PATHS['sized-proposal']['tests'].index(_sized_original_preparation)] = {'path': 'src/frontend/specialize/lower/zero_basis/transform_tests.rs',
 'test': 'forward_preparation_operation_retains_its_original_source_interval'}
_sized_source_extensions = {'src/frontend/specialize/lower.rs': ['pub fn source_trace_graph(&self) -> &[u8] {\n'
                                      '        &self.retained_source_proposal().graph',
                                      'pub fn source_events(&self) -> &[SourceEvent] {\n'
                                      '        &self.retained_source_proposal().events',
                                      'pub fn initialization_moves(&self) -> &[InitializationMove] '
                                      '{\n'
                                      '        &self.retained_source_proposal().moves',
                                      'checked.reconstruction().checker()',
                                      'let original = self.retained_source_proposal();',
                                      '.check_instrument_native(original.payload(), '
                                      'original.comparison_request())',
                                      'if checked.checker() != checker {',
                                      'if actual_structural_work > 2_000_000\n'
                                      '                || checked.structural_work() > 2_000_000\n'
                                      '                || actual_exact_work > '
                                      'crate::contract::DEFAULT_EXACT_WORK\n'
                                      '                || checked.exact_work() > '
                                      'crate::contract::DEFAULT_EXACT_WORK',
                                      'if forward_isometry && '
                                      '!zero_basis::materialized_without_repeat(operation)? {'],
 'src/frontend/specialize/fourier.rs': ['pub(super) fn retained_trace_pair(',
                                        'fn trace_debit(',
                                        '*remaining -= initial - work;',
                                        'staircase(&original_trace, width) && '
                                        'staircase(&actual_trace, width)',
                                        'pub(super) fn factor_fourier_with_work('],
 'src/frontend/specialize/qpe.rs': ['self.validate_fourier_transport()?;'],
 'src/frontend/specialize/lower/zero_basis.rs': ['pub(super) fn materialized_without_repeat(',
                                                 'pub(super) fn validate_constructor_operation(',
                                                 'operations::validate_bound(proposal, event, '
                                                 'operation, defs, adjoint)',
                                                 'if materialized_constructors {'],
 'src/frontend/specialize/lower/zero_basis/operations.rs': ['pub(super) fn validate_bound(',
                                                            'matcher.bound(operation, id, &before, '
                                                            '&after, adjoint, 0)'],
 'src/frontend/specialize/lower/preservation.rs': ['Some((&children[0], true))',
                                                   'materialized zero-basis repetition lacks its '
                                                   'original dormant child transport'],
 'src/frontend/specialize/lower/zero_basis/native_source.rs': ['pub(in '
                                                               'crate::frontend::specialize::lower) '
                                                               'fn retained_witness('],
 'src/interchange/hierarchical.rs': ['pub(crate) fn checker(&self) -> &Path {\n'
                                     '        &self.checker'],
 'src/frontend/specialize/lower/fourier_transport.rs': ['const RETAINED_BYTES: usize = 16 << 20;',
                                                        'const RETAINED_CELLS: usize = 100_000;',
                                                        'const REPLAY_WORK: usize = 2_000_000;',
                                                        'pub(super) original: '
                                                        'Arc<HierarchyProposal>',
                                                        'fn source_cells(',
                                                        'operation.key()',
                                                        'OperationKey::SourceEffect(Effect::Unitary, '
                                                        '_)',
                                                        'original.fourier_transport.is_some()',
                                                        '!proposal.source.same_witness_source(&original.source)',
                                                        'expected.payload != proposal.payload',
                                                        'expected.graph != proposal.graph',
                                                        'expected.comparison != '
                                                        'proposal.comparison',
                                                        'expected.bindings != transport.bindings',
                                                        'fourier::retained_trace_pair(',
                                                        'bindings.retain(|binding| '
                                                        'mapping.contains_key(&binding.original));',
                                                        'Err(error) if error.code() == "limit" => '
                                                        'return Ok(original)',
                                                        'Arc::try_unwrap(fallback)']}
for _path, _markers in _sized_source_extensions.items():
    _bindings = [row for row in PATHS['sized-proposal']['source_bindings'] if row['path'] == _path]
    if len(_bindings) > 1:
        raise ValueError('duplicate source binding')
    if _bindings:
        _bindings[0]['markers'].extend(_markers)
    else:
        PATHS['sized-proposal']['source_bindings'].append(dict(path=_path, markers=_markers))
PATHS['sized-proposal']['tests'].extend(
    dict(path=_path, test=_test) for _path, _test in [('src/frontend/specialize/lower/zero_basis/transform_tests.rs',
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
  'all_native_modes_retain_invoked_canonical_paths_after_alias_and_target_moves')])

ROUTES = {'raw': ('tests/native_paths.rs', 'raw_exports_conversions_and_native_reports_share_the_original_byte_gate'), 'contract': ('tests/semantic_contracts.rs', 'primitive_evidence_preserves_exact_phase'), 'function': ('tests/function_evidence.rs', 'checks_two_raw_functions_and_retains_their_full_snapshots'), 'qirf': ('tests/native_paths.rs', 'raw_exports_conversions_and_native_reports_share_the_original_byte_gate'), 'finite-leaf': ('tests/finite_leaf.rs', 'reconstruct_hadamard_in_both_formats_and_bind_complete_bytes'), 'source': ('scripts/test_source_kernel.py', 'test_unused_body_native_rejection_blocks_every_source_action'), 'foreign': ('scripts/test_interop_native.py', 'test_all_actions_formats_use_real_native_checker'), 'native-components': ('tests/hierarchical_host.rs', 'native_request_binds_reindexed_shared_powers_and_exact_meaning_bytes'), 'hierarchy-inspect': ('tests/hierarchical_host.rs', 'native_request_binds_reindexed_shared_powers_and_exact_meaning_bytes'), 'execution': ('tests/sampling.rs', 'stochastic_samples_match_independent_bell_and_reset_feedback_contracts'), 'readout-component': ('scripts/test_hierarchical_readout.py', 'test_native_branches'), 'preparation-component': ('scripts/test_hierarchical_preparation.py', 'test_zero_reference'), 'instrument-composition': ('tests/hierarchical_host.rs', 'native_instrument_binds_all_stages_and_reconstructs_finite_obligations'), 'hierarchy-execution': ('tests/hierarchical_execution.rs', 'small_source_clients_match_independent_complex_reference_branches'), 'sized-source-proposal': ('tests/sized_source.rs', 'rust_source_proposals_check_natively_and_preserve_small_system_coefficients'), 'named-qpe-components': ('tests/hierarchical_qpe_host.rs', 'native_qpe_instrument_binds_provider_phase_hadamards_and_all_boundaries'), 'source-edition-configuration': ('tests/review_v021.rs', 'grouped_imports_expand_to_existing_leaves_with_docs_spans_and_resolution'), 'lean-finite-component-v024': ('tests/semantic_contracts.rs', 'primitive_evidence_preserves_exact_phase'), 'qirf-native-v028': ('tests/native_paths.rs', 'native_report_retains_the_exact_artifact_request_and_reconstructed_program'), 'qirf-native-v029': ('tests/native_acceptance.rs', 'native_handles_execute_bell_and_feedback_without_legacy_receipts')}
ROUTES['engineering-pure'] = ('src/interchange/engineering_pure/tests.rs',
                             'native_bound_retains_original_bodies_and_zero_stays_engineering')
ROUTES['engineering-instrument'] = ('src/interchange/engineering_instrument/tests.rs',
                                   'native_nonzero_and_zero_reports_keep_original_bytes_and_engineering_status')
ROUTES['engineering-pure-tensor'] = ('src/interchange/engineering_pure_tensor/tests.rs',
                                    'native_tensor_composes_component_bounds_without_parent_frobenius')

ROUTES['engineering-openqasm'] = ('src/interchange/engineering_openqasm/tests.rs', 'native_checks_actual_backend_target_bytes_against_an_original_ideal_and_zero_stays_engineering')
ROUTES['source-edition-configuration'] = ('tests/editions.rs', 'qrate_selection_retains_its_exact_manifest_without_reselecting_later_edits')


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
        require(row['status'] in {'untrusted-host', 'lean-component', 'native-execution', 'mixed-boundary',
                                 'engineering-check'}, 'unknown migration status')
        require((row['status'] == 'engineering-check') == (row['id'] in {
            'engineering-pure', 'engineering-instrument', 'engineering-pure-tensor', 'engineering-openqasm'}),
                'engineering-only status must remain separate from exact production acceptance')
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
        if row['id'] == 'engineering-pure-check':
            require({key: row[key] for key in ENGINEERING_PURE_PROOF} == ENGINEERING_PURE_PROOF,
                    'unreviewed engineering-pure proof scope')
        if row['id'] == 'engineering-instrument-check':
            require({key: row[key] for key in ENGINEERING_INSTRUMENT_PROOF} == ENGINEERING_INSTRUMENT_PROOF,
                    'unreviewed engineering-instrument proof scope')
        if row['id'] == 'engineering-openqasm-check':
            require({key: row[key] for key in ENGINEERING_OPENQASM_PROOF} == ENGINEERING_OPENQASM_PROOF,
                    'unreviewed engineering-openqasm proof scope')
        if row['id'] == 'engineering-pure-tensor-check':
            require({key: row[key] for key in ENGINEERING_PURE_TENSOR_PROOF} == ENGINEERING_PURE_TENSOR_PROOF,
                    'unreviewed engineering-pure-tensor proof scope')
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
