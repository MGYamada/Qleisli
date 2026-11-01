"""Migration coverage must fail closed on omitted or newly exposed paths."""
import copy
import json
from pathlib import Path
import tomllib
import unittest
from unittest.mock import patch
import check_production_coverage as coverage
from check_verification_inventory import variants
from current_metadata import read_json


class ProductionCoverage(unittest.TestCase):
    def setUp(self):
        self.data = read_json(coverage.ROOT, coverage.COVERAGE)
        self.inventory = read_json(coverage.ROOT, coverage.INVENTORY)

    def test_current_review_accounts_for_all_groups_and_boundaries(self):
        result = coverage.check(coverage.ROOT, self.data, self.inventory)
        self.assertEqual(result['groups'], len(self.inventory['groups']))
        self.assertEqual(result['groups'], 49)
        self.assertEqual(result['public_boundaries'], 28)
        self.assertEqual(result['authority'], 'Lean')
        self.assertEqual(result['target_authority'], 'Lean')
        self.assertEqual(result['migration'], 'single-lean-acceptance-implemented')
        self.assertEqual(result['production_paths'], 39)
        self.assertEqual(result['native_modes'], 17)
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
                     'foreign-export', 'checked-views', 'carrier-proposal', 'carrier-views',
                     'ordinary-result-proposal', 'ordinary-result-views', 'qmatch-proposal', 'qmatch-views'):
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

    def test_carrier_gate_requires_its_own_execution_mode_and_sealed_scope(self):
        for name in ('carrier-check', 'source-carrier-check'):
            for field, value in (
                ('native_modes', ['--qirf-native']),
                ('classification', 'untrusted-proposal'),
                ('boundaries', ['finite-leaf']),
            ):
                data = copy.deepcopy(self.data)
                next(row for row in data['paths'] if row['id'] == name)[field] = value
                with self.subTest(path=name, field=field), self.assertRaisesRegex(ValueError, 'classification or binding'):
                    coverage.check(coverage.ROOT, data, self.inventory)

    def test_carrier_proof_scope_cannot_claim_source_or_guarantee_completion(self):
        for name in ('carrier-check', 'source-carrier-check'):
            for field, value in (
                ('proof_scope', 'Equal metadata proves the full original function AST'),
                ('gaps', 'All runtime, inverse/control and admitted constitutional guarantees are complete'),
            ):
                data = copy.deepcopy(self.data)
                next(row for row in data['paths'] if row['id'] == name)[field] = value
                with self.subTest(path=name, field=field), self.assertRaisesRegex(ValueError, 'finite-carrier proof scope'):
                    coverage.check(coverage.ROOT, data, self.inventory)

    def test_ordinary_result_requires_its_typed_execution_mode(self):
        for field, value in (
            ('native_modes', ['--qirf-native']),
            ('classification', 'untrusted-proposal'),
            ('boundaries', ['finite-leaf']),
        ):
            data = copy.deepcopy(self.data)
            next(row for row in data['paths'] if row['id'] == 'ordinary-result-check')[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'classification or binding'):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_ordinary_result_proof_scope_cannot_be_widened(self):
        for field, value in (
            ('proof_scope', 'The result storage check proves the complete source function'),
            ('gaps', 'All inputs, quantum nominal interfaces and QS/PR/RS guarantees are complete'),
        ):
            data = copy.deepcopy(self.data)
            next(row for row in data['paths'] if row['id'] == 'ordinary-result-check')[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'ordinary-result proof scope'):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_runtime_root_keeps_its_native_mode_and_limited_proof_scope(self):
        for field, value, message in (
            ('native_modes', ['--qirf-native'], 'classification or binding'),
            ('proof_scope', 'Complete source and numerical runtime preservation', 'runtime-result proof scope'),
            ('gaps', 'All generic and qmatch obligations are discharged', 'runtime-result proof scope'),
        ):
            data = copy.deepcopy(self.data)
            next(row for row in data['paths'] if row['id'] == 'runtime-result-check')[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, message):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_qmatch_component_requires_its_bound_mode_and_explicit_proof_gaps(self):
        for field, value, message in (
            ('native_modes', ['--qirf-native'], 'classification or binding'),
            ('classification', 'untrusted-proposal', 'classification or binding'),
            ('proof_scope', 'The original complete source function is proved', 'qmatch-component proof scope'),
            ('gaps', 'All source/runtime and constitutional obligations are complete', 'qmatch-component proof scope'),
        ):
            data = copy.deepcopy(self.data)
            next(row for row in data['paths'] if row['id'] == 'qmatch-check')[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, message):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_qmatch_and_ordinary_roots_keep_their_original_subject_obligations(self):
        for path, marker in (
            ('src/interchange/native/qmatch.rs', 'qmatch::complete(prepared.graph(), &request)?'),
            ('src/interchange/mod.rs', 'roots.push(programs.len() + evidence)'),
            ('lean-kernel/QleisliKernel/Qirf/Carrier.lean', 'sourceRootFromRoots artifact order attached required [artifact.root]'),
            ('lean-kernel/QleisliKernel/Qirf/Carrier.lean', 'sourceRootWithRows artifact order attached required roots []'),
            ('lean-kernel/Protocol/Qmatch.lean', 'Qirf.ContextSector.check artifact order'),
            ('lean-kernel/Protocol/Qmatch.lean', 'let result ← Qirf.ContextSector.check artifact order request.source.moduleName request.source.functionName\n    request.positions request.sites'),
            ('lean-kernel/Protocol/Qmatch.lean', 'exactWork (Exact.charge (8*(positions.size+1)))'),
            ('lean-kernel/QleisliKernel/Qirf/ContextSector.lean', '(RawTrace.check headers.source.val root.val.dependencies root.val.program positions)\n  return ⟨root,context⟩'),
            ('lean-kernel/QleisliKernel/Qirf/ContextSector.lean', 'let selected ← collect body.context.val.sites'),
            ('lean-kernel/QleisliKernel/Qirf/ContextSector.lean', 'if position : header.request.position = bound.position then'),
            ('lean-kernel/QleisliKernel/Qirf/SelectionCore.lean', 'let entries ← SourceTypes.NaturalAffine.witness (header.bindings.val.mapM fun binding =>\n        SourceSector.readEntry artifact root.receipts binding fresh)'),
            ('lean-kernel/QleisliKernel/Qirf/SelectionCore.lean', 'let logical ← SourceTypes.NaturalAffine.witness (NominalSector.checkLogicals'),
            ('lean-kernel/QleisliKernel/Qirf/SourceSequence.lean', 'Raw.OwnerFlow.check'),
            ('lean-kernel/QleisliKernel/SourceTypes/SourceTrace.lean', 'theorem Checked.allOriginalCalls '),
            ('lean-kernel/QleisliKernel/Qirf/RawTrace.lean', 'QleisliKernel.Raw.OwnerBoundaries.check'),
            ('lean-kernel/QleisliKernel/Qirf/RawTrace.lean', 'if complete : Qirf.SourceSequence.covers program.operations.length positions = true then'),
            ('lean-kernel/QleisliKernel/Qirf/PrimitiveAction.lean', 'if instruction : interval.slice.operations = [operation kind input output] then'),
            ('lean-kernel/QleisliKernel/Qirf/PrimitiveAction.lean', 'if inputWidth : interval.selected.map (·.bits) = [layout.val.bits] then'),
            ('lean-kernel/QleisliKernel/Qirf/PrimitiveAction.lean', 'if outputWidth : interval.returned.map (·.bits) = [layout.val.bits] then'),
            ('src/interchange/execution_view/finite/qmatch.rs', 'view.list(&request.positions, |w, position| {\n        w.record("source-interval",'),
            ('src/interchange/execution_view/finite/qmatch.rs', 'w.n(site.position.offset as usize)?;'),
            ('src/interchange/execution_view/finite/qmatch.rs', 'w.n(site.position.start as usize)?;'),
            ('src/interchange/execution_view/finite/qmatch.rs', 'w.n(site.position.count as usize)'),
            ('src/interchange/execution_view/finite/qmatch.rs', 'view.list(&request.positions,'),
            ('lean-kernel/Protocol/ExecutionView/CheckedQmatch.lean', '.array (checked.request.positions.map position)'),
            ('lean-kernel/QleisliKernel/Qirf/PureInterval.lean', 'let whole ← SourceTypes.NaturalAffine.witness'),
            ('lean-kernel/Protocol/NativeContext/Bindings.lean', 'theorem run_qmatch_binding '),
        ):
            with self.subTest(path=path, marker=marker), self.assertRaisesRegex(ValueError, 'source binding changed'):
                self.check_changed_source(path, marker, 'removed required original-subject binding')

    def test_carrier_requires_original_source_body_view_and_false_source_claim(self):
        for path, marker in (
            ('lean-kernel/Protocol/Carrier.lean', 'checkSources artifact.sources request'),
            ('lean-kernel/QleisliKernel/Qirf/Carrier.lean', 'guard (actual == specified) .equation'),
            ('lean-kernel/Protocol/ExecutionView/CheckedCarrier.lean', '.inspection | .caller => throw .packet'),
            ('lean-kernel/Protocol/NativeContext/Bindings.lean', 'theorem run_carrier_binding '),
            ('src/frontend/specialize/raw/carrier.rs', 'preservation::validate_subject_with_meanings('),
            ('src/frontend/specialize/raw/carrier.rs', 'pub fn source_meaning_verified(&self) -> bool {\n        false'),
        ):
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, 'source binding changed'):
                self.check_changed_source(path, marker, 'removed reviewed binding')

    def test_provider_reuse_keeps_producer_and_native_root_profiles(self):
        for path, marker in (
            ('src/frontend/compile/instances.rs', 'pub bodies: [BodyState; 2]'),
            ('src/frontend/compile/instances/provider.rs', 'match &self.instances[record].bodies[profile]'),
            ('src/frontend/compile/instances/provider.rs', 'operations::ProviderRoot::of(&body)'),
            ('src/frontend/compile/instances/provider.rs', 'cached.body.artifact() != body.artifact()'),
            ('src/frontend/compile/operations.rs', 'ProviderRoot::of(program)'),
            ('src/frontend/compile/operations.rs', 'self.providers[&cache].body.artifact() != self.checked[&key].artifact()'),
        ):
            with self.subTest(path=path, marker=marker), self.assertRaisesRegex(ValueError, 'source binding changed'):
                self.check_changed_source(path, marker, 'removed reviewed cache binding')

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

    def check_changed_source(self, name, old, new, checker=None):
        read = Path.read_text
        selected = coverage.ROOT/name
        self.assertIn(old, selected.read_text())
        def altered(path, *args, **kwargs):
            text = read(path, *args, **kwargs)
            return text.replace(old, new, 1) if path == selected else text
        with patch.object(Path, 'read_text', altered):
            if checker is None:
                coverage.check(coverage.ROOT, self.data, self.inventory)
            else:
                checker(coverage.ROOT)

    def test_current_native_dispatch_uses_all_fourteen_canonical_modes(self):
        self.assertEqual(coverage.check_native_dispatch(coverage.ROOT),
                         {mode for row in self.data['paths'] for mode in row['native_modes']})

    def test_new_removed_and_redirected_native_modes_reject(self):
        line = '| "--qirf-native" => some .ordinary'
        replacements = (
            line + '\n  | "--new-mode" => none',
            line + '\n  | "native-alias" => some .ordinary',
            line + '\n  ' + line,
            '',
            '| "--qirf-native" => some .contract',
        )
        for replacement in replacements:
            with self.subTest(replacement=replacement), self.assertRaisesRegex(ValueError, 'native mode'):
                self.check_changed_source('lean-kernel/Protocol/NativeContext.lean', line, replacement,
                                          coverage.check_native_dispatch)

    def test_accepting_default_or_inconsistent_mode_name_rejects(self):
        for old, new in (
            ('| _ => none', '| _ => some .ordinary'),
            ('| .ordinary => "--qirf-native"', '| .ordinary => "--alias"'),
            ('def Mode.parse : String → Option Mode',
             'private def parseOther : String → Option Mode'),
        ):
            with self.subTest(new=new), self.assertRaisesRegex(ValueError, 'native mode'):
                self.check_changed_source('lean-kernel/Protocol/NativeContext.lean', old, new,
                                          coverage.check_native_dispatch)

    def test_native_main_cannot_bypass_context_or_missing_version_check(self):
        for old, new in (
            ('QleisliKernel.Cli.runNativeContext selected version',
             'QleisliKernel.Cli.runValidity version'),
            ('QleisliKernel.Cli.runNativeContext selected ""',
             'QleisliKernel.Cli.runNativeContext selected "0.3.0-beta"'),
            ('| [mode, version] =>', '| [mode, version] =>\n    return 0\n  | [mode, version] =>'),
            ('    | none => QleisliKernel.Cli.run mode version',
             '  | none => QleisliKernel.Cli.run mode version'),
            ('| _ => QleisliKernel.Cli.usage', '| _ => pure 0'),
        ):
            with self.subTest(new=new), self.assertRaisesRegex(ValueError, 'native dispatch'):
                self.check_changed_source('lean-kernel/Main.lean', old, new,
                                          coverage.check_native_dispatch)

    def test_native_context_guards_and_original_bindings_are_required(self):
        for path, markers in (
            ('lean-kernel/Protocol/NativeContext.lean', [
                'guard (requestedProduct == productVersion) .version',
                'let input ← lift (Packet.read bytes)\n  let value ← check mode bytes',
                'guard (decide (scope mode value = input.scope)) .packet',
                'theorem run_edition ',
            ]),
            ('lean-kernel/Protocol/ExecutionView/Packet.lean', [
                'else if u32 bytes 4 != 2026 then .error .edition',
            ]),
            ('src/interchange/native_context.rs', [
                'fields[1] != mode.status()', 'fields[2] != edition.as_str()',
                'fields[3] != env!("CARGO_PKG_VERSION")',
                'fields[4] != mode.argument()', 'fields[5] != scope.name()',
                '!mode.permits(scope)',
            ]),
            ('lean-kernel/Protocol/NativeContext/Bindings.lean', [
                'theorem run_ordinary_root_safe ', 'theorem run_contract_binding ',
                'theorem run_hierarchy_binding ', 'theorem run_engineering_pure_binding ',
                'theorem run_engineering_tensor_binding ',
                'theorem run_engineering_instrument_binding ',
                'theorem run_engineering_target_binding ',
                'theorem run_readout_binding ', 'theorem run_preparation_binding ',
            ]),
        ):
            for marker in markers:
                self.assertEqual((coverage.ROOT/path).read_text().count(marker), 1)
                with self.subTest(path=path, marker=marker), self.assertRaisesRegex(ValueError, 'source binding changed'):
                    self.check_changed_source(path, marker, 'removed binding')

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
