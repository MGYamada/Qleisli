#!/usr/bin/env python3
"""Mutation checks for the VM-22 coverage gate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from current_metadata import read_json

from check_verification_inventory import ROOT, INVENTORY, check, check_language_primitives, digest, public_surface, test_names, variants


class InventoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='qleisli-vm22-inventory-')
        cls.addClassCleanup(cls.temp.cleanup)
        cls.root = Path(cls.temp.name)
        cls.baseline = read_json(ROOT, INVENTORY)
        files = {s['path'] for s in cls.baseline['sources']}
        files |= set(cls.baseline['corpus']['pinned_files'])
        files |= set(cls.baseline['comparison']['pinned_files'])
        files |= {g[k]['path'] for g in cls.baseline['groups'] for k in ['positive','negative']}
        files |= {c['test'].split('#')[0] for c in cls.baseline['capacities']}
        files |= {'lean/schema-registry.json', INVENTORY, 'corpus/manifest.json',
                  'corpus/semantic_faults/manifest.json'}
        for name in files:
            target = cls.root/name
            target.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(ROOT/name,target)

    def setUp(self):
        self.data = copy.deepcopy(self.baseline)

    def bad(self, fragment):
        self.assertTrue(any(fragment in e for e in check(self.root,self.data)),check(self.root,self.data))

    def test_frozen_repository_is_covered(self):
        self.assertEqual(check(self.root,self.data),[])

    def test_typed_source_growth_rejects_even_after_enum_and_hash_refresh(self):
        path = self.root/'src/frontend/primitive.rs'
        original = path.read_text()
        try:
            path.write_text(original.replace('pub enum PrimitiveId {',
                                             'pub enum PrimitiveId { ExtraSourceIdentity,'))
            for source in self.data['sources']:
                if source['path'] == 'src/frontend/primitive.rs':
                    source['sha256'] = digest(path)
            enum = next(row for row in self.data['enums']
                        if (row['path'], row['name']) == ('src/frontend/primitive.rs', 'PrimitiveId'))
            enum['members']['ExtraSourceIdentity'] = {'declaration': 'ExtraSourceIdentity', 'group': 'source'}
            self.bad('unreviewed typed language primitive identity set')
        finally:
            path.write_text(original)

    def test_typed_spelling_cannot_restore_a_retired_alias(self):
        path = self.root/'src/frontend/primitive.rs'
        original = path.read_text()
        try:
            path.write_text(original.replace('=> "global_phase_eighth"', '=> "phase_eighth"'))
            with self.assertRaisesRegex(ValueError, 'typed language primitive spelling drift'):
                check_language_primitives(self.root)
        finally:
            path.write_text(original)

    def test_typed_spelling_early_return_cannot_hide_behind_canonical_rows(self):
        path = self.root/'src/frontend/primitive.rs'
        original = path.read_text()
        try:
            path.write_text(original.replace(
                'match self {',
                'if self == Self::H { return "different_h"; } match self {', 1))
            with self.assertRaisesRegex(ValueError, 'typed language primitive spelling body must remain canonical'):
                check_language_primitives(self.root)
        finally:
            path.write_text(original)

    def test_typed_all_cannot_duplicate_or_omit_an_identity(self):
        path = self.root/'src/frontend/primitive.rs'
        original = path.read_text()
        try:
            path.write_text(original.replace('Self::H,', 'Self::H, Self::H,', 1))
            with self.assertRaisesRegex(ValueError, 'typed language primitive ALL drift'):
                check_language_primitives(self.root)
        finally:
            path.write_text(original)

    def test_typed_lookup_cannot_add_a_hidden_alias(self):
        path = self.root/'src/frontend/primitive.rs'
        original = path.read_text()
        try:
            path.write_text(original.replace(
                'Self::ALL.iter().copied().find(|id| id.spelling() == name)',
                'if name == "phase_eighth" { return Some(Self::GlobalPhaseEighth); }\n'
                '        Self::ALL.iter().copied().find(|id| id.spelling() == name)'))
            with self.assertRaisesRegex(ValueError, 'typed language primitive lookup must remain canonical'):
                check_language_primitives(self.root)
        finally:
            path.write_text(original)

    def test_new_constructor_is_rejected_even_if_hash_is_updated(self):
        path = self.root/'src/ir.rs'
        original = path.read_text()
        try:
            path.write_text(original.replace('pub enum RawOp {','pub enum RawOp { NewOperation,'))
            for s in self.data['sources']:
                if s['path']=='src/ir.rs': s['sha256']=digest(path)
            self.bad('constructor coverage drift')
        finally: path.write_text(original)

    def test_changed_field_cannot_hide_under_same_constructor_name(self):
        enum = next(e for e in self.data['enums'] if e['name']=='RawOp')
        enum['members']['Split']['declaration'] += ' extra: u32'
        self.bad('constructor field drift')

    def test_missing_published_family_is_rejected(self):
        self.data['enums']=[e for e in self.data['enums'] if e['name']!='ProtectedUse']
        self.bad('missing published constructor')

    def test_new_instrument_result_variant_cannot_hide_behind_an_updated_hash(self):
        path = self.root/'src/contract/instrument.rs'
        original = path.read_text()
        try:
            path.write_text(original.replace('pub enum InstrumentResult {',
                                             'pub enum InstrumentResult { UncheckedEvidence,'))
            for source in self.data['sources']:
                if source['path'] == 'src/contract/instrument.rs':
                    source['sha256'] = digest(path)
            self.bad('constructor coverage drift: InstrumentResult')
        finally:
            path.write_text(original)

    def test_missing_raw_only_coverage_group_is_rejected(self):
        self.data['groups']=[g for g in self.data['groups'] if g['id']!='raw-QuantumIf']
        self.bad('unmapped constructor')

    def test_test_name_in_comment_is_not_a_test(self):
        self.data['groups'][0]['negative']['test']='imaginary_missing_test'
        self.bad('missing test')
        self.assertEqual(variants('// pub enum E { Fake }\npub enum E { Real(Vec<(u8,u8)>), }','E'),{'Real':'Real(Vec<(u8,u8)>)'})

    def test_private_checking_change_requires_review(self):
        self.data['sources'][0]['sha256']='0'*64
        self.bad('frozen source changed')

    def test_array_signature_keeps_later_parameters_and_return_type(self):
        source = '''pub fn execute(&self, input: &[[f64; 2]],
            reference_dimension: usize, limits: Limits) -> Result<State> { todo!() }
            pub const fn dimensions<const N: usize>(x: [u8; { N + 1 }])
                -> Container<{ 1 < 2 }> { todo!() }
            pub fn callback(f: impl Fn(u8) -> [u8; 2]) -> Result<()>;
        '''
        self.assertEqual(public_surface(source)['functions'], sorted([
            'pub fn execute(&self, input: &[[f64; 2]], reference_dimension: usize, limits: Limits) -> Result<State>',
            'pub const fn dimensions<const N: usize>(x: [u8; { N + 1 }]) -> Container<{ 1 < 2 }>',
            'pub fn callback(f: impl Fn(u8) -> [u8; 2]) -> Result<()>',
        ]))
        path = self.root/'src/interchange/hierarchical/execution.rs'
        original = path.read_text()
        try:
            path.write_text(original.replace('reference_dimension: usize', 'reference_dimension: u32'))
            for s in self.data['sources']:
                if s['path'] == str(path.relative_to(self.root)):
                    s['sha256'] = digest(path)
            self.bad('public API/capacity drift')
        finally:
            path.write_text(original)

    def test_new_checking_file_requires_inventory_entry(self):
        path=self.root/'src/contract/new_checker.rs'
        try:
            path.write_text('pub fn new_check() {}')
            self.bad('unlisted checking source')
        finally: path.unlink()

    def test_boundary_must_include_independent_request_and_binding(self):
        self.data['boundaries'][0]['request']=''
        self.bad('empty boundary field')

    def test_carrier_contract_cannot_claim_ast_runtime_or_inverse_authority(self):
        for field, value in (
            ('binding', 'Matching metadata proves the original source function'),
            ('domain', 'Every enum supports ordinary runtime, matching, inverse and control'),
            ('encoding', 'Old inspection success replies are sufficient'),
            ('failure', 'An unavailable checker may fall back to a producer receipt'),
        ):
            self.data = copy.deepcopy(self.baseline)
            next(row for row in self.data['boundaries'] if row['id'] == 'finite-carrier')[field] = value
            with self.subTest(field=field):
                self.bad('unreviewed finite-carrier boundary contract')

    def test_carrier_public_source_requires_its_distinct_boundary(self):
        self.data['boundaries'] = [row for row in self.data['boundaries'] if row['id'] != 'finite-carrier']
        self.bad('missing finite-carrier public boundary')

    def test_new_carrier_constructor_cannot_hide_behind_updated_source_identity(self):
        path = self.root/'src/interchange/carrier.rs'
        original = path.read_text()
        try:
            path.write_text(original.replace('pub enum Atom {', 'pub enum Atom { UncheckedNominal,'))
            next(row for row in self.data['sources'] if row['path'] == 'src/interchange/carrier.rs')['sha256'] = digest(path)
            self.bad('constructor coverage drift: Atom')
        finally:
            path.write_text(original)

    def test_qmatch_component_scope_and_failure_cannot_be_widened(self):
        for field, value in (
            ('binding', 'Source spelling proves the original function and all lowering'),
            ('domain', 'All general qmatch source programs execute and QS is complete'),
            ('encoding', 'An ordinary-mode success may authorize the source component'),
            ('failure', 'A missing native checker may use cached acceptance'),
        ):
            self.data = copy.deepcopy(self.baseline)
            next(row for row in self.data['boundaries'] if row['id'] == 'qmatch-component')[field] = value
            with self.subTest(field=field):
                self.bad('unreviewed qmatch-component boundary contract')

    def test_qmatch_public_source_requires_its_distinct_boundary(self):
        self.data['boundaries'] = [row for row in self.data['boundaries'] if row['id'] != 'qmatch-component']
        self.bad('missing qmatch-component public boundary')

    def test_nominal_declaration_family_cannot_be_omitted(self):
        self.data['enums'] = [row for row in self.data['enums'] if row['name'] != 'TypeDeclKind']
        self.bad('unlisted public constructor family: TypeDeclKind')

    def test_multiline_native_test_attributes_require_a_real_uncommented_test(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary)/'tests.rs'
            path.write_text('''
                // #[test] fn fake_comment() {}
                const EXAMPLE: &str = "#[test] fn fake_literal() {}";
                #[test]
                #[cfg_attr(
                    not(qleisli_native_tests),
                    ignore = "requires native checker"
                )]
                fn actual_native() {}
                #[cfg_attr(not(qleisli_native_tests), ignore = "native")]
                #[test]
                fn actual_reordered() {}
                fn helper_without_test() {}
            ''')
            self.assertEqual(test_names(path), {'actual_native', 'actual_reordered'})

    def test_instrument_engineering_contract_cannot_promote_zero_or_claim_hardware(self):
        for field, value in (
            ('status', 'native exact acceptance'),
            ('binding', 'epsilon zero yields an accepted program and permits exact cleanup'),
            ('domain', 'qirf-r8-instrument-v1 certifies emitted hardware and resources'),
            ('request', 'probability tables without original expected artifact or typed interfaces'),
            ('encoding', 'inspection without a host execution view is sufficient'),
        ):
            self.data = copy.deepcopy(self.baseline)
            boundary = next(row for row in self.data['boundaries'] if row['id'] == 'engineering-instrument')
            boundary[field] = value
            with self.subTest(field=field):
                self.bad('unreviewed engineering-instrument boundary contract')

    def test_instrument_engineering_public_source_requires_its_own_boundary(self):
        self.data['boundaries'] = [row for row in self.data['boundaries'] if row['id'] != 'engineering-instrument']
        self.bad('missing engineering-instrument public boundary')

    def test_tensor_engineering_contract_retains_originals_budget_and_claim_kind(self):
        for field, value in (
            ('status', 'native exact acceptance'),
            ('binding', 'two old component receipts are sufficient for any parent'),
            ('request', 'runtime precision with no explicit total budget'),
            ('encoding', 'inspection compares only the parent graph'),
            ('domain', 'epsilon zero supplies clean release and target resources'),
        ):
            self.data = copy.deepcopy(self.baseline)
            boundary = next(row for row in self.data['boundaries'] if row['id'] == 'engineering-pure-tensor')
            boundary[field] = value
            with self.subTest(field=field):
                self.bad('unreviewed engineering-pure-tensor boundary contract')

    def test_tensor_engineering_public_source_requires_its_own_boundary(self):
        self.data['boundaries'] = [row for row in self.data['boundaries'] if row['id'] != 'engineering-pure-tensor']
        self.bad('missing engineering-pure-tensor public boundary')

    def test_target_engineering_contract_retains_literal_target_and_scope(self):
        for field, value in (
            ('status', 'native exact acceptance'),
            ('binding', 'A producer target graph and stale ideal receipts suffice'),
            ('request', 'probability-only comparison without an original ideal'),
            ('encoding', 'inspection does not need target bytes or ordered gate word'),
            ('domain', 'arbitrary-input pure coherent target with clean release'),
            ('limits', 'unbounded target bytes and gate count'),
        ):
            self.data = copy.deepcopy(self.baseline)
            next(row for row in self.data['boundaries'] if row['id'] == 'engineering-openqasm')[field] = value
            with self.subTest(field=field):
                self.bad('unreviewed engineering-openqasm boundary contract')

    def test_target_engineering_public_source_requires_its_own_boundary(self):
        self.data['boundaries'] = [row for row in self.data['boundaries'] if row['id'] != 'engineering-openqasm']
        self.bad('missing engineering-openqasm public boundary')

    def test_capacity_test_and_replacement_are_required(self):
        self.data['capacities'][0]['replacement']=[]
        self.bad('incomplete capacity replacement')

    def test_corpus_history_remains_frozen(self):
        name=next(iter(self.data['corpus']['pinned_files']))
        self.data['corpus']['pinned_files'][name]='0'*64
        self.bad('corpus baseline changed')

    def test_current_corpus_additions_cannot_rewrite_original_cases(self):
        path=self.root/'corpus/manifest.json'
        original=path.read_text()
        try:
            data=json.loads(original)
            data['cases'][0]['contract']='different original meaning'
            path.write_text(json.dumps(data))
            self.bad('original corpus census changed')
        finally: path.write_text(original)

    def test_current_fault_additions_cannot_rewrite_original_faults(self):
        path=self.root/'corpus/semantic_faults/manifest.json'
        original=path.read_text()
        try:
            data=json.loads(original)
            data['cases'][0]['reference']='different/reference'
            path.write_text(json.dumps(data))
            self.bad('original corpus fault census changed')
        finally: path.write_text(original)

    def test_comparison_bytes_cannot_be_silently_refreshed(self):
        name=next(iter(self.data['comparison']['pinned_files']))
        self.data['comparison']['pinned_files'][name]='0'*64
        self.bad('comparison fixture changed')

    def test_external_schema_and_packaging_cannot_enable_authority(self):
        path=self.root/'lean/schema-registry.json'
        original=path.read_text()
        try:
            registry=json.loads(original)
            registry['entries'][0]['external_enabled']=True
            path.write_text(json.dumps(registry))
            self.bad('external schema enabled')
        finally: path.write_text(original)
        self.data['native_packaging'][0]['selected_for_dual']=True
        self.bad('forbids dual packaging')

    def test_inventory_cannot_transfer_production_authority(self):
        self.data['authority']='Lean only'
        self.bad('cannot change production authority')


if __name__=='__main__': unittest.main()
