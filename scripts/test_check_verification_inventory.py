#!/usr/bin/env python3
"""Mutation checks for the VM-22 coverage gate.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from check_verification_inventory import ROOT, INVENTORY, check, digest, public_surface, variants


class InventoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='qleisli-vm22-inventory-')
        cls.addClassCleanup(cls.temp.cleanup)
        cls.root = Path(cls.temp.name)
        cls.baseline = json.loads((ROOT/INVENTORY).read_text())
        files = {s['path'] for s in cls.baseline['sources']}
        files |= set(cls.baseline['corpus']['pinned_files'])
        files |= set(cls.baseline['comparison']['pinned_files'])
        files |= {g[k]['path'] for g in cls.baseline['groups'] for k in ['positive','negative']}
        files |= {c['test'].split('#')[0] for c in cls.baseline['capacities']}
        files |= {'lean/schema-registry.json', INVENTORY}
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

    def test_capacity_test_and_replacement_are_required(self):
        self.data['capacities'][0]['replacement']=[]
        self.bad('incomplete capacity replacement')

    def test_corpus_history_remains_frozen(self):
        name=next(iter(self.data['corpus']['pinned_files']))
        self.data['corpus']['pinned_files'][name]='0'*64
        self.bad('corpus baseline changed')

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
        self.bad('does not select production dual')

    def test_inventory_cannot_transfer_production_authority(self):
        self.data['authority']='Lean only'
        self.bad('cannot change production authority')


if __name__=='__main__': unittest.main()
