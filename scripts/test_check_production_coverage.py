"""Migration coverage must fail closed on omitted or newly exposed paths."""
import copy
import json
from pathlib import Path
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
        self.assertEqual(result['public_boundaries'], 20)
        self.assertEqual(result['authority'], 'Lean')
        self.assertEqual(result['target_authority'], 'Lean')
        self.assertEqual(result['migration'], 'single-lean-acceptance-implemented')
        self.assertEqual(result['production_paths'], 22)
        self.assertEqual(result['native_modes'], 9)
        self.assertEqual(result['published_baseline'], '0.2.9')
        self.assertEqual(result['development_version'], '0.3.0-alpha')
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
