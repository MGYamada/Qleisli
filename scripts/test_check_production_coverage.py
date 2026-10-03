"""Migration coverage must fail closed on omitted or newly exposed paths."""
import copy
import json
import unittest
import check_production_coverage as coverage


class ProductionCoverage(unittest.TestCase):
    def setUp(self):
        self.data = json.loads((coverage.ROOT/coverage.COVERAGE).read_text())
        self.inventory = json.loads((coverage.ROOT/coverage.INVENTORY).read_text())

    def test_current_review_accounts_for_all_groups_and_boundaries(self):
        result = coverage.check(coverage.ROOT, self.data, self.inventory)
        self.assertEqual(result['groups'], 36)
        self.assertEqual(result['public_boundaries'], 20)
        self.assertEqual(result['authority'], 'Lean')
        self.assertEqual(result['target_authority'], 'Lean')
        self.assertEqual(result['migration'], 'in-progress')

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
            with self.assertRaises(ValueError):
                coverage.check(coverage.ROOT, data, self.inventory)

    def test_new_entrypoint_or_signature_requires_review(self):
        self.inventory['boundaries'][0]['entry_points'].append('new public entry')
        with self.assertRaisesRegex(ValueError, 'surface changed'):
            coverage.check(coverage.ROOT, self.data, self.inventory)
        self.data['surface_sha256'] = coverage.surface_identity(self.inventory)
        with self.assertRaisesRegex(ValueError, 'entry point'):
            coverage.check(coverage.ROOT, self.data, self.inventory)


if __name__ == '__main__':
    unittest.main()
