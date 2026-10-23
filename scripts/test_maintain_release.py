"""Version synchronization cannot edit dependencies or silently refresh evidence."""
import json
from pathlib import Path
import tempfile
import tomllib
import unittest
from unittest.mock import patch
import maintain_release as release


class ReleaseMaintenance(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for name, section in release.MANIFESTS.items():
            header = '[' + section + ']\n' if section else ''
            self.write(name, header + 'name="qleisli"\nversion = "0.2.8"\n[dependencies.test]\nversion="9.8.7"\n')
        self.write('Cargo.lock', 'version=4\n\n[[package]]\nname="other"\nversion="0.2.8"\n\n[[package]]\nname="qleisli"\nversion="0.2.8"\n')
        self.write('python/qleisli/__init__.py', '__version__ = "0.2.8"\n')
        self.write(release.INVENTORY, json.dumps(dict(sources=[dict(path='python/qleisli/__init__.py',
                   sha256=release.digest((self.root/'python/qleisli/__init__.py').read_bytes()), surface=None)])))

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def test_plan_is_read_only_and_preserves_dependency_versions(self):
        before = (self.root/'Cargo.toml').read_bytes()
        changes = release.version_plan(self.root, '0.2.9')
        self.assertEqual(len(changes), 8)
        self.assertEqual((self.root/'Cargo.toml').read_bytes(), before)
        for name in release.MANIFESTS:
            self.assertIn('version="9.8.7"', changes[name])
        self.assertIn('name="other"\nversion="0.2.8"', changes['Cargo.lock'])
        data, rows = release.inventory_plan(self.root, changes, [])
        self.assertEqual(rows[0]['classification'], 'version-only')
        self.assertEqual(data['sources'][0]['sha256'], release.digest(changes['python/qleisli/__init__.py'].encode()))

    def test_preexisting_edits_are_not_disguised_as_version_only(self):
        self.write('python/qleisli/__init__.py', '__version__ = "0.2.8"\nraise RuntimeError("changed behavior")\n')
        changes = release.version_plan(self.root, '0.2.9')
        _, rows = release.inventory_plan(self.root, changes, [])
        self.assertEqual(rows[0]['classification'], 'review-required')
        _, rows = release.inventory_plan(self.root, changes, ['python/qleisli/__init__.py'])
        self.assertEqual(rows[0]['classification'], 'reviewed')

    def test_prerelease_updates_exact_product_slots_and_is_repeatable(self):
        self.write('lean-kernel/Protocol/Product.lean', 'def productVersion : String := "0.2.8"\n')
        self.write('README.md', 'Development version: 0.2.8 (unpublished). Latest published version: 0.2.7.\n'
                   'macOS distribution is under consideration.\n')
        source_url = 'https://github.com/MGYamada/Qleisli/blob/v0.2.8/README.md'
        history_url = 'https://github.com/MGYamada/Qleisli/releases/tag/v0.2.7'
        self.write('README.crates.md', 'Package version: **0.2.8**\n'
                   'macOS distribution is under consideration.\n' + source_url + '\n' + history_url + '\n')
        self.write('python/README.md', 'separately installed Qleisli 0.2.8 Rust executable\n')
        self.write('src/lib.rs', '//! [Source](' + source_url + ')\n')
        self.write('CHANGELOG.md', '## 0.2.8\nPreviously selected version.\n')
        for version in ['0.3.0-alpha', '0.3.0-alpha.1', '0.3.0-beta.2', '0.3.0']:
            with self.subTest(version=version):
                changes = release.version_plan(self.root, version)
                self.assertEqual(len(changes), 13)
                for name, section in release.MANIFESTS.items():
                    manifest = tomllib.loads(changes[name])
                    product = manifest[section] if section else manifest
                    self.assertEqual(product['version'], version)
                    self.assertEqual(manifest['dependencies']['test']['version'], '9.8.7')
                packages = tomllib.loads(changes['Cargo.lock'])['package']
                self.assertEqual(packages[0]['version'], '0.2.8')
                self.assertEqual(packages[1]['version'], version)
                self.assertEqual(changes['python/qleisli/__init__.py'], '__version__ = "' + version + '"\n')
                self.assertEqual(changes['lean-kernel/Protocol/Product.lean'],
                                 'def productVersion : String := "' + version + '"\n')
                self.assertIn('Latest published version: 0.2.7.', changes['README.md'])
                self.assertIn('Development version: ' + version, changes['README.md'])
                self.assertIn('Package version: **' + version + '**', changes['README.crates.md'])
                for name in ['README.md', 'README.crates.md']:
                    self.assertIn('macOS distribution is under consideration.', changes[name])
                    self.assertNotIn('cargo install', changes[name])
                self.assertIn('separately installed Qleisli ' + version + ' Rust', changes['python/README.md'])
                for name in ['README.crates.md', 'src/lib.rs']:
                    self.assertIn(source_url.replace('v0.2.8/', 'v' + version + '/'), changes[name])
                self.assertIn(history_url, changes['README.crates.md'])
                self.assertNotIn('CHANGELOG.md', changes)
                for name, text in changes.items():
                    self.write(name, text)
                self.assertEqual(release.version_plan(self.root, version), {})

    def test_malformed_current_document_version_cannot_be_partially_replaced(self):
        for version in ['0.3.0-alpha.01', '0.3.0-', '0.3.0_alpha', '0.3.0-α', '0.3.0+build']:
            self.write('README.md', 'Development version: ' + version + '\n')
            with self.subTest(version=version), self.assertRaisesRegex(ValueError, 'Development version:'):
                release.version_plan(self.root, '0.3.0-alpha')

    def test_shared_semver_python_prerelease_stages(self):
        for version in ['0.3.0-alpha', '0.3.0-alpha.1', '0.3.0-alpha.10',
                        '0.3.0-beta', '0.3.0-beta.2', '0.3.0-rc', '0.3.0-rc.10']:
            with self.subTest(version=version):
                changes = release.version_plan(self.root, version)
                self.assertIn('version = "' + version + '"', changes['Cargo.toml'])

    def test_nonshared_selectors_reject_before_synchronization(self):
        before = {path: path.read_bytes() for path in self.root.rglob('*') if path.is_file()}
        # Unknown stages cannot build Python metadata. Attached counters have
        # lexicographic SemVer order, and .0 aliases the unnumbered Python stage.
        for version in ['0.3.0-dev', '0.3.0-0', '0.3.0-01a', '0.3.0-x-y.Z9',
                        '0.3.0-alpha2', '0.3.0-alpha10', '0.3.0-beta-2',
                        '0.3.0-alpha.0', '0.3.0-beta.0', '0.3.0-rc.0']:
            with self.subTest(version=version), self.assertRaisesRegex(ValueError, 'SemVer/Python ordering'):
                release.version_plan(self.root, version)
        self.assertEqual({path: path.read_bytes() for path in before}, before)

    def test_invalid_versions_and_unknown_review_paths_reject(self):
        for version in ['1.0.0', '0.02.9', '0.3.00', '0.2.9\n', '0.3.0-',
                        '0.3.0-01', '0.3.0-alpha.01', '0.3.0-alpha..1',
                        '0.3.0-.alpha', '0.3.0-alpha.', '0.3.0-alpha_1',
                        '0.3.0-α', '0.3.0+build', '0.3.0-alpha+build', 'v0.3.0-alpha']:
            with self.subTest(version=version), self.assertRaises(ValueError):
                release.version_plan(self.root, version)
        with self.assertRaises(ValueError):
            release.inventory_plan(self.root, {}, ['not-in-inventory'])

    def test_audit_failure_cannot_be_reported_as_completed(self):
        report = self.root/'report.json'
        with patch.object(release, 'command', side_effect=ValueError('audit failed')):
            code = release.main(['--root', str(self.root), '--version', '0.2.9', '--write', '--refresh-registry', '--report', str(report)])
        self.assertEqual(code, 1)
        data = json.loads(report.read_text())
        self.assertEqual(data['status'], 'failed')
        self.assertTrue(data['changes'])
        self.assertEqual(data['error'], 'audit failed')


    def test_write_compact_inventory_rows_keeps_data_order_and_report_format(self):
        runtime = 'python/qleisli/__init__.py'
        unchanged = 'python/aaa_metadata.py'
        old_runtime = '__version__ = "0.2.8"\n# ζ ≤ [quoted] and \\escaped\n'
        new_runtime = old_runtime.replace('"0.2.8"', '"0.2.9"', 1)
        self.write(runtime, old_runtime)
        self.write(unchanged, 'LABEL = "unchanged"\n')
        inventory = {
            'format': 'serializer regression',
            'before': {'sources': [], 'note': 'ζ ≤ [brackets] "quoted"\n literal \\u03b6'},
            'sources': [
                {'path': runtime, 'sha256': release.digest(old_runtime.encode()),
                 'surface': None, 'group': 'source-config'},
                {'surface': None, 'group': 'source \"ζ\"\n[config]', 'path': unchanged,
                 'sha256': release.digest((self.root / unchanged).read_bytes())},
            ],
            'after': {'note': '雪\nnewline\ttab\\backslash', 'nested': [{}, []]},
        }
        # The source order is deliberately not lexical, and each row has a
        # different key order. Nested sources and escaped text are not markers.
        original = json.dumps(inventory, indent=2, ensure_ascii=False) + '\n'
        self.write(release.INVENTORY, original)
        expected = json.loads(original)
        expected['sources'][0]['sha256'] = release.digest(new_runtime.encode())
        report = self.root / 'report.json'
        with patch.object(release, 'command') as command:
            code = release.main(['--root', str(self.root), '--version', '0.2.9',
                                 '--write', '--report', str(report)])
        self.assertEqual(code, 0)
        self.assertEqual([call.args[0][1:] for call in command.call_args_list], [
            ['scripts/check_verification_inventory.py'],
            ['scripts/check_schema_registry.py', '--source-only'],
            ['scripts/check_docs.py'],
            ['scripts/check_editions.py'],
        ])
        self.assertTrue(all(call.args[1] == self.root.resolve() for call in command.call_args_list))
        self.assertEqual((self.root / runtime).read_text(), new_runtime)
        self.assertEqual((self.root / unchanged).read_text(), 'LABEL = "unchanged"\n')
        actual = (self.root / release.INVENTORY).read_text()
        parsed = json.loads(actual)
        self.assertEqual(parsed, expected)
        self.assertEqual(list(parsed), list(inventory))
        self.assertEqual([list(row) for row in parsed['sources']],
                         [list(row) for row in inventory['sources']])
        self.assertEqual([row['path'] for row in parsed['sources']], [runtime, unchanged])
        marker = '\n  "sources": '
        old_prefix, old_tail = original.split(marker, 1)
        new_prefix, new_tail = actual.split(marker, 1)
        _, old_end = json.JSONDecoder().raw_decode(old_tail)
        _, new_end = json.JSONDecoder().raw_decode(new_tail)
        self.assertEqual(new_prefix, old_prefix)
        self.assertIn('    \"nested\": [{},[]]', new_tail[new_end:])
        self.assertNotEqual(new_tail[new_end:], old_tail[old_end:])
        source_lines = new_tail[:new_end].splitlines()
        self.assertEqual(source_lines, [
            '[',
            '    ' + json.dumps(expected['sources'][0], separators=(',', ':'), ensure_ascii=False) + ',',
            '    ' + json.dumps(expected['sources'][1], separators=(',', ':'), ensure_ascii=False),
            '  ]',
        ])
        self.assertTrue(actual.endswith('\n'))
        raw_report = report.read_bytes()
        result = json.loads(raw_report)
        self.assertEqual(result['status'], 'passed')
        self.assertEqual(result['version'], '0.2.9')
        self.assertEqual([(row['path'], row['classification']) for row in result['source_review']],
                         [(runtime, 'version-only')])
        # The inventory-specific formatter must not change report encoding.
        self.assertEqual(raw_report, (json.dumps(result, indent=2) + '\n').encode())
        self.assertIn(b'\\u03b6', raw_report)


    def test_current_metadata_small_rows_and_large_records_are_readable(self):
        long = 'x' * 500
        value = {'format': 'row format', 'rows': [
            {'b': 2, 'a': [True, None, 'ζ']},
            {'long': long, 'nested': {'z': 0, 'a': False}},
        ], 'empty': {}}
        actual = release.current_metadata_json(value)
        expected = ('{\n  "format": "row format",\n  "rows": [\n'
                    '    {"b":2,"a":[true,null,"ζ"]},\n'
                    '    {"long":"' + long + '",\n'
                    '      "nested":{"z":0,"a":false}}\n'
                    '  ],\n  "empty": {}\n}\n')
        self.assertEqual(actual, expected)
        self.assertEqual(release.current_metadata_json(json.loads(actual)), actual)

    def test_current_metadata_preserves_recursive_pairs_escapes_and_source_rows(self):
        value = {'groups': [{'two': 2, 'one': 1, 'cells': [-3, 0.25, False, None]}],
                 'sources': [{'path': '雪/"quoted"\nline\t\\literal', 'long': 'x' * 600,
                              'surface': {'z': [3, 2], 'a': []}}],
                 'other': {'sources': [{'long': 'y' * 600, 'value': 1}],
                           'key': 'literal \\u03b6'}}
        expected = json.dumps(value, ensure_ascii=False)
        actual = release.current_metadata_json(value)
        self.assertEqual(json.loads(actual, object_pairs_hook=list),
                         json.loads(expected, object_pairs_hook=list))
        source = '    ' + json.dumps(value['sources'][0], separators=(',', ':'), ensure_ascii=False)
        self.assertIn(source, actual.splitlines())
        self.assertIn('{"long":"' + 'y' * 600 + '",\n', actual)
        nested_row = json.dumps(value['other']['sources'][0], separators=(',', ':'))
        self.assertNotIn(nested_row, actual)
        self.assertEqual(release.inventory_json(value), actual)
        self.assertTrue(actual.endswith('\n'))

    def test_current_metadata_limit_counts_utf8_bytes(self):
        # These rows fit 480 characters but exceed 480 UTF-8 bytes.
        value = {'rows': [{'text': '雪' * 170, 'tail': 0}]}
        actual = release.current_metadata_json(value)
        self.assertIn('    {"text":"' + '雪' * 170 + '",\n', actual)
        self.assertEqual(json.loads(actual), value)


    def test_current_metadata_wraps_complete_utf8_entries_and_keeps_json_kinds(self):
        value = {'rows': [['雪' * 70 + str(i) for i in range(7)]],
                 'kinds': {'object': {}, 'array': [], 'bool': False, 'integer': 0,
                           'float': 0.0, 'null': None, 'text': '[\"a\", true]'}}
        actual = release.current_metadata_json(value)
        def tagged(item):
            if isinstance(item, dict):
                return ('object', tuple((key, tagged(child)) for key, child in item.items()))
            if isinstance(item, list):
                return ('array', tuple(tagged(child) for child in item))
            return (type(item).__name__, item)
        self.assertEqual(tagged(json.loads(actual)), tagged(value))
        self.assertTrue(all(len(line.encode('utf-8')) <= 480 for line in actual.splitlines()))
        self.assertEqual(actual.count('雪' * 70), 7)
        self.assertEqual(release.current_metadata_json(json.loads(actual)), actual)


if __name__ == '__main__':
    unittest.main()
