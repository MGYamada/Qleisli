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
                   'Compiler version `0.2.8`\nOnce 0.2.8 is published\n'
                   'cargo install qleisli --version 0.2.8 --locked\n')
        source_url = 'https://github.com/MGYamada/Qleisli/blob/v0.2.8/README.md'
        history_url = 'https://github.com/MGYamada/Qleisli/releases/tag/v0.2.7'
        self.write('README.crates.md', 'Package version: **0.2.8**\n'
                   'cargo install qleisli --version 0.2.8 --locked\n'
                   'qleisli = "0.2.8"\n'
                   'Current documentation links target `v0.2.8`\n' + source_url + '\n' + history_url + '\n')
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
                self.assertIn('Once ' + version + ' is published', changes['README.md'])
                self.assertIn('cargo install qleisli --version ' + version + ' --locked', changes['README.md'])
                self.assertIn('separately installed Qleisli ' + version + ' Rust', changes['python/README.md'])
                for name in ['README.crates.md', 'src/lib.rs']:
                    self.assertIn(source_url.replace('v0.2.8/', 'v' + version + '/'), changes[name])
                self.assertIn(history_url, changes['README.crates.md'])
                self.assertIn('qleisli = "' + version + '"', changes['README.crates.md'])
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


if __name__ == '__main__':
    unittest.main()
