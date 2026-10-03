"""Version synchronization cannot edit dependencies or silently refresh evidence."""
import json
from pathlib import Path
import tempfile
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
        self.assertEqual(len(changes), 7)
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

    def test_invalid_versions_and_unknown_review_paths_reject(self):
        for version in ['1.0.0', '0.02.9', '0.2.9\n', '0.2.9-beta']:
            with self.assertRaises(ValueError):
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
