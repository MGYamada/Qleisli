#!/usr/bin/env python3
"""Exercise Git whitespace checks on committed, staged and working sources.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from check_whitespace import check


class WhitespaceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.git('init', '-q')
        (self.root / 'source').write_text('original\n')
        self.git('add', 'source')
        self.git('commit', '-qm', 'baseline')

    def git(self, *args):
        return subprocess.check_output(
            ['git', '-c', 'user.name=Test', '-c', 'user.email=test@example.invalid',
             '-c', 'commit.gpgsign=false', *args], cwd=self.root)

    def test_complete_tree_keeps_unchanged_committed_errors_visible(self):
        (self.root / 'source').write_text('bad \n')
        self.git('commit', '-qam', 'bad baseline')
        self.assertFalse(check(self.root))
        self.assertFalse(check(self.root, committed=True))
        (self.root / 'source').write_text('repaired\n')
        self.assertTrue(check(self.root))
        self.assertFalse(check(self.root, committed=True))

    def test_unstaged_staged_and_untracked_inputs_are_checked(self):
        self.assertTrue(check(self.root))
        for name in ('source', 'new file\nwith newline'):
            with self.subTest(name=name):
                path = self.root / name
                path.write_text('bad \n')
                self.assertFalse(check(self.root))
                self.assertTrue(check(self.root, committed=True))
                self.git('add', name)
                self.assertFalse(check(self.root))
                path.write_text('clean\n')
                self.assertTrue(check(self.root))
                self.git('add', name)
        (self.root / 'source').unlink()
        self.assertTrue(check(self.root))

    def test_frozen_eof_attribute_does_not_disable_other_whitespace_rules(self):
        (self.root / '.gitattributes').write_text('frozen whitespace=-blank-at-eof\n')
        path = self.root / 'frozen'
        # This also exercises attributes on a new, not-yet-staged copy.
        path.write_text('preserved\n\n')
        self.assertTrue(check(self.root))
        self.git('add', '.')
        self.git('commit', '-qm', 'frozen source')
        self.assertTrue(check(self.root, committed=True))
        for bad in ('bad \n\n', ' \tindented\n'):
            path.write_text(bad)
            self.assertFalse(check(self.root))
        path.write_text('preserved\n\n')
        (self.root / 'ordinary').write_text('not frozen\n\n')
        self.assertFalse(check(self.root))

    def test_ignored_generated_output_is_not_source(self):
        (self.root / '.gitignore').write_text('generated/\n')
        (self.root / 'generated').mkdir()
        (self.root / 'generated/log').write_text('raw output \n\n')
        self.assertTrue(check(self.root))

    def test_disappearing_untracked_input_is_not_a_clean_difference(self):
        path = self.root / 'vanished'
        path.write_text('clean before removal\n')
        run = subprocess.run

        def remove_before_diff(command, *args, **kwargs):
            if '--no-index' in command and command[-1] == path.name:
                path.unlink()
            return run(command, *args, **kwargs)

        with patch('check_whitespace.subprocess.run', side_effect=remove_before_diff):
            self.assertFalse(check(self.root))

    def test_git_errors_are_not_success(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(subprocess.CalledProcessError):
                check(Path(directory))


if __name__ == '__main__':
    unittest.main()
