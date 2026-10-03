"""Transport failures cannot masquerade as matching negative decisions."""
import unittest
from test_native_acceptance_replay import decision


class NativeReplay(unittest.TestCase):
    def test_acceptance_requires_clean_success(self):
        self.assertEqual(decision(0, 'accepted\n', '', False), (True, 'native'))
        for code, output, error in [(1, 'accepted\n', ''), (0, 'accepted', ''),
                                    (0, 'accepted\nextra\n', ''), (0, 'accepted\n', 'panic')]:
            with self.assertRaises(ValueError):
                decision(code, output, error, False)

    def test_only_explicit_native_rejections_count(self):
        for code in ['format', 'invalid_ir', 'contract', 'limit']:
            message = f'{code}: Lean native checker rejected the artifact/request; no fallback\n'
            self.assertEqual(decision(1, f'error\t{code}\n', message, False), (False, 'native'))
            with self.assertRaises(ValueError):
                decision(101, f'error\t{code}\n', message, False)
        for code, reason in [('limit', 'Lean dual checker timed out; no fallback'),
                             ('format', 'unknown dual response protocol'),
                             ('io', 'cannot start Lean dual checker'),
                             ('unsupported', 'native execution view not implemented')]:
            with self.assertRaises(ValueError):
                decision(1, f'error\t{code}\n', f'{code}: {reason}\n', False)

    def test_empty_file_bound_is_not_a_general_rejection_escape(self):
        message = 'limit: proposal files must contain 1..16777216 bytes\n'
        self.assertEqual(decision(1, 'error\tlimit\n', message, True), (False, 'proposal-bound'))
        with self.assertRaises(ValueError):
            decision(1, 'error\tlimit\n', message, False)


if __name__ == '__main__':
    unittest.main()
