"""Ensure the RSS/decision harness cannot count crashes or missing data as success."""
import json
import unittest

from test_json_prescan import checked_memory, checked_response, large_input


class JsonPrescanHarness(unittest.TestCase):
    def test_crashes_and_malformed_rejections_do_not_count_as_parser_refusals(self):
        for code, stdout, stderr in [
                (-9, '', ''), (0, 'error\nno\n', ''), (1, '', ''),
                (1, 'accepted\n', ''), (1, 'error\nno\n', 'warning')]:
            with self.assertRaises(ValueError):
                checked_response(dict(returncode=code, stdout=stdout, stderr=stderr), False)
        checked_response(dict(returncode=1, stdout='error\nno\n', stderr=''), False)

    def test_native_memory_probes_require_the_exact_schema_refusal(self):
        reply = 'qleisli.native-result 3\nerror\ninvalid_ir\n'
        checked_response(dict(returncode=1, stdout=reply, stderr=''), True, native=True)
        for code, stdout in [(0, reply), (-9, reply), (1, reply + 'extra'),
                             (1, reply.replace('invalid_ir', 'format'))]:
            with self.assertRaises(ValueError):
                checked_response(dict(returncode=code, stdout=stdout, stderr=''), True, native=True)

    def test_missing_or_excessive_rss_fails_the_measurement(self):
        for peak in [0, -1, 101, 1151 * 1024 * 1024]:
            with self.assertRaises(ValueError):
                checked_memory(dict(peak_rss_bytes=peak, rss_ceiling_bytes=100))
        checked_memory(dict(peak_rss_bytes=100, rss_ceiling_bytes=100))

    def test_memory_inputs_are_valid_json_at_the_requested_byte_size(self):
        for size in [100, 1024, 4096]:
            for kind in ['string', 'array']:
                data = large_input(kind, size)
                self.assertEqual(len(data), size)
                value = json.loads(data)
                self.assertIsInstance(value, str if kind == 'string' else list)
                if kind == 'array':
                    self.assertTrue(value)
                    self.assertTrue(all(item == 0 for item in value))


if __name__ == '__main__':
    unittest.main()
