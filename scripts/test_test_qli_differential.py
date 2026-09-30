"""Independent analytic calibrations and counterexamples for the test oracle.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import math
import random
import unittest
from test_qli_differential import SEED, execute, gate, make_case, project, rotate


class ReferenceOracle(unittest.TestCase):
    def test_h_and_bell_match_closed_form_complex_amplitudes(self):
        r = 1 / math.sqrt(2)
        plus = gate([1, 0], "h", [0])
        self.assertEqual(plus, [r, r])
        bell = execute([1, 0, 0, 0], [("h", [0]), ("cnot", [0, 1])])
        self.assertEqual(bell, [r, 0, 0, r])
        self.assertAlmostEqual(sum(abs(v)**2 for v in project(bell, 0, 1)), 0.5)

    def test_y_statistics_detect_phase_sign_and_controlled_scalar_sign(self):
        plus = [1/math.sqrt(2)] * 2
        expected = (1 + 1/math.sqrt(2)) / 2
        forward = rotate(gate(plus, "t", [0]), 0, "y")
        inverse = rotate(gate(plus, "t", [0], inverse=True), 0, "y")
        self.assertAlmostEqual(abs(forward[0])**2, expected)
        self.assertAlmostEqual(abs(inverse[0])**2, 1-expected)
        # Controlled -I is a Z on the control, detectable in the X basis.
        state = [1/math.sqrt(2), 0, 1/math.sqrt(2), 0]
        changed = [v * (-1 if i & 2 else 1) for i, v in enumerate(state)]
        self.assertAlmostEqual(abs(rotate(state, 1, "x")[0])**2, 1)
        self.assertAlmostEqual(abs(rotate(changed, 1, "x")[2])**2, 1)

    def test_toffoli_axes_and_fixed_seed_source_are_reproducible(self):
        state = [int(i == 3) for i in range(8)]
        self.assertEqual(gate(state, "toffoli", [0, 1, 2]), [int(i == 7) for i in range(8)])
        left, right = random.Random(SEED), random.Random(SEED)
        for index in range(24):
            source, expected = make_case(left, index)
            self.assertEqual((source, expected), make_case(right, index))
            self.assertIn("apply_contract(u,reference,q)", source)
            self.assertAlmostEqual(sum(expected.values()), 1)


if __name__ == "__main__":
    unittest.main()
