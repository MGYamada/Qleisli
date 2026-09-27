#!/usr/bin/env python3
"""Shape and arithmetic regressions for the imaginary-v1 mathematical helpers."""

import unittest

from check_imaginary_v1_examples import add, adj, close, eye, mul, power, scale


class MatrixHelperTests(unittest.TestCase):
    def test_review_close_reproducer_rejects_later_nan(self):
        with self.assertRaisesRegex(ValueError, 'finite entries'):
            close([[0.0, float('nan')]], [[0.0, 0.0]])

    def test_close_rejects_nonfinite_entries_in_either_operand_at_every_position(self):
        for bad in (float('nan'), float('inf'), -float('inf'),
                    complex(0, float('nan')), complex(0, float('inf')),
                    complex(0, -float('inf'))):
            for row in range(2):
                for column in range(2):
                    malformed = [[0j, 0j], [0j, 0j]]
                    malformed[row][column] = bad
                    valid = [[0j, 0j], [0j, 0j]]
                    for left, right in ((malformed, valid), (valid, malformed),
                                        (malformed, malformed)):
                        with self.subTest(bad=bad, row=row, column=column,
                                          left=left, right=right):
                            with self.assertRaisesRegex(ValueError, 'finite entries'):
                                close(left, right)

    def test_invalid_comparison_cannot_pass_a_negative_check(self):
        with self.assertRaisesRegex(ValueError, 'finite entries'):
            not close([[float('nan')]], [[0]])

    def test_close_preserves_finite_complex_tolerance(self):
        self.assertTrue(close([[1 + 2j]], [[1 + (2 + 1e-12) * 1j]]))
        self.assertFalse(close([[1 + 2j]], [[1 + (2 + 1e-10) * 1j]]))

    def test_review_close_reproducer_rejects_different_shapes(self):
        with self.assertRaisesRegex(ValueError, 'close requires equal shapes'):
            close([[1]], [[1, 0], [0, 1]])

    def test_review_mul_reproducer_rejects_inner_dimension_mismatch(self):
        with self.assertRaisesRegex(ValueError, 'mul requires matching inner dimensions'):
            mul([[1, 2]], [[3]])

    def test_elementwise_operations_reject_extra_rows_or_columns(self):
        for operation in (add, close):
            for left, right in (
                ([[1]], [[1], [0]]),
                ([[1]], [[1, 0]]),
                ([[1], [0]], [[1]]),
                ([[1, 0]], [[1]]),
            ):
                with self.subTest(operation=operation.__name__, left=left, right=right):
                    with self.assertRaisesRegex(ValueError, 'requires equal shapes'):
                        operation(left, right)

    def test_multiplication_checks_both_inner_dimension_directions(self):
        for left, right in (
            ([[1, 2]], [[3]]),
            ([[1]], [[2], [3]]),
        ):
            with self.subTest(left=left, right=right):
                with self.assertRaisesRegex(ValueError, 'matching inner dimensions'):
                    mul(left, right)

    def test_binary_operations_reject_ragged_operands(self):
        for operation in (add, close, mul):
            for malformed in ([[1, 2], [3]], [[1], [2, 3]], [[1], []]):
                for left, right in ((malformed, eye(2)), (eye(2), malformed)):
                    with self.subTest(operation=operation.__name__, left=left, right=right):
                        with self.assertRaisesRegex(ValueError, 'must be rectangular'):
                            operation(left, right)

    def test_binary_operations_reject_empty_operands(self):
        for operation in (add, close, mul):
            for empty in ([], [[]], [[], []]):
                for left, right in ((empty, [[1]]), ([[1]], empty), (empty, empty)):
                    with self.subTest(operation=operation.__name__, left=left, right=right):
                        with self.assertRaisesRegex(ValueError, 'at least one row and one column'):
                            operation(left, right)

    def test_unary_helpers_reject_malformed_shapes_before_computation(self):
        for operation in (adj, lambda a: scale(0, a), lambda a: power(a, 0)):
            for malformed in ([], [[]], [[], []], [[1, 2], [3]], [[1], [2, 3]]):
                with self.subTest(operation=operation, malformed=malformed):
                    with self.assertRaises(ValueError):
                        operation(malformed)

    def test_rectangular_multiplication_keeps_every_entry(self):
        left = [[1, 2, 3], [4, 5, 6]]
        right = [[7, 8], [9, 10], [11, 12]]
        self.assertEqual(mul(left, right), [[58, 64], [139, 154]])
        self.assertEqual(mul([[1, 2, 3]], [[4], [5], [6]]), [[32]])
        self.assertEqual(mul([[1], [2]], [[3, 4, 5]]), [[3, 4, 5], [6, 8, 10]])

    def test_rectangular_elementwise_operations_keep_every_entry(self):
        left = [[1, 2, 3], [4, 5, 6]]
        right = [[7, 8, 9], [10, 11, 12]]
        self.assertEqual(add(left, right), [[8, 10, 12], [14, 16, 18]])
        self.assertEqual(scale(-2, left), [[-2, -4, -6], [-8, -10, -12]])
        self.assertTrue(close(left, [[1, 2, 3], [4, 5, 6 + 1e-12]]))
        self.assertFalse(close(left, [[1, 2, 3], [4, 5, 6 + 1e-10]]))

    def test_rectangular_adjoint_conjugates_and_transposes(self):
        matrix = [[1 + 2j, 3, 4j], [5, 6 - 7j, 8]]
        self.assertEqual(adj(matrix), [[1 - 2j, 5], [3, 6 + 7j], [-4j, 8]])
        self.assertEqual(adj(adj(matrix)), matrix)

    def test_power_requires_a_square_matrix_even_at_zero_exponent(self):
        for matrix in ([[1, 2]], [[1], [2]]):
            for exponent in (0, 1, 2):
                with self.subTest(matrix=matrix, exponent=exponent):
                    with self.assertRaisesRegex(ValueError, 'requires a square matrix'):
                        power(matrix, exponent)

    def test_identity_and_powers_have_valid_dimensions(self):
        self.assertEqual(eye(1), [[1]])
        self.assertEqual(eye(2), [[1, 0], [0, 1]])
        matrix = [[1, 2], [3, 4]]
        self.assertEqual(power(matrix, 0), [[1, 0], [0, 1]])
        self.assertEqual(power(matrix, 1), matrix)
        self.assertEqual(power(matrix, 2), [[7, 10], [15, 22]])

    def test_identity_rejects_invalid_dimensions(self):
        for dimension in (-1, 0, 1.5):
            with self.subTest(dimension=dimension):
                with self.assertRaisesRegex(ValueError, 'positive integer dimension'):
                    eye(dimension)

    def test_power_rejects_invalid_exponents(self):
        for exponent in (-1, 0.5):
            with self.subTest(exponent=exponent):
                with self.assertRaisesRegex(ValueError, 'nonnegative integer exponent'):
                    power([[1]], exponent)


if __name__ == '__main__':
    unittest.main()
