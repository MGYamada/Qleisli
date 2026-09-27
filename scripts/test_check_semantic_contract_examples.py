#!/usr/bin/env python3
"""Shape and exact-arithmetic regressions for semantic-contract fixtures."""

from fractions import Fraction
import unittest

from check_semantic_contract_examples import (
    Quadratic, controlled, identity, matrix, multiply, norm_squared,
    scale, subtract, tensor, transpose, zeros,
)


class ExactMatrixHelperTests(unittest.TestCase):
    def test_review_subtraction_reproducer_rejects_shape_mismatch(self):
        with self.assertRaisesRegex(ValueError, 'equal shapes'):
            subtract([[1, 0], [0, 1]], [[1]])

    def test_review_transpose_reproducer_rejects_ragged_input(self):
        with self.assertRaisesRegex(ValueError, 'rectangular'):
            transpose([[1, 2], [3]])

    def test_review_multiply_reproducer_rejects_extra_entries(self):
        with self.assertRaisesRegex(ValueError, 'rectangular'):
            multiply([[1], [2, 3]], [[1]])

    def test_all_matrix_operands_reject_empty_and_ragged_inputs(self):
        operations = (matrix, transpose, lambda a: scale(0, a), norm_squared,
                      controlled)
        binary = (multiply, subtract, tensor)
        for malformed in ([], [[]], [[], []], [[1, 2], [3]], [[1], [2, 3]],
                          [[1], []]):
            for operation in operations:
                with self.subTest(operation=operation, malformed=malformed):
                    with self.assertRaises(ValueError):
                        operation(malformed)
            for operation in binary:
                for left, right in ((malformed, [[1]]), ([[1]], malformed)):
                    with self.subTest(operation=operation.__name__, left=left, right=right):
                        with self.assertRaises(ValueError):
                            operation(left, right)

    def test_subtraction_requires_equal_rows_and_columns_in_both_directions(self):
        for larger in ([[1, 2]], [[1], [2]]):
            for left, right in ((larger, [[1]]), ([[1]], larger)):
                with self.subTest(left=left, right=right):
                    with self.assertRaisesRegex(ValueError, 'equal shapes'):
                        subtract(left, right)

    def test_multiply_requires_matching_inner_dimensions(self):
        for left, right in (([[1, 2]], [[3]]), ([[1]], [[2], [3]])):
            with self.subTest(left=left, right=right):
                with self.assertRaisesRegex(ValueError, 'matching inner dimensions'):
                    multiply(left, right)

    def test_rectangular_arithmetic_keeps_every_entry(self):
        left = matrix([[1, 2, 3], [4, 5, 6]])
        right = matrix([[7, 8], [9, 10], [11, 12]])
        self.assertEqual(multiply(left, right), [[58, 64], [139, 154]])
        self.assertEqual(transpose(left), [[1, 4], [2, 5], [3, 6]])
        self.assertEqual(subtract(left, [[6, 5, 4], [3, 2, 1]]),
                         [[-5, -3, -1], [1, 3, 5]])
        self.assertEqual(scale(Fraction(1, 2), [[1, 2]]), [[Fraction(1, 2), 1]])
        self.assertEqual(tensor([[1, 2]], [[3], [4]]), [[3, 6], [4, 8]])

    def test_arithmetic_retains_exact_quadratic_coefficients(self):
        root_half = Quadratic(0, Fraction(1, 2))
        hadamard = matrix([[root_half, root_half], [root_half, -root_half]])
        self.assertEqual(multiply(hadamard, hadamard), identity(2))
        self.assertEqual(norm_squared([[root_half], [root_half]]), 1)
        self.assertEqual(norm_squared([[Fraction(3, 5)], [Fraction(4, 5)]]), 1)

    def test_control_requires_a_square_operation(self):
        for operation in ([[1, 2]], [[1], [2]]):
            with self.subTest(operation=operation):
                with self.assertRaisesRegex(ValueError, 'square matrix'):
                    controlled(operation)
        self.assertEqual(controlled([[0, 1], [1, 0]]),
                         [[1, 0, 0, 0], [0, 1, 0, 0],
                          [0, 0, 0, 1], [0, 0, 1, 0]])
        self.assertEqual(controlled([[-1]]), [[1, 0], [0, -1]])

    def test_norm_requires_a_column_vector(self):
        for value in ([[3, 4]], [[1, 0], [0, 1]]):
            with self.subTest(value=value):
                with self.assertRaisesRegex(ValueError, 'column vector'):
                    norm_squared(value)

    def test_constructors_reject_invalid_dimensions(self):
        for dimension in (0, -1, 1.5):
            for operation in (lambda n: zeros(n, 1), lambda n: zeros(1, n), identity):
                with self.subTest(dimension=dimension, operation=operation):
                    with self.assertRaisesRegex(ValueError, 'positive integer'):
                        operation(dimension)
        self.assertEqual(zeros(1, 2), [[0, 0]])
        self.assertEqual(identity(1), [[1]])


if __name__ == '__main__':
    unittest.main()
