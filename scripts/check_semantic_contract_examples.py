#!/usr/bin/env python3
"""Exact finite examples for encoded-operation contracts.

Run with Python 3 and its standard library. Rational matrices, plus an exact
Q(sqrt(2)) Hadamard example, illustrate identities and counterexamples. This
script is not a proof of their general forms or a Qleisli implementation.

Matrix helpers require nonempty rectangular matrices and compatible dimensions.
Malformed inputs raise ValueError before arithmetic, including in negative
examples. A scalar operation has shape 1-by-1; empty matrices are not fixtures.
"""

from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True, eq=False)
class Quadratic:
    """An exact real number a + b*sqrt(2); no floating-point coercions."""

    a: Fraction = Fraction(0)
    b: Fraction = Fraction(0)

    def __post_init__(self):
        object.__setattr__(self, "a", Fraction(self.a))
        object.__setattr__(self, "b", Fraction(self.b))

    @staticmethod
    def coerce(value):
        if isinstance(value, Quadratic):
            return value
        if isinstance(value, (int, Fraction)):
            return Quadratic(Fraction(value))
        raise TypeError("expected an exact rational or quadratic number")

    def __add__(self, other):
        other = self.coerce(other)
        return Quadratic(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Quadratic(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        other = self.coerce(other)
        return Quadratic(
            self.a * other.a + 2 * self.b * other.b,
            self.a * other.b + self.b * other.a,
        )

    __rmul__ = __mul__

    def __eq__(self, other):
        if not isinstance(other, (int, Fraction, Quadratic)):
            return NotImplemented
        other = self.coerce(other)
        return self.a == other.a and self.b == other.b

    def __repr__(self):
        return f"({self.a}) + ({self.b})*sqrt(2)"


def shape(value, name="matrix"):
    if not value or not value[0]:
        raise ValueError(f"{name} must have at least one row and one column")
    columns = len(value[0])
    if any(len(row) != columns for row in value):
        raise ValueError(f"{name} must be rectangular")
    return len(value), columns


def matrix(rows):
    shape(rows)
    return [
        [value if isinstance(value, Quadratic) else Fraction(value) for value in row]
        for row in rows
    ]


def zeros(rows, columns):
    if any(not isinstance(size, int) or size < 1 for size in (rows, columns)):
        raise ValueError("zeros requires positive integer dimensions")
    return [[Fraction(0) for _ in range(columns)] for _ in range(rows)]


def identity(size):
    if not isinstance(size, int) or size < 1:
        raise ValueError("identity requires a positive integer dimension")
    return [[Fraction(i == j) for j in range(size)] for i in range(size)]


def transpose(value):
    # All fixtures are real; transpose is their adjoint.
    shape(value, "transpose matrix")
    return [list(row) for row in zip(*value)]


def multiply(left, right):
    left_shape = shape(left, "multiply left matrix")
    right_shape = shape(right, "multiply right matrix")
    if left_shape[1] != right_shape[0]:
        raise ValueError(
            f"multiply requires matching inner dimensions; got {left_shape} and {right_shape}"
        )
    return [
        [
            sum(
                (left[i][k] * right[k][j] for k in range(len(right))),
                Fraction(0),
            )
            for j in range(len(right[0]))
        ]
        for i in range(len(left))
    ]


def subtract(left, right):
    left_shape = shape(left, "subtract left matrix")
    right_shape = shape(right, "subtract right matrix")
    if left_shape != right_shape:
        raise ValueError(f"subtract requires equal shapes; got {left_shape} and {right_shape}")
    return [
        [x - y for x, y in zip(left_row, right_row)]
        for left_row, right_row in zip(left, right)
    ]


def scale(coefficient, value):
    shape(value, "scale matrix")
    return [[coefficient * x for x in row] for row in value]


def tensor(left, right):
    """Usual Kronecker order: the left factor is the high-order factor."""
    shape(left, "tensor left matrix")
    shape(right, "tensor right matrix")
    return [
        [
            left[i][j] * right[k][l]
            for j in range(len(left[0]))
            for l in range(len(right[0]))
        ]
        for i in range(len(left))
        for k in range(len(right))
    ]


def column(values):
    return matrix([[value] for value in values])


def norm_squared(vector):
    if shape(vector, "norm_squared vector")[1] != 1:
        raise ValueError("norm_squared requires a column vector")
    return multiply(transpose(vector), vector)[0][0]


def permutation(size, image):
    result = zeros(size, size)
    for source in range(size):
        result[image(source)][source] = Fraction(1)
    return result


def controlled(operation):
    """Control is the high-order factor; control zero applies identity."""
    size, columns = shape(operation, "controlled operation")
    if size != columns:
        raise ValueError("controlled requires a square matrix")
    result = zeros(2 * size, 2 * size)
    for i in range(size):
        result[i][i] = Fraction(1)
        for j in range(size):
            result[size + i][size + j] = operation[i][j]
    return result


def check(label, condition):
    if not condition:
        raise AssertionError(label)
    print("PASS", label)
    return 1


def graph_code_examples():
    # Graph examples use physical index x + 2*a: data is the low-order bit.
    encoding = matrix([[1, 0], [0, 0], [0, 0], [0, 1]])
    append_zero = matrix([[1, 0], [0, 1], [0, 0], [0, 0]])
    logical_x = matrix([[0, 1], [1, 0]])
    logical_z = matrix([[1, 0], [0, -1]])
    both_x = permutation(4, lambda index: index ^ 3)
    auxiliary_x = permutation(4, lambda index: index ^ 2)
    auxiliary_z = matrix(
        [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]]
    )
    compute = permutation(4, lambda index: index ^ (2 if index & 1 else 0))
    count = 0
    count += check("E_id is isometric", multiply(transpose(encoding), encoding) == identity(2))
    count += check("CNOT append-zero equals E_id", multiply(compute, append_zero) == encoding)
    count += check(
        "X_source X_aux implements logical X",
        multiply(both_x, encoding) == multiply(encoding, logical_x),
    )
    decoded_x = multiply(multiply(multiply(compute, both_x), compute), append_zero)
    count += check("compute/use/uncompute returns X with clean zero", decoded_x == multiply(append_zero, logical_x))
    count += check(
        "aux Z implements logical Z on the graph code",
        multiply(auxiliary_z, encoding) == multiply(encoding, logical_z),
    )
    decoded_z = multiply(multiply(multiply(compute, auxiliary_z), compute), append_zero)
    count += check("compute/Z/uncompute returns the phase oracle", decoded_z == multiply(append_zero, logical_z))
    changed_code = multiply(auxiliary_x, encoding)
    count += check(
        "aux X fails the fixed graph code: compression is zero",
        multiply(transpose(encoding), changed_code) == zeros(2, 2),
    )
    count += check("aux X has unit leakage on each code basis", multiply(transpose(changed_code), changed_code) == identity(2))
    count += check("composition yields logical identity", multiply(multiply(both_x, both_x), encoding) == encoding)
    count += check(
        "tensoring a reference preserves intertwining",
        multiply(tensor(both_x, identity(2)), tensor(encoding, identity(2)))
        == multiply(tensor(encoding, identity(2)), tensor(logical_x, identity(2))),
    )
    count += check(
        "the same preserved code admits meanings I and X",
        multiply(identity(4), encoding) == encoding
        and multiply(both_x, encoding) != encoding,
    )
    controlled_encoding = tensor(identity(2), encoding)
    count += check(
        "a common encoding supports coherent control",
        multiply(controlled(both_x), controlled_encoding)
        == multiply(controlled_encoding, controlled(logical_x)),
    )
    return count


def inverse_examples():
    count = 0
    implementation = column([1, 0])
    # Logical u is the scalar identity. Its encoded adjoint equation holds,
    # although U† annihilates out-of-code inputs instead of preserving norm.
    count += check(
        "rectangular isometry: forward and encoded adjoint hold",
        multiply(implementation, identity(1)) == implementation
        and multiply(transpose(implementation), implementation) == identity(1),
    )
    count += check(
        "a rectangular adjoint is not globally isometric",
        multiply(implementation, transpose(implementation)) != identity(2),
    )
    print("adjoint maps out-of-code |1> norm^2 to", norm_squared(multiply(transpose(implementation), column([0, 1]))))
    # Even physical U=I is insufficient when logical u is not surjective.
    input_encoding = column([1, 0])
    output_encoding = identity(2)
    logical = input_encoding
    count += check(
        "non-surjective logical u satisfies the forward equality",
        multiply(identity(2), input_encoding) == multiply(output_encoding, logical),
    )
    count += check(
        "non-surjective logical u fails the full adjoint equality",
        output_encoding != multiply(input_encoding, transpose(logical)),
    )
    return count


def compression_and_hadamard_examples():
    count = 0
    a, b = Fraction(3, 5), Fraction(4, 5)
    rotation = matrix([[a, -b], [b, a]])
    encoding = column([1, 0])
    compressed = multiply(transpose(encoding), multiply(rotation, encoding))
    count += check("compression example rotation is unitary", multiply(transpose(rotation), rotation) == identity(2))
    count += check(
        "compressed target 3/5 is not the full intertwiner",
        compressed == matrix([[a]]) and multiply(rotation, encoding) != multiply(encoding, compressed),
    )
    print("compression-only leakage probability =", b * b)
    amplification = matrix([[1, 0], [1, 1]])
    count += check(
        "non-isometric U can have unitary compression and leakage",
        multiply(transpose(encoding), multiply(amplification, encoding)) == identity(1)
        and multiply(amplification, encoding) != encoding,
    )
    root_half = Quadratic(0, Fraction(1, 2))
    hadamard = matrix([[root_half, root_half], [root_half, -root_half]])
    count += check("Hadamard is unitary over Q(sqrt(2))", multiply(transpose(hadamard), hadamard) == identity(2))
    count += check("H followed by H is exactly identity", multiply(hadamard, hadamard) == identity(2))
    graph_encoding = matrix([[1, 0], [0, 0], [0, 0], [0, 1]])
    auxiliary_h = tensor(hadamard, identity(2))
    count += check(
        "auxiliary H;H preserves the graph code exactly",
        multiply(multiply(auxiliary_h, auxiliary_h), graph_encoding) == graph_encoding,
    )
    compressed = multiply(transpose(encoding), multiply(hadamard, encoding))
    count += check("Hadamard compression equals 1/sqrt(2)", compressed == [[root_half]])
    count += check("Hadamard compression retains nonzero leakage", multiply(hadamard, encoding) != multiply(encoding, compressed))
    leakage = multiply(hadamard, encoding)[1][0]
    count += check("Hadamard leakage probability equals 1/2", leakage * leakage == Quadratic(Fraction(1, 2)))
    print("Hadamard compressed coefficient =", compressed[0][0], "; leakage probability = 1/2")
    return count


def control_and_entry_examples():
    count = 0
    # U=X realizes logical scalar identity between different one-dimensional
    # encodings. A controlled-U identity arm does not convert |0> to |1>.
    input_encoding = column([1, 0])
    output_encoding = column([0, 1])
    implementation = matrix([[0, 1], [1, 0]])
    count += check("X converts the different encodings", multiply(implementation, input_encoding) == output_encoding)
    count += check(
        "different encodings invalidate the identity control arm",
        multiply(controlled(implementation), tensor(identity(2), input_encoding))
        != multiply(tensor(identity(2), output_encoding), identity(2)),
    )
    count += check(
        "a certified conversion on both arms restores control compatibility",
        multiply(tensor(identity(2), implementation), tensor(identity(2), input_encoding))
        == tensor(identity(2), output_encoding),
    )
    # A valid code contract has no claim about a wrongly initialized auxiliary.
    encoding = matrix([[1, 0], [0, 1], [0, 0], [0, 0]])
    auxiliary_control = permutation(4, lambda index: index ^ (1 if index & 2 else 0))
    count += check("aux-controlled X is logical I on zero-auxiliary code", multiply(auxiliary_control, encoding) == encoding)
    count += check(
        "without the code promise logical zero changes to one",
        multiply(auxiliary_control, column([0, 0, 1, 0])) == column([0, 0, 0, 1]),
    )
    plus = matrix([[Fraction(1, 2), Fraction(1, 2)], [Fraction(1, 2), Fraction(1, 2)]])
    minus = matrix([[Fraction(1, 2), Fraction(-1, 2)], [Fraction(-1, 2), Fraction(1, 2)]])
    logical_z = matrix([[1, 0], [0, -1]])
    count += check(
        "density maps cannot distinguish I and -I",
        multiply(multiply(scale(-1, identity(2)), plus), scale(-1, identity(2))) == plus,
    )
    count += check("control of scalar -1 changes plus to minus", multiply(multiply(logical_z, plus), logical_z) == minus)
    probability = sum(multiply(minus, minus)[i][i] for i in range(2))
    print("X-minus outcome: controlled(+1)=0, controlled(-1)=", probability)
    return count


def basis_only_cleanup_examples():
    count = 0
    # U swaps the code's uniform vector with one orthogonal leakage direction.
    # For n=k^2, every basis input leaks 1/n; their superposition leaks fully.
    for root_dimension in [2, 4]:
        dimension = root_dimension * root_dimension
        uniform = column([Fraction(1, root_dimension)] * dimension)
        projector = multiply(uniform, transpose(uniform))
        complement = subtract(identity(dimension), projector)
        implementation = [
            complement[i] + [uniform[i][0]] for i in range(dimension)
        ] + [[Fraction(1, root_dimension)] * dimension + [Fraction(0)]]
        encoding = identity(dimension) + [[Fraction(0)] * dimension]
        count += check(
            f"coherent leakage n={dimension}: U is unitary",
            multiply(transpose(implementation), implementation) == identity(dimension + 1),
        )
        image = multiply(implementation, multiply(encoding, uniform))
        basis_leakage = max(multiply(implementation, encoding)[dimension][j] ** 2 for j in range(dimension))
        count += check(
            f"coherent leakage n={dimension}: uniform vector leaks completely",
            image == column([0] * dimension + [1]),
        )
        print(f"n={dimension}: every basis leakage={basis_leakage}; superposition leakage={image[dimension][0] ** 2}")
    return count


def approximate_cleanup_example():
    # A controlled rotation weakly entangles the logical bit and its auxiliary.
    # Even uniformly small leakage does not authorize exact pure release.
    parameter = Fraction(1, 100)
    a = (1 - parameter * parameter) / (1 + parameter * parameter)
    b = 2 * parameter / (1 + parameter * parameter)
    implementation = matrix([[1, 0, 0, 0], [0, a, 0, -b], [0, 0, 1, 0], [0, b, 0, a]])
    count = check("controlled rotation is unitary", multiply(transpose(implementation), implementation) == identity(4))
    encoding = matrix([[1, 0], [0, 1], [0, 0], [0, 0]])
    plus = matrix([[Fraction(1, 2), Fraction(1, 2)], [Fraction(1, 2), Fraction(1, 2)]])
    isometry = multiply(implementation, encoding)
    joint = multiply(multiply(isometry, plus), transpose(isometry))
    reduced = [[joint[i][j] + joint[i + 2][j + 2] for j in range(2)] for i in range(2)]
    expected = matrix([[Fraction(1, 2), a / 2], [a / 2, Fraction(1, 2)]])
    count += check("discarding a nearly-zero auxiliary makes a mixed state", reduced == expected)
    determinant = reduced[0][0] * reduced[1][1] - reduced[0][1] * reduced[1][0]
    count += check("the reduced logical state is not pure", determinant > 0)
    print("uniform max cleanup failure =", b * b)
    print("plus-input cleanup failure =", b * b / 2)
    print("reduced logical determinant =", determinant)
    print("zero-projection success trace =", (1 + a * a) / 2)
    return count


def main():
    count = sum(
        example()
        for example in [
            graph_code_examples,
            inverse_examples,
            compression_and_hadamard_examples,
            control_and_entry_examples,
            basis_only_cleanup_examples,
            approximate_cleanup_example,
        ]
    )
    print(f"All {count} exact rational/algebraic assertions passed.")


if __name__ == "__main__":
    main()
