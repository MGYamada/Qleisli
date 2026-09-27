#!/usr/bin/env python3
"""Finite mathematical checks for imaginary drafts, not a Qleisli interpreter.

These independently constructed small matrices check conventions and negative
examples. Floating-point agreement is neither a general theorem nor exact
cleanup evidence. No imaginary source is parsed, compiled, or executed here.
"""

import cmath
from fractions import Fraction
from math import asin, gcd, pi, sin, sqrt


def eye(n):
    return [[complex(i == j) for j in range(n)] for i in range(n)]


def mul(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def adj(a):
    return [[x.conjugate() for x in row] for row in zip(*a)]


def add(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(c, a):
    return [[c * x for x in row] for row in a]


def close(a, b):
    return max(abs(x - y) for ar, br in zip(a, b) for x, y in zip(ar, br)) < 1e-11


def power(a, k):
    result = eye(len(a))
    for _ in range(k):
        result = mul(a, result)
    return result


def check(label, condition):
    if not condition:
        raise AssertionError(label)
    print('PASS', label)
    return 1


def qpe_checks():
    count = 0
    # Transcribe the draft's elementary gate order and compare every column
    # with an independently specified positive Fourier matrix.
    for width in range(1, 5):
        size = 2**width
        columns = []
        for source in range(size):
            state = [complex(i == source) for i in range(size)]
            for j in reversed(range(width)):
                for lo in range(size):
                    if not lo & (1 << j):
                        hi = lo | (1 << j)
                        a, b = state[lo], state[hi]
                        state[lo], state[hi] = (a+b)/sqrt(2), (a-b)/sqrt(2)
                for k in reversed(range(j)):
                    phase = cmath.exp(2j*pi / 2**(j-k+1))
                    for i in range(size):
                        if i & (1 << k) and i & (1 << j):
                            state[i] *= phase
            reordered = [0j]*size
            for i, amplitude in enumerate(state):
                reversed_index = int(f'{i:0{width}b}'[::-1], 2)
                reordered[reversed_index] = amplitude
            columns.append(reordered)
        actual = [list(row) for row in zip(*columns)]
        fourier = [[cmath.exp(2j*pi*i*j/size)/sqrt(size) for j in range(size)] for i in range(size)]
        count += check(f'QFT displayed gate order matches positive Fourier matrix at width={width}', close(actual, fourier))
    # Finite Fourier sum derived from phase kickback, with inverse-QFT sign.
    for m, phase in [(4, Fraction(1, 4)), (8, Fraction(1, 5))]:
        amplitudes = [sum(cmath.exp(2j * pi * k * (float(phase) - y / m))
                          for k in range(m)) / m for y in range(m)]
        count += check(f'QPE M={m} normalized', abs(sum(abs(a)**2 for a in amplitudes) - 1) < 1e-12)
        if m == 4:
            count += check('QPE phase 1/4 decodes to integer 1, not 3', abs(amplitudes[1] - 1) < 1e-12 and abs(amplitudes[3]) < 1e-12)
    x = [[0j, 1+0j], [1+0j, 0j]]
    ks = []
    for y in range(4):
        k_y = [[0j, 0j], [0j, 0j]]
        for k in range(4):
            k_y = add(k_y, scale(cmath.exp(-2j*pi*k*y/4)/4, power(x, k)))
        ks.append(k_y)
    plus = scale(0.5, add(eye(2), x))
    minus = scale(0.5, add(eye(2), scale(-1, x)))
    count += check('QPE X instrument is P_plus at y=0 and P_minus at y=2', close(ks[0], plus) and close(ks[2], minus))
    complete = [[0j, 0j], [0j, 0j]]
    for k_y in ks:
        complete = add(complete, mul(adj(k_y), k_y))
    count += check('QPE instrument completeness', close(complete, eye(2)))
    # Bell input: (K tensor I)|Bell>; reference is explicitly retained.
    for y in [0, 2]:
        branch = [[ks[y][i][j] / sqrt(2)] for i in range(2) for j in range(2)]
        count += check(f'QPE Bell reference branch y={y} probability 1/2', abs(sum(abs(v[0])**2 for v in branch) - 0.5) < 1e-12)
        expected = [[((-1)**(i+j) if y == 2 else 1)/(2*sqrt(2))]
                    for i in range(2) for j in range(2)]
        count += check(f'QPE Bell branch y={y} retains full target/reference coherence', close(branch, expected))
    return count


def amplification_checks():
    count = 0
    psi = [[0.5+0j] for _ in range(4)]
    reflection = add(scale(2, mul(psi, adj(psi))), scale(-1, eye(4)))
    oracle = eye(4)
    oracle[3][3] = -1
    g = mul(reflection, oracle)
    output = mul(g, psi)
    count += check('Grover four items one marked succeeds after one iterate', abs(abs(output[3][0])**2 - 1) < 1e-12)
    interference = mul(adj(psi), output)[0][0].real
    count += check('controlled Grover sign changes control-X expectation from +1/2 to -1/2', abs(interference-0.5) < 1e-12 and abs((-interference)-0.5) > 0.9)
    theta = asin(3/5)
    state = [[3/5+0j], [4/5+0j]]
    r = add(scale(2, mul(state, adj(state))), scale(-1, eye(2)))
    g2 = mul(r, [[-1+0j, 0j], [0j, 1+0j]])
    for k in [0, 1, 2, 3]:
        p = abs(mul(power(g2, k), state)[0][0])**2
        count += check(f'amplification k={k} agrees with sin²((2k+1)theta)', abs(p - sin((2*k+1)*theta)**2) < 1e-12)
    # For theta=pi/8, QPE of G has phases +/-1/8. Both give p=sin²(theta).
    p = sin(pi/8)**2
    count += check('AE resolves the two phase signs to the same probability', abs(sin(pi*1/8)**2-p) < 1e-12 and abs(sin(pi*7/8)**2-p) < 1e-12)
    count += check('AE opposite iterate sign changes probability to 1-p', abs(sin(pi*5/8)**2-(1-p)) < 1e-12 and abs(p-(1-p)) > 0.1)
    return count


def shor_checks():
    n, a, width = 15, 2, 16
    image = [(a*x) % n if x < n else x for x in range(width)]
    count = check('modular multiplication including padded label is a permutation', len(set(image)) == width and image[15] == 15)
    count += check('noncoprime multiplication cannot supply the same unitary contract', len({(3*x) % n for x in range(n)}) < n)
    for numerator in [1, 3]:
        r = Fraction(numerator, 4).denominator
        z = pow(a, r//2, n)
        factors = sorted([gcd(z-1, n), gcd(z+1, n)])
        count += check(f'Shor phase {numerator}/4 verifies period and factors', pow(a, r, n) == 1 and factors == [3, 5])
    count += check('Shor denominator 2 is not a period for a=2,N=15', pow(a, 2, n) != 1)
    count += check('a verified multiple of the order still needs factor checks', pow(a, 8, n) == 1 and pow(a, 4, n) == 1)
    return count


def walk_checks():
    # Symmetric two-state P with row amplitudes 3/5,4/5.
    # Matrix fixture uses basis |x,y>, index 2*x+y, stated independently of IR.
    columns = [[3/5, 4/5, 0, 0], [0, 0, 4/5, 3/5]]
    t = [[complex(columns[j][i]) for j in range(2)] for i in range(4)]
    swap = [[complex(i == (2*(j % 2)+j//2)) for j in range(4)] for i in range(4)]
    pa = mul(t, adj(t))
    pb = mul(mul(swap, pa), swap)
    ra = add(scale(2, pa), scale(-1, eye(4)))
    rb = add(scale(2, pb), scale(-1, eye(4)))
    w = mul(rb, ra)
    count = check('walk transition encoding is isometric', close(mul(adj(t), t), eye(2)))
    count += check('walk product of reflections is unitary', close(mul(adj(w), w), eye(4)))
    stationary = mul(t, [[1/sqrt(2)+0j], [1/sqrt(2)+0j]])
    count += check('symmetric walk stationary lifted vector has eigenvalue +1', close(mul(w, stationary), stationary))
    count += check('walk reflection product order cannot be silently swapped', not close(w, mul(ra, rb)))
    return count


def qsvt_checks():
    count = 0
    z = [[1+0j, 0j], [0j, -1+0j]]
    for x in [-1, -0.6, 0, 0.3, 1]:
        s = sqrt(1-x*x)
        u = [[x+0j, s+0j], [s+0j, -x+0j]]
        # Odd d=3 with phases (pi, pi/2, pi/2): U Z U† Z U.
        sequence = mul(mul(mul(mul(u, z), adj(u)), z), u)
        count += check(f'QSVT d=3 block at x={x} is T3(x)', abs(sequence[0][0]-(4*x**3-3*x)) < 1e-12)
        count += check(f'QSVT full output at x={x} remains unitary', close(mul(adj(sequence), sequence), eye(2)))
        even = mul(mul(mul(z, adj(u)), z), u)
        count += check(f'QSVT d=2 block at x={x} is T2(x)', abs(even[0][0]-(2*x*x-1)) < 1e-12)
    # Canonical dilation of a non-Hermitian B distinguishes singular transforms
    # from matrix polynomials and even right-space from left-space transforms.
    b = [[0j, 0.3+0j], [0.6+0j, 0j]]
    c, e = sqrt(1-0.3**2), sqrt(1-0.6**2)
    u = [[0j, 0.3+0j, c+0j, 0j], [0.6+0j, 0j, 0j, e+0j],
         [e+0j, 0j, 0j, -0.6+0j], [0j, c+0j, -0.3+0j, 0j]]
    z4 = eye(4)
    z4[2][2] = z4[3][3] = -1
    even = mul(mul(mul(z4, adj(u)), z4), u)
    even_block = [row[:2] for row in even[:2]]
    expected_right = add(scale(2, mul(adj(b), b)), scale(-1, eye(2)))
    wrong_left = add(scale(2, mul(b, adj(b))), scale(-1, eye(2)))
    count += check('non-Hermitian encoding dilation is unitary', close(mul(adj(u), u), eye(4)))
    count += check('even QSVT uses right singular space, not left', close(even_block, expected_right) and not close(even_block, wrong_left))
    odd = mul(mul(mul(mul(u, z4), adj(u)), z4), u)
    odd_block = [row[:2] for row in odd[:2]]
    expected_odd = add(scale(4, mul(mul(b, adj(b)), b)), scale(-3, b))
    matrix_polynomial = add(scale(4, power(b, 3)), scale(-3, b))
    count += check('odd QSVT is singular transform, not matrix polynomial', close(odd_block, expected_odd) and not close(odd_block, matrix_polynomial))
    # d=1, phi=pi/3 realizes p(x)=x/2 only after combining both phase lists.
    plus_phase = [[cmath.exp(1j*pi/3)*v if i < 2 else cmath.exp(-1j*pi/3)*v
                   for v in row] for i, row in enumerate(u)]
    minus_phase = [[cmath.exp(-1j*pi/3)*v if i < 2 else cmath.exp(1j*pi/3)*v
                    for v in row] for i, row in enumerate(u)]
    branches = [scale(0.5, add(plus_phase, minus_phase)),
                scale(0.5, add(plus_phase, scale(-1, minus_phase)))]
    success = [row[:2] for row in branches[0][:2]]
    count += check('real polynomial selector implements B/2', close(success, scale(0.5, b)))
    complete = [[0j, 0j], [0j, 0j]]
    for branch in branches:
        for ancilla in [0, 1]:
            k = [row[:2] for row in branch[2*ancilla:2*ancilla+2]]
            complete = add(complete, mul(adj(k), k))
    count += check('QSVT all selector/ancilla branches form a complete instrument', close(complete, eye(2)))
    success_weight = sum(abs(row[0])**2 for row in success)
    count += check('QSVT success block leaves nonzero failure weight', abs(success_weight-0.09) < 1e-12 and 1-success_weight > 0.9)
    return count


if __name__ == '__main__':
    total = sum(f() for f in [qpe_checks, amplification_checks, shor_checks, walk_checks, qsvt_checks])
    print(f'All {total} finite mathematical checks passed; imaginary source was not compiled.')
