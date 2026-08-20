#!/usr/bin/env python3
"""Exact verifier for the Gaussian descent and split-37 certificate."""

from fractions import Fraction
from itertools import product
from math import gcd


def gadd(z, w):
    return z[0] + w[0], z[1] + w[1]


def gneg(z):
    return -z[0], -z[1]


def gmul(z, w):
    a, b = z
    c, d = w
    return a * c - b * d, a * d + b * c


def gscale(n, z):
    return n * z[0], n * z[1]


def ginv(z):
    a, b = z
    n = a * a + b * b
    return a / n, -b / n


def gdiv(z, w):
    return gmul(z, ginv(w))


def gpow(z, n):
    out = (type(z[0])(1), type(z[0])(0))
    while n:
        if n & 1:
            out = gmul(out, z)
        z = gmul(z, z)
        n //= 2
    return out


def gmod(z, modulus):
    """Reduce a Gaussian rational at i -> root modulo modulus."""
    root = z[2]
    a, b = z[0], z[1]

    def fmod(q):
        return (q.numerator % modulus) * pow(q.denominator, -1, modulus) % modulus

    return (fmod(a) + root * fmod(b)) % modulus


def exact_div_gaussian(z, w):
    a, b = z
    c, d = w
    norm = c * c + d * d
    x = a * c + b * d
    y = b * c - a * d
    assert x % norm == 0 and y % norm == 0
    return x // norm, y // norm


def gaussian_mod_mul(z, w, modulus):
    a, b = z
    c, d = w
    return (a * c - b * d) % modulus, (a * d + b * c) % modulus


def gaussian_mod_add(*zs, modulus):
    return (
        sum(z[0] for z in zs) % modulus,
        sum(z[1] for z in zs) % modulus,
    )


def locally_soluble_homogeneous_space(A, B, d, modulus):
    """Search for a lambda-primitive solution of (HS) modulo `modulus`."""
    B_over_d = exact_div_gaussian(B, d)
    elements = list(product(range(modulus), repeat=2))
    squares = {gaussian_mod_mul(z, z, modulus) for z in elements}
    for U in elements:
        U2 = gaussian_mod_mul(U, U, modulus)
        U4 = gaussian_mod_mul(U2, U2, modulus)
        for V in elements:
            # lambda=1+i divides a+bi iff a+b is even.
            if (U[0] + U[1]) % 2 == 0 and (V[0] + V[1]) % 2 == 0:
                continue
            V2 = gaussian_mod_mul(V, V, modulus)
            V4 = gaussian_mod_mul(V2, V2, modulus)
            rhs = gaussian_mod_add(
                gaussian_mod_mul(d, U4, modulus),
                gaussian_mod_mul(A, gaussian_mod_mul(U2, V2, modulus), modulus),
                gaussian_mod_mul(B_over_d, V4, modulus),
                modulus=modulus,
            )
            if rhs in squares:
                return True
    return False


def finite_add(P, Q, A, B, p):
    if P is None:
        return Q
    if Q is None:
        return P
    x, y = P
    X, Y = Q
    if x == X and (y + Y) % p == 0:
        return None
    if x == X:
        slope = (3 * x * x + 2 * A * x + B) * pow(2 * y, -1, p) % p
    else:
        slope = (Y - y) * pow(X - x, -1, p) % p
    xr = (slope * slope - A - x - X) % p
    yr = (-y + slope * (x - xr)) % p
    return xr, yr


def finite_mul(n, P, A, B, p):
    out = None
    while n:
        if n & 1:
            out = finite_add(out, P, A, B, p)
        P = finite_add(P, P, A, B, p)
        n //= 2
    return out


def finite_points(A, B, p):
    out = [None]
    for x in range(p):
        rhs = (x**3 + A * x * x + B * x) % p
        out.extend((x, y) for y in range(p) if y * y % p == rhs)
    return out


def finite_order(P, A, B, p):
    Q = None
    for n in range(1, 4 * p + 20):
        Q = finite_add(Q, P, A, B, p)
        if Q is None:
            return n
    raise AssertionError("Hasse bound exceeded")


def finite_exponent(A, B, p):
    e = 1
    for P in finite_points(A, B, p):
        o = 1 if P is None else finite_order(P, A, B, p)
        e = e * o // gcd(e, o)
    return e


def curve_coefficients(curve, root, p):
    if curve == "E0":
        return 2 * root % p, (-2 - 4 * root) % p
    if curve == "E1":
        return 2 % p, (2 + 4 * root) % p
    raise ValueError(curve)


def check_cardinality_rows():
    rows = {
        "E0": [(13, 5, 12), (13, 8, 18), (29, 12, 28), (29, 17, 38)],
        "E1": [(13, 5, 16), (13, 8, 10), (29, 12, 32), (29, 17, 22)],
    }
    for curve, entries in rows.items():
        for p, root, expected in entries:
            assert root * root % p == p - 1
            A, B = curve_coefficients(curve, root, p)
            assert len(finite_points(A, B, p)) == expected


def check_index_rows():
    rows = [
        (37, 6, 48, 12, (26, 0)),
        (29, 12, 28, 14, (0, 0)),
        (157, 28, 148, 74, (92, 0)),
    ]
    P = (2, 2)
    for p, root, card, order, half in rows:
        A, B = curve_coefficients("E0", root, p)
        assert len(finite_points(A, B, p)) == card
        assert finite_order(P, A, B, p) == order
        assert finite_mul(order // 2, P, A, B, p) == half
        assert finite_mul(order, P, A, B, p) is None


def check_split37_tables():
    p = 37
    P = (2, 2)
    T = (0, 0)
    expected = {
        6: {
            "A": 12,
            "B": 11,
            "card": 48,
            "exponent": 12,
            "order": 12,
            "plain": [
                None, (2, 2), (10, 4), (20, 12), (33, 26), (6, 14),
                (26, 0), (6, 23), (33, 11), (20, 25), (10, 33), (2, 35),
            ],
            "twisted": [
                (0, 0), (24, 13), (27, 4), (32, 3), (25, 33), (8, 6),
                (36, 0), (8, 31), (25, 4), (32, 34), (27, 33), (24, 24),
            ],
        },
        31: {
            "A": 25,
            "B": 22,
            "card": 42,
            "exponent": 42,
            "order": 6,
            "plain": [
                None, (2, 2), (11, 11), (0, 0), (11, 26), (2, 35),
                None, (2, 2), (11, 11), (0, 0), (11, 26), (2, 35),
            ],
            "twisted": [
                (0, 0), (11, 26), (2, 35), None, (2, 2), (11, 11),
                (0, 0), (11, 26), (2, 35), None, (2, 2), (11, 11),
            ],
        },
    }
    actual = {}
    for root, row in expected.items():
        assert root * root % p == p - 1
        A, B = curve_coefficients("E0", root, p)
        assert (A, B) == (row["A"], row["B"])
        points = finite_points(A, B, p)
        assert len(points) == row["card"]
        assert finite_exponent(A, B, p) == row["exponent"]
        assert finite_order(P, A, B, p) == row["order"]
        plain = [finite_mul(n, P, A, B, p) for n in range(12)]
        twisted = [finite_add(Q, T, A, B, p) for Q in plain]
        assert plain == row["plain"]
        assert twisted == row["twisted"]
        actual[root] = plain, twisted

    def same_x(Q, R):
        return (Q is None and R is None) or (
            Q is not None and R is not None and Q[0] == R[0]
        )

    plus, minus = actual[6], actual[31]
    assert [n for n in range(12) if same_x(plus[0][n], minus[0][n])] == [0, 1, 11]
    assert [n for n in range(12) if same_x(plus[1][n], minus[1][n])] == [0]
    # The infinity disk would require the leading quartic coefficient 2
    # to be a local square.
    assert pow(2, 18, 37) == 36
    # q(0)=-1-2i at i=6.
    q0 = (-1 - 2 * 6) % 37
    assert q0 == 24 and pow(q0, 18, 37) == 36


def gaussian_curve_add(P, Q, A, B):
    """Affine group law over Q(i), with Gaussian-rational pairs."""
    if P is None:
        return Q
    if Q is None:
        return P
    x, y = P
    X, Y = Q
    if x == X and gadd(y, Y) == (0, 0):
        return None
    if x == X:
        numerator = gadd(gadd(gscale(3, gmul(x, x)), gscale(2, gmul(A, x))), B)
        denominator = gscale(2, y)
    else:
        numerator = gadd(Y, gneg(y))
        denominator = gadd(X, gneg(x))
    slope = gdiv(numerator, denominator)
    xr = gadd(gadd(gadd(gmul(slope, slope), gneg(A)), gneg(x)), gneg(X))
    yr = gadd(gneg(y), gmul(slope, gadd(x, gneg(xr))))
    return xr, yr


def gaussian_curve_mul(n, P, A, B):
    out = None
    while n:
        if n & 1:
            out = gaussian_curve_add(out, P, A, B)
        P = gaussian_curve_add(P, P, A, B)
        n //= 2
    return out


def eval_gaussian_fraction(z, root, modulus):
    a, b = z

    def eval_fraction(q):
        return q.numerator % modulus * pow(q.denominator, -1, modulus) % modulus

    return (eval_fraction(a) + root * eval_fraction(b)) % modulus


def check_formal_row():
    F = Fraction
    I = (F(0), F(1))
    A = gscale(2, I)
    B = (F(-2), F(-4))
    P = ((F(2), F(0)), (F(2), F(0)))
    R = gaussian_curve_mul(12, P, A, B)
    tR = gneg(gdiv(R[0], R[1]))
    modulus = 37**2
    roots = [117, modulus - 117]
    assert all((root * root + 1) % modulus == 0 for root in roots)
    values = [eval_gaussian_fraction(tR, root, modulus) for root in roots]
    assert values == [629, 703]
    assert [value // 37 % 37 for value in values] == [17, 19]
    assert 4 * (17 - 19) % 37 == 29
    assert -4 * (17 - 19) % 37 == 8


def check_mod1369_trace():
    modulus = 37**2

    def affine_add_when_unit(P, Q, A, B):
        if P is None:
            return Q
        if Q is None:
            return P
        x, y = P
        X, Y = Q
        if x == X:
            numerator = (3 * x * x + 2 * A * x + B) % modulus
            denominator = 2 * y % modulus
        else:
            numerator = (Y - y) % modulus
            denominator = (X - x) % modulus
        assert gcd(denominator, modulus) == 1
        slope = numerator * pow(denominator, -1, modulus) % modulus
        xr = (slope * slope - A - x - X) % modulus
        return xr, (-y + slope * (x - xr)) % modulus

    def initial_multiples(root, count):
        A, B = curve_coefficients("E0", root, modulus)
        P = (2, 2)
        out = []
        Q = None
        for _ in range(count):
            Q = affine_add_when_unit(Q, P, A, B)
            out.append(Q)
        return A, B, out

    A, B, plus = initial_multiples(117, 6)
    assert (A, B) == (234, 899)
    assert plus == [(2, 2), (10, 411), (464, 678), (329, 1173), (931, 347), (655, 370)]
    x, y = plus[-1]
    N = (3 * x * x + 2 * A * x + B) % modulus
    D = 2 * y % modulus
    X = (N * N - (A + 2 * x) * D * D) % modulus
    Y = (-y * D**3 + N * (x * D * D - X)) % modulus
    Z = D
    assert (N, D, X, Y, Z) == (998, 740, 741, 1111, 740)
    assert -X * Z * pow(Y, -1, modulus) % modulus == 629

    A, B, minus = initial_multiples(modulus - 117, 3)
    assert (A, B) == (1135, 466)
    assert minus == [(2, 2), (677, 1306), (0, 444)]
    x, y = minus[-1]
    N = (3 * x * x + 2 * A * x + B) % modulus
    D = 2 * y % modulus
    X = (N * N - (A + 2 * x) * D * D) % modulus
    Y = (-y * D**3 + N * (x * D * D - X)) % modulus
    Z = D
    assert (N, D, X, Y, Z) == (466, 888, 854, 415, 888)
    t6 = -X * Z * pow(Y, -1, modulus) % modulus
    assert t6 == 1036 and 2 * t6 % modulus == 703


def check_external_generator_relation_only():
    """Check P=-H+T; this does not certify that H is a generator."""
    F = Fraction
    I = (F(0), F(1))
    A = gscale(2, I)
    B = (F(-2), F(-4))
    P = ((F(2), F(0)), (F(2), F(0)))
    T = ((F(0), F(0)), (F(0), F(0)))
    H = ((F(-1), F(-2)), (F(-1), F(-2)))
    minus_H = (H[0], gneg(H[1]))
    assert gaussian_curve_add(minus_H, T, A, B) == P


def check_descent_obstructions():
    rows = [
        # curve, A, B, d, modulus
        ("E0_dual_i", (0, -4), (4, 16), (0, 1), 16),
        ("E0_dual_i_rho", (0, -4), (4, 16), (-4, 1), 16),
        ("E1_i", (2, 0), (2, 4), (0, 1), 8),
        ("E1_pi", (2, 0), (2, 4), (1, 2), 4),
        ("E1_dual_i", (-4, 0), (-4, -16), (0, 1), 32),
        ("E1_dual_i_rho", (-4, 0), (-4, -16), (-4, 1), 32),
    ]
    for name, A, B, d, modulus in rows:
        assert not locally_soluble_homogeneous_space(A, B, d, modulus), name


def main():
    check_descent_obstructions()
    check_cardinality_rows()
    check_index_rows()
    check_split37_tables()
    check_formal_row()
    check_mod1369_trace()
    check_external_generator_relation_only()
    print("all Gaussian descent and split-37 certificates verified")


if __name__ == "__main__":
    main()
