#!/usr/bin/env python3
"""Exact identities for the fifth-power norm descent.

This script does not search for factors.  It verifies the symbolic identities
used in the no-large-compute local argument at primes dividing p^2+q^2.
All arithmetic is exact over ZZ/QQ.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    s, x, d, y = sp.symbols("s x d y")
    a, b = sp.symbols("a b")

    c4 = (2 + s) * (3 - 2 * s)
    c3 = 1 + 10 * s + 4 * s**2 - 14 * s**3 + s**4
    c2 = -s * (1 - 14 * s + 4 * s**2 + 10 * s**3 + s**4)
    c1 = -s**3 * (1 + 2 * s) * (-2 + 3 * s)
    P = sp.expand(x**5 + c4*x**4 + c3*x**3 + c2*x**2 + c1*x - s**5)

    translated = sp.expand(P.subs({s: -1 + d, x: -1 + y}, simultaneous=True))
    expected = sp.expand(
        y**5
        + d*(3 - 2*d)*y**4
        + d*(-56 + 60*d - 18*d**2 + d**3)*y**3
        + d*(144 - 192*d + 80*d**2 - 8*d**3 - d**4)*y**2
        - 4*d*(40 - 68*d + 42*d**2 - 11*d**3 + d**4)*y
        + 4*d*(d - 2)**4
    )
    assert translated == expected

    # Primitive Gaussian fifth-power parametrizations.
    real5 = a**5 - 10*a**3*b**2 + 5*a*b**4
    imag5 = 5*a**4*b - 10*a**2*b**3 + b**5
    assert sp.expand(real5**2 + imag5**2 - (a**2 + b**2)**5) == 0

    real5_twisted = sp.expand(real5 - imag5)
    imag5_twisted = sp.expand(real5 + imag5)
    assert sp.expand(
        real5_twisted**2 + imag5_twisted**2 - 2*(a**2 + b**2)**5
    ) == 0

    # The residual polynomial after an edge of slope -m is, up to a fifth
    # power rescaling, Z^5-256.  The constant class is 2^8, so over a field
    # containing the fifth roots of unity it is a fifth power iff 2 is.
    assert 8 % 5 == 3
    assert pow(3, -1, 5) == 2

    print("translated_s_minus_one_identity=OK")
    print("gaussian_fifth_power_norm_identity=OK")
    print("twisted_gaussian_norm_identity=OK")
    print("residual_constant_class=2^3 in F_l^*/F_l^{*5}")


if __name__ == "__main__":
    main()
