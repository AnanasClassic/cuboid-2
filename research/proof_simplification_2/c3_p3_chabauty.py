#!/usr/bin/env python3
"""Fail-closed exact audit of direct p=3 Chabauty on the genus-three curve.

The curve is

    C3: r^2 = 4*u^8 - 8*u^2 + 5.

This hardened copy differs from the first Target A prototype in four
proof-critical ways:

* every proof gate uses :func:`require`, so ``python -O`` cannot remove it;
* repository helper results are checked before they enter the proof;
* dependency artifacts are bound to exact canonical SHA-256 values and
  checked against explicit metadata contracts; and
* all p-adic tail estimates use universal integer lemmas, not a finite
  search through an arbitrary maximum degree.

The canonical genus-two rank premise remains the shorter, already validated
Schaefer--Stoll certificate.  ``--rank-source richelot`` replays the new
Richelot alternative explicitly, but does not make the larger alternative a
dependency of the simplified proof.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from math import gcd
import os
from pathlib import Path
import sys
from typing import Callable

import sympy as sp


ROOT = Path(
    os.environ.get(
        "CUBOID_REPO_ROOT",
        Path(__file__).resolve().parents[2],
    )
).resolve()
sys.path.insert(0, str(ROOT))

from research.arithmetic_geometry.product_genus2_p7_formal_log import (
    cantor_add as imported_rational_cantor_add,
    qpoly as imported_qpoly,
    valuation_and_unit as imported_valuation_and_unit,
)
from research.arithmetic_geometry.product_genus2_square_sieve import (
    all_reduced_divisors as imported_all_reduced_divisors,
    cantor_add as imported_finite_cantor_add,
    divisor_order as imported_divisor_order,
    point_divisor as imported_point_divisor,
)


DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")
PRIME = 3

ELLIPTIC_RANK_CHECKSUM = (
    "3c33cc66f0bb3a2d659af53e833ce9a24b0e3755cdba4077df15b87c80aa1703"
)
STRUCTURE_CHECKSUM = (
    "31a990b98138affb577a6a59bf8fef05ba811156a3eb5b8c32780a1db87fd7db"
)
OLD_SCHAEFER_STOLL_CHECKSUM = (
    "8cd90ba46311943ac32f7d9b810994a3dbb86913fdeb11b64c8d0e1ae13c19a2"
)
# One-line update point after the corrected Target B artifact lands.
TARGET_B_CHECKSUM = (
    "2545fcdb086557af36efcdb4e7464fd368cdf154b54d41462bb01c8bbbda269a"
)

ELLIPTIC_RANK_PATH = (
    "research/frobenius_audit/candidate_544c_rank_descent.json"
)
STRUCTURE_PATH = "research/proof_simplification/c041_structure.json"
OLD_SCHAEFER_STOLL_PATH = (
    "research/arithmetic_geometry/product_genus2_two_descent.json"
)
TARGET_B_PATH = (
    "research/proof_simplification_2/richelot_isogeny_descent.json"
)


class CertificateFailure(RuntimeError):
    """Raised whenever an exact Target A gate cannot be certified."""


def require(condition: object, message: str) -> None:
    """Fail closed when a claimed certificate identity is not exact."""

    if not condition:
        raise CertificateFailure(message)


def checked_call(name: str, function: Callable, *args, **kwargs):
    """Call an imported helper and translate every failure into certificate failure."""

    try:
        return function(*args, **kwargs)
    except CertificateFailure:
        raise
    except Exception as error:
        raise CertificateFailure(f"imported helper {name} failed") from error


def rational_residue(value: sp.Expr, modulus: int) -> int:
    """Return the exact residue of a rational with unit denominator."""

    require(
        isinstance(modulus, int) and not isinstance(modulus, bool) and modulus > 1,
        "a residue modulus must be an integer greater than one",
    )
    try:
        value = sp.Rational(value)
    except Exception as error:
        raise CertificateFailure("residue input is not rational") from error
    numerator = int(value.p)
    denominator = int(value.q)
    require(
        gcd(denominator, modulus) == 1,
        "a rational residue was requested with non-unit denominator",
    )
    return numerator % modulus * pow(denominator % modulus, -1, modulus) % modulus


def valuation(integer: int, prime: int = PRIME) -> int:
    """Return ``v_prime(integer)``; zero is deliberately outside the contract."""

    require(
        isinstance(integer, int) and not isinstance(integer, bool),
        "valuation input must be an integer",
    )
    require(integer != 0, "the valuation of zero is not finite")
    require(
        isinstance(prime, int)
        and not isinstance(prime, bool)
        and prime >= 2
        and bool(sp.isprime(prime)),
        "valuation base must be prime",
    )
    work = abs(integer)
    answer = 0
    while work % prime == 0:
        work //= prime
        answer += 1
    return answer


def exact_valuation_and_unit(
    value: sp.Expr, prime: int = PRIME
) -> tuple[int, int]:
    """Independently compute the valuation and residue of a rational number."""

    try:
        rational = sp.Rational(value)
    except Exception as error:
        raise CertificateFailure("valuation/unit input is not rational") from error
    require(rational != 0, "valuation/unit input must be nonzero")
    numerator = int(rational.p)
    denominator = int(rational.q)
    numerator_valuation = valuation(numerator, prime)
    denominator_valuation = valuation(denominator, prime)
    numerator_unit = numerator // prime**numerator_valuation
    denominator_unit = denominator // prime**denominator_valuation
    return (
        numerator_valuation - denominator_valuation,
        numerator_unit
        % prime
        * pow(denominator_unit % prime, -1, prime)
        % prime,
    )


def checked_valuation_and_unit(
    value: sp.Expr, prime: int = PRIME
) -> tuple[int, int]:
    """Check the imported valuation helper against an independent computation."""

    result = checked_call(
        "valuation_and_unit", imported_valuation_and_unit, value, prime
    )
    require(
        isinstance(result, tuple)
        and len(result) == 2
        and all(
            isinstance(entry, int) and not isinstance(entry, bool)
            for entry in result
        ),
        "valuation_and_unit returned a malformed pair",
    )
    expected = exact_valuation_and_unit(value, prime)
    require(
        result == expected,
        f"valuation_and_unit mismatch: returned {result}, expected {expected}",
    )
    return expected


def checked_qpoly(expression: sp.Expr, variable: sp.Symbol) -> sp.Poly:
    """Check that the imported polynomial adapter preserves the exact expression."""

    result = checked_call("qpoly", imported_qpoly, expression, variable)
    require(isinstance(result, sp.Poly), "qpoly did not return a SymPy polynomial")
    require(result.gens == (variable,), "qpoly changed the polynomial variable")
    require(result.domain == sp.QQ, "qpoly did not use the rational domain")
    require(
        sp.expand(result.as_expr() - expression) == 0,
        "qpoly changed the polynomial expression",
    )
    return result


def validate_rational_mumford(
    divisor: object,
    variable: sp.Symbol,
    monic_curve: sp.Expr,
    context: str,
) -> tuple[sp.Expr, sp.Expr]:
    """Validate a reduced rational Mumford pair returned by Cantor arithmetic."""

    require(
        isinstance(divisor, tuple) and len(divisor) == 2,
        f"{context}: expected a two-component Mumford pair",
    )
    u, v = divisor
    try:
        u_polynomial = sp.Poly(u, variable, domain=sp.QQ)
        v_polynomial = sp.Poly(v, variable, domain=sp.QQ)
    except Exception as error:
        raise CertificateFailure(
            f"{context}: Mumford coordinates are not rational polynomials"
        ) from error
    require(not u_polynomial.is_zero, f"{context}: Mumford u is zero")
    require(u_polynomial.LC() == 1, f"{context}: Mumford u is not monic")
    degree_u = int(u_polynomial.degree())
    require(degree_u <= 2, f"{context}: Mumford u is not reduced")
    degree_v = -1 if v_polynomial.is_zero else int(v_polynomial.degree())
    require(degree_v < degree_u, f"{context}: Mumford v is not reduced modulo u")
    remainder = sp.rem(
        monic_curve - v_polynomial.as_expr() ** 2,
        u_polynomial.as_expr(),
        variable,
        domain=sp.QQ,
    )
    require(
        sp.expand(remainder) == 0,
        f"{context}: Mumford u does not divide f-v^2",
    )
    if degree_u == 0:
        require(
            u_polynomial.as_expr() == 1 and v_polynomial.is_zero,
            f"{context}: malformed identity divisor",
        )
    return u_polynomial.as_expr(), v_polynomial.as_expr()


def checked_rational_cantor_add(
    first: tuple[sp.Expr, sp.Expr],
    second: tuple[sp.Expr, sp.Expr],
    variable: sp.Symbol,
    monic_curve: sp.Expr,
    context: str,
) -> tuple[sp.Expr, sp.Expr]:
    """Call rational Cantor addition and validate its complete output contract."""

    validate_rational_mumford(first, variable, monic_curve, f"{context} first input")
    validate_rational_mumford(
        second, variable, monic_curve, f"{context} second input"
    )
    result = checked_call(
        "rational cantor_add",
        imported_rational_cantor_add,
        first,
        second,
        variable,
        monic_curve,
    )
    return validate_rational_mumford(
        result, variable, monic_curve, f"{context} output"
    )


FinitePolynomial = tuple[int, ...]
FiniteDivisor = tuple[FinitePolynomial, FinitePolynomial]


def finite_trim(values: object, prime: int, context: str) -> FinitePolynomial:
    """Normalize and validate a finite-field polynomial coefficient tuple."""

    require(
        isinstance(values, tuple) and len(values) >= 1,
        f"{context}: finite polynomial is not a nonempty tuple",
    )
    require(
        all(
            isinstance(value, int) and not isinstance(value, bool)
            for value in values
        ),
        f"{context}: finite polynomial has a non-integer coefficient",
    )
    normalized = [value % prime for value in values]
    while len(normalized) > 1 and normalized[-1] == 0:
        normalized.pop()
    answer = tuple(normalized)
    require(answer == values, f"{context}: finite polynomial is not canonical")
    return answer


def finite_multiply(
    left: FinitePolynomial, right: FinitePolynomial, prime: int
) -> FinitePolynomial:
    """Multiply finite polynomials for independent output validation."""

    coefficients = [0] * (len(left) + len(right) - 1)
    for left_index, left_value in enumerate(left):
        for right_index, right_value in enumerate(right):
            coefficients[left_index + right_index] += left_value * right_value
    normalized = tuple(value % prime for value in coefficients)
    while len(normalized) > 1 and normalized[-1] == 0:
        normalized = normalized[:-1]
    return normalized


def finite_subtract(
    left: FinitePolynomial, right: FinitePolynomial, prime: int
) -> FinitePolynomial:
    """Subtract finite polynomials for independent output validation."""

    length = max(len(left), len(right))
    normalized = tuple(
        (
            (left[index] if index < len(left) else 0)
            - (right[index] if index < len(right) else 0)
        )
        % prime
        for index in range(length)
    )
    while len(normalized) > 1 and normalized[-1] == 0:
        normalized = normalized[:-1]
    return normalized


def finite_remainder(
    dividend: FinitePolynomial,
    divisor: FinitePolynomial,
    prime: int,
) -> FinitePolynomial:
    """Compute a finite-polynomial remainder without repository helpers."""

    require(divisor != (0,), "independent finite division by zero")
    work = list(dividend)
    inverse_lead = pow(divisor[-1], -1, prime)
    while len(work) >= len(divisor) and tuple(work) != (0,):
        coefficient = work[-1] * inverse_lead % prime
        shift = len(work) - len(divisor)
        for index, value in enumerate(divisor):
            work[index + shift] = (work[index + shift] - coefficient * value) % prime
        while len(work) > 1 and work[-1] == 0:
            work.pop()
    return tuple(work)


def finite_curve_monic(prime: int) -> FinitePolynomial:
    """Return the monic ``w=R/2`` model of ``D_+`` over a finite field."""

    return (0, 5 * pow(4, -1, prime) % prime, -2 % prime, 0, 0, 1)


def validate_finite_divisor(
    divisor: object, prime: int, context: str
) -> FiniteDivisor:
    """Validate a canonical reduced finite Mumford representation."""

    require(
        isinstance(divisor, tuple) and len(divisor) == 2,
        f"{context}: finite divisor is not a Mumford pair",
    )
    u = finite_trim(divisor[0], prime, f"{context} u")
    v = finite_trim(divisor[1], prime, f"{context} v")
    require(u != (0,), f"{context}: finite Mumford u is zero")
    require(u[-1] == 1, f"{context}: finite Mumford u is not monic")
    degree_u = len(u) - 1
    degree_v = -1 if v == (0,) else len(v) - 1
    require(degree_u <= 2, f"{context}: finite divisor is not reduced")
    require(degree_v < degree_u, f"{context}: finite v is not reduced modulo u")
    remainder = finite_remainder(
        finite_subtract(
            finite_curve_monic(prime),
            finite_multiply(v, v, prime),
            prime,
        ),
        u,
        prime,
    )
    require(remainder == (0,), f"{context}: finite u does not divide f-v^2")
    if degree_u == 0:
        require(
            (u, v) == ((1,), (0,)),
            f"{context}: malformed finite identity divisor",
        )
    return u, v


def checked_all_reduced_divisors(
    prime: int, expected_order: int
) -> set[FiniteDivisor]:
    """Validate every imported reduced divisor and the exact set cardinality."""

    result = checked_call(
        "all_reduced_divisors", imported_all_reduced_divisors, prime
    )
    require(isinstance(result, set), "all_reduced_divisors did not return a set")
    validated = {
        validate_finite_divisor(item, prime, "all_reduced_divisors output")
        for item in result
    }
    require(
        len(validated) == len(result),
        "all_reduced_divisors contains noncanonical duplicate representations",
    )
    require(
        len(validated) == expected_order,
        f"finite Jacobian order mismatch at {prime}",
    )
    return validated


def checked_point_divisor(
    a_value: int, r_value: int, prime: int
) -> FiniteDivisor:
    """Check the imported point-to-Mumford conversion against its exact formula."""

    result = checked_call(
        "point_divisor", imported_point_divisor, a_value, r_value, prime
    )
    validated = validate_finite_divisor(result, prime, "point_divisor output")
    expected: FiniteDivisor = (
        (-a_value % prime, 1),
        (r_value * pow(2, -1, prime) % prime,),
    )
    require(validated == expected, "point_divisor changed the point or model")
    return validated


def checked_finite_cantor_add(
    first: FiniteDivisor,
    second: FiniteDivisor,
    prime: int,
    context: str,
) -> FiniteDivisor:
    """Call finite Cantor addition and validate the returned Mumford pair."""

    validate_finite_divisor(first, prime, f"{context} first input")
    validate_finite_divisor(second, prime, f"{context} second input")
    result = checked_call(
        "finite cantor_add", imported_finite_cantor_add, first, second, prime
    )
    return validate_finite_divisor(result, prime, f"{context} output")


def checked_divisor_order(
    divisor: FiniteDivisor, prime: int, group_order: int
) -> int:
    """Check the imported order by replaying and validating every group element."""

    reported = checked_call(
        "divisor_order", imported_divisor_order, divisor, prime
    )
    require(
        isinstance(reported, int)
        and not isinstance(reported, bool)
        and 1 <= reported <= group_order,
        "divisor_order returned an invalid order",
    )
    require(
        group_order % reported == 0,
        "reported divisor order does not divide the group order",
    )
    identity: FiniteDivisor = ((1,), (0,))
    value = identity
    seen = {identity}
    for exponent in range(1, reported + 1):
        value = checked_finite_cantor_add(
            value,
            divisor,
            prime,
            f"order replay step {exponent}",
        )
        if exponent < reported:
            require(value != identity, "divisor_order was not minimal")
            require(value not in seen, "order replay repeated before the identity")
            seen.add(value)
    require(value == identity, "reported divisor order does not return to identity")
    return reported


def certify_exponential_linear_induction(
    start: int, offset: int
) -> dict[str, int | str]:
    """Certify ``3^k >= k+offset`` for every integer ``k>=start``.

    The induction base is checked exactly.  Assuming the inequality at
    ``k``, the next-step slack is bounded below by

        3*(k+offset) - ((k+1)+offset)
        = 2*k + 2*offset - 1.

    This affine function is nondecreasing and is checked at ``start``;
    those finite algebraic gates certify every induction step.
    """

    require(
        isinstance(start, int)
        and not isinstance(start, bool)
        and isinstance(offset, int)
        and not isinstance(offset, bool),
        "exponential-linear induction parameters must be integers",
    )
    require(start >= 0, "exponential-linear induction start must be nonnegative")
    base_gap = 3**start - start - offset
    slope = 2
    intercept = 2 * offset - 1
    first_step_slack = slope * start + intercept
    require(base_gap >= 0, "exponential-linear induction base case failed")
    require(slope >= 0, "exponential-linear induction slack decreases")
    require(
        first_step_slack >= 0,
        "exponential-linear induction first step has negative slack",
    )
    return {
        "status": "PASS",
        "domain": f"all integers k>={start}",
        "bound": f"3^k>=k+{offset}",
        "base_gap": base_gap,
        "step_slack": f"{slope}*k+{intercept}",
        "first_step_slack": first_step_slack,
    }


def certify_universal_integer_lemmas() -> dict[str, object]:
    """Certify the two universal ``v_3(n)`` bounds used by every tail.

    For ``k>=1``, ``3^k >= k+2`` follows from the base ``3>=3`` and
    induction slack ``3(k+2)-(k+3)=2k+3>=0``.  For ``k>=2``,
    ``3^k >= k+4`` follows from ``9>=6`` and induction slack
    ``3(k+4)-(k+5)=2k+7>=0``.

    If ``v=v_3(n)``, then ``3^v<=n``.  The first power bound gives
    ``v<=n-2`` for every ``n>=2`` (the ``v=0`` case is immediate).
    For ``n>=4``, the second gives ``v<=n-4`` when ``v>=2``; ``v=0`` is
    immediate and ``v=1`` forces the first eligible multiple ``n>=6``.
    These cases exhaust all integers, so no upper cutoff is involved.
    """

    require(PRIME == 3, "the universal lemmas were specialized to p=3")
    first_power_bound = certify_exponential_linear_induction(1, 2)
    second_power_bound = certify_exponential_linear_induction(2, 4)
    require(
        first_power_bound["status"] == "PASS"
        and second_power_bound["status"] == "PASS",
        "universal exponential-linear induction did not certify",
    )
    require(
        4 % 3 != 0 and 5 % 3 != 0 and 6 % 3 == 0,
        "the v_3(n)=1 edge-case first multiple was not certified",
    )
    require(6 - 4 >= 1, "the v_3(n)=1 edge case for n>=4 failed")
    return {
        "status": "PASS",
        "prime": 3,
        "v3_n_le_n_minus_2": {
            "domain": "all integers n>=2",
            "proof": "v=0 is immediate; v>=1 uses 3^v<=n and 3^v>=v+2",
        },
        "v3_n_le_n_minus_4": {
            "domain": "all integers n>=4",
            "proof": (
                "v=0 is immediate; v=1 forces n>=6; v>=2 uses "
                "3^v<=n and 3^v>=v+4"
            ),
        },
        "method": "base cases plus symbolic induction slack; no degree cutoff",
        "power_bounds": [first_power_bound, second_power_bound],
    }


def universal_v3_le_n_minus_2(integer: int) -> bool:
    """Instantiate the certified bound ``v_3(n)<=n-2`` at any ``n>=2``."""

    require(
        isinstance(integer, int)
        and not isinstance(integer, bool)
        and integer >= 2,
        "the n-2 valuation lemma requires an integer n>=2",
    )
    bound = valuation(integer) <= integer - 2
    require(bound, "the certified n-2 valuation bound failed to instantiate")
    return True


def universal_v3_le_n_minus_4(integer: int) -> bool:
    """Instantiate the certified bound ``v_3(n)<=n-4`` at any ``n>=4``."""

    require(
        isinstance(integer, int)
        and not isinstance(integer, bool)
        and integer >= 4,
        "the n-4 valuation lemma requires an integer n>=4",
    )
    bound = valuation(integer) <= integer - 4
    require(bound, "the certified n-4 valuation bound failed to instantiate")
    return True


def certify_inverse_square_root_integrality(
    rhs: sp.Expr,
    variable: sp.Symbol,
    base_root: sp.Rational,
    context: str,
) -> dict[str, object]:
    """Certify integrality of every coefficient of a formal inverse square root.

    After division by ``base_root^2``, write the input as ``1+P`` with
    ``P`` in ``x*Z_3[x]``.  The universal identity

        (1+P)^(-1/2) = sum_k (-1)^k binom(2k,k) P^k / 4^k

    has 3-integral coefficients because ``4`` is a 3-adic unit.  Each
    coefficient after composition is a finite sum, so this proves the
    complete formal series, not a truncation.
    """

    try:
        base_root = sp.Rational(base_root)
        normalized = sp.Poly(
            sp.expand(rhs / base_root**2), variable, domain=sp.QQ
        )
    except Exception as error:
        raise CertificateFailure(
            f"{context}: inverse-square-root input is not rational polynomial data"
        ) from error
    require(base_root != 0, f"{context}: inverse-square-root branch is zero")
    require(
        gcd(int(base_root.q), PRIME) == 1
        and int(base_root.p) % PRIME != 0,
        f"{context}: inverse-square-root branch is not a 3-adic unit",
    )
    require(
        normalized.coeff_monomial(1) == 1,
        f"{context}: normalized series does not have constant term one",
    )
    nonconstant = normalized.as_expr() - 1
    require(
        sp.expand(nonconstant.subs(variable, 0)) == 0,
        f"{context}: normalized tail is not divisible by the parameter",
    )
    for coefficient in normalized.all_coeffs():
        rational = sp.Rational(coefficient)
        require(
            gcd(int(rational.q), PRIME) == 1,
            f"{context}: normalized polynomial is not 3-integral",
        )
    require(gcd(4, PRIME) == 1, "central-binomial denominators are not units")
    return {
        "status": "PASS",
        "context": context,
        "branch_at_center": str(base_root),
        "universal_series": "(-1)^k*binomial(2*k,k)/4^k for every k>=0",
        "coefficient_ring": "Z_3",
    }


def certify_power_difference_quotient_tail(
    linear: sp.Expr, constant: sp.Expr
) -> dict[str, object]:
    """Certify ``v_3((t_+^n-t_-^n)/(t_+-t_-))>=n-1`` for all n.

    The difference quotients satisfy ``S_1=1``, ``S_2=-b`` and
    ``S_n=-b*S_(n-1)-c*S_(n-2)``.  The checked bounds ``v_3(b)>=1`` and
    ``v_3(c)>=2`` make the induction exact for every ``n>=3``.
    """

    linear_data = checked_valuation_and_unit(linear, PRIME)
    constant_data = checked_valuation_and_unit(constant, PRIME)
    require(linear_data[0] >= 1, "the shifted-u linear coefficient is not in 3Z_3")
    require(
        constant_data[0] >= 2,
        "the shifted-u constant coefficient is not in 9Z_3",
    )
    require(1 + 1 == 2, "difference-quotient b-term induction shift failed")
    require(2 + 0 == 2, "difference-quotient c-term induction shift failed")
    return {
        "status": "PASS",
        "domain": "all integers n>=1",
        "bound": "v_3(S_n)>=n-1",
        "recurrence": "S_n=-b*S_(n-1)-c*S_(n-2)",
        "base_valuations": [0, linear_data[0]],
    }


def certify_h0_unit(
    original_curve: sp.Expr,
    curve_variable: sp.Symbol,
    local_variable: sp.Symbol,
    branch_sign: int,
) -> dict[str, object]:
    """Certify universally that ``H_0(x)=x*unit`` for every ``x in 3Z_3``.

    The inverse-root coefficients are all in ``Z_3``.  After integrating
    and dividing by ``x``, the term of primitive degree ``n>=2`` has
    valuation at least ``n-1-v_3(n)>=1`` by the universal ``n-2`` lemma.
    Thus ``H_0(x)/x`` is congruent to ``branch_sign`` modulo 3 for every
    ``x`` in the full disk.
    """

    require(branch_sign in (1, -1), "H0 branch sign must be +1 or -1")
    shifted_rhs = sp.expand(original_curve.subs(curve_variable, 1 + local_variable))
    series_certificate = certify_inverse_square_root_integrality(
        shifted_rhs,
        local_variable,
        sp.Rational(1),
        f"H0 branch {branch_sign}",
    )
    integer_lemmas = certify_universal_integer_lemmas()
    require(
        integer_lemmas["status"] == "PASS",
        "the universal H0 tail lemma did not certify",
    )
    require(
        rational_residue(sp.Integer(branch_sign), PRIME) != 0,
        "the H0 leading coefficient is not a unit",
    )
    return {
        "status": "PASS",
        "domain": "all x in 3*Z_3",
        "identity": f"H_0(x)=x*U(x), U(x)={branch_sign} mod 3",
        "tail": "v_3(c_(n-1)*x^(n-1)/n)>=n-1-v_3(n)>=1 for every n>=2",
        "inverse_square_root": series_certificate,
        "integer_lemma": "v_3(n)<=n-2 for every integer n>=2",
    }


def c3_points_mod_3() -> dict[str, object]:
    """Enumerate the six points of ``C3(F_3)`` exactly."""

    rows: list[list[object]] = []
    affine_count = 0
    for u_value in range(PRIME):
        rhs = (
            4 * pow(u_value, 8, PRIME) - 8 * u_value**2 + 5
        ) % PRIME
        roots = [
            r_value
            for r_value in range(PRIME)
            if r_value * r_value % PRIME == rhs
        ]
        affine_count += len(roots)
        if roots:
            rows.append([u_value, roots])
    require(affine_count == 4, "unexpected affine point count on C3(F_3)")
    require(
        rows == [[1, [1, 2]], [2, [1, 2]]],
        "unexpected affine points on C3(F_3)",
    )
    return {
        "cardinality": affine_count + 2,
        "affine_rows": rows,
        "infinity_points": 2,
        "known_Q_points_cover_all_disks": True,
    }


def multiple_11D_data() -> tuple[sp.Expr, sp.Expr, dict[str, object]]:
    """Compute ``11*[(1,1)-infinity]`` and its exact p=3 leading data."""

    a, t = sp.symbols("a t")
    original_curve = 4 * a**5 - 8 * a**2 + 5 * a
    monic_curve = original_curve / 4
    divisor = (a - 1, sp.Rational(1, 2))
    multiple = (sp.Integer(1), sp.Integer(0))
    validate_rational_mumford(divisor, a, monic_curve, "divisor D")
    for multiplier in range(1, 12):
        multiple = checked_rational_cantor_add(
            multiple,
            divisor,
            a,
            monic_curve,
            f"{multiplier}*D",
        )
    mumford_u, mumford_v_w = multiple
    mumford_v_R = sp.factor(2 * mumford_v_w)

    quotient, remainder = sp.div(
        original_curve - mumford_v_R**2,
        mumford_u,
        a,
        domain=sp.QQ,
    )
    require(sp.expand(remainder) == 0, "11D failed the original-model curve relation")
    require(quotient != 0, "11D curve-relation quotient vanished")

    shifted_u = checked_qpoly(sp.expand(mumford_u.subs(a, 1 + t)), t)
    require(
        shifted_u.degree() == 2 and shifted_u.LC() == 1,
        "11D shifted Mumford u is not monic quadratic",
    )
    b = shifted_u.coeff_monomial(t)
    c = shifted_u.coeff_monomial(1)
    discriminant = sp.factor(b**2 - 4 * c)

    shifted_v = checked_qpoly(sp.expand(mumford_v_R.subs(a, 1 + t)), t)
    require(shifted_v.degree() == 1, "11D shifted Mumford v is not linear")
    slope = shifted_v.coeff_monomial(t)
    value_at_center = shifted_v.coeff_monomial(1)
    root_center = -b / 2
    r_at_root_center = sp.factor(slope * root_center + value_at_center)
    half_r_difference_squared = sp.factor(slope**2 * discriminant / 4)

    exact_data = {
        "shifted_u_linear": checked_valuation_and_unit(b, PRIME),
        "shifted_u_constant": checked_valuation_and_unit(c, PRIME),
        "u_discriminant": checked_valuation_and_unit(discriminant, PRIME),
        "v_R_slope": checked_valuation_and_unit(slope, PRIME),
        "v_R_at_a_1": checked_valuation_and_unit(value_at_center, PRIME),
        "R_at_root_center": checked_valuation_and_unit(r_at_root_center, PRIME),
        "half_R_difference_squared": checked_valuation_and_unit(
            half_r_difference_squared, PRIME
        ),
    }
    expected_data = {
        "shifted_u_linear": (1, 2),
        "shifted_u_constant": (2, 1),
        "u_discriminant": (4, 1),
        "v_R_slope": (-2, 2),
        "v_R_at_a_1": (-1, 2),
        "R_at_root_center": (3, 2),
        "half_R_difference_squared": (0, 1),
    }
    require(exact_data == expected_data, "unexpected exact 3-adic data for 11D")
    certify_power_difference_quotient_tail(b, c)

    return mumford_u, mumford_v_R, {
        "multiple": "11*D",
        "D": "[(1,1)-infinity]",
        "D_mod_3_order": 11,
        "exact_data": {
            name: {"valuation": pair[0], "unit_mod_3": pair[1]}
            for name, pair in exact_data.items()
        },
        "reduced_support": ["(1,1)", "(1,-1)"],
        "reduction_is_principal": "(1,1)+(1,-1)-2*infinity=divisor(a-1)",
    }


def annihilator_ratio(mumford_u: sp.Expr) -> dict[str, object]:
    """Compute ``lambda=log_1(D)/log_0(D)`` modulo 27 exactly."""

    a, t = sp.symbols("a t")
    original_curve = 4 * a**5 - 8 * a**2 + 5 * a
    shifted_u = checked_qpoly(sp.expand(mumford_u.subs(a, 1 + t)), t)
    require(shifted_u.degree() == 2, "annihilator input u is not quadratic")
    b = shifted_u.coeff_monomial(t)
    c = shifted_u.coeff_monomial(1)
    power_tail = certify_power_difference_quotient_tail(b, c)
    inverse_root_tail = certify_inverse_square_root_integrality(
        original_curve.subs(a, 1 + t),
        t,
        sp.Rational(1),
        "annihilator logarithms",
    )

    inverse_root = sp.series(
        1 / sp.sqrt(original_curve.subs(a, 1 + t)),
        t,
        0,
        4,
    ).removeO()
    difference_quotients = [None, sp.Integer(1), -b, b**2 - c]
    truncated_logs: list[sp.Expr] = []
    primitives: list[sp.Expr] = []
    for power in (0, 1):
        integrand = sp.series(
            (1 + t) ** power * inverse_root,
            t,
            0,
            3,
        ).removeO()
        primitive = sp.expand(sp.integrate(integrand, t))
        primitives.append(primitive)
        coefficients = [
            primitive.coeff(t, degree) for degree in range(1, 4)
        ]
        truncated = sp.factor(
            sum(
                coefficients[degree - 1] * difference_quotients[degree]
                for degree in range(1, 4)
            )
        )
        require(
            checked_valuation_and_unit(truncated, PRIME)[0] == 0,
            f"truncated logarithm {power} is not a 3-adic unit",
        )
        truncated_logs.append(truncated)

    expected_primitives = [
        t - sp.Rational(9, 4) * t**2 + sp.Rational(115, 24) * t**3,
        t - sp.Rational(7, 4) * t**2 + sp.Rational(79, 24) * t**3,
    ]
    require(primitives == expected_primitives, "unexpected primitive truncations")

    integer_lemmas = certify_universal_integer_lemmas()
    require(
        integer_lemmas["status"] == "PASS"
        and power_tail["status"] == "PASS"
        and inverse_root_tail["status"] == "PASS",
        "annihilator tail certificates did not pass",
    )
    # For every omitted primitive degree n>=4:
    # v_3(term)>=n-1-v_3(n)>=3, since v_3(n)<=n-4 universally.

    log_0, log_1 = truncated_logs
    ratio = sp.factor(log_1 / log_0)
    ratio_mod_27 = rational_residue(ratio, 27)
    require(ratio_mod_27 == 7, "annihilator ratio is not 7 modulo 27")
    delta = sp.factor(ratio - 1)
    require(
        checked_valuation_and_unit(delta, PRIME) == (1, 2),
        "lambda-1 does not have the certified valuation and unit",
    )
    require(
        rational_residue(delta / 3, 3) == 2,
        "normalized lambda-1 has the wrong residue",
    )

    return {
        "basis": ["da/R", "a*da/R"],
        "logarithm_direction": "[log_0(D),log_1(D)]",
        "primitive_truncations": [str(item) for item in primitives],
        "tail_after_difference_quotient": "3^3*Z_3 for every degree n>=4",
        "tail_certificate": {
            "inverse_square_root": inverse_root_tail,
            "power_difference_quotients": power_tail,
            "integer_bound": "v_3(n)<=n-4 for every integer n>=4",
        },
        "lambda_definition": "log_1(D)/log_0(D)",
        "lambda_mod_27": ratio_mod_27,
        "lambda_valuation": 0,
        "lambda_minus_1": {
            "valuation": 1,
            "unit_mod_3": 2,
        },
        "log_0_11D_valuation": 2,
        "log_0_D_valuation": 2,
        "valuation_reason": (
            "The root difference has valuation 2 and the divided first "
            "logarithm is a unit; 11 is a 3-adic unit."
        ),
        "D_plus_annihilator": "(lambda-a)*da/R",
        "C3_pullback_annihilator": "(lambda-u^2)*du/r (up to a unit scalar)",
    }


def affine_disk_audit(annihilator: dict[str, object]) -> dict[str, object]:
    """Prove the degree-two Weierstrass reduction in four affine disks."""

    require(
        annihilator.get("lambda_minus_1")
        == {"valuation": 1, "unit_mod_3": 2},
        "affine disk audit lacks the certified lambda-1 input",
    )
    integer_lemmas = certify_universal_integer_lemmas()
    require(integer_lemmas["status"] == "PASS", "affine tail lemma failed")

    t, z, delta, delta_unit = sp.symbols("t z delta delta_unit")
    u = sp.symbols("u")
    c3_rhs = 4 * u**8 - 8 * u**2 + 5
    records: list[dict[str, object]] = []

    for center_u in (1, -1):
        local_rhs = sp.expand(c3_rhs.subs(u, center_u + t))
        inverse_root_tail = certify_inverse_square_root_integrality(
            local_rhs,
            t,
            sp.Rational(1),
            f"C3 affine center u={center_u}",
        )
        local_inverse_r = sp.series(
            1 / sp.sqrt(local_rhs),
            t,
            0,
            4,
        ).removeO()
        integrand = sp.series(
            (1 + delta - (center_u + t) ** 2) * local_inverse_r,
            t,
            0,
            4,
        ).removeO()
        primitive = sp.expand(sp.integrate(integrand, t))

        normalized = sp.expand(
            primitive.subs({t: 3 * z, delta: 3 * delta_unit}) / 9
        )
        truncated_reduction = sp.Poly(
            normalized.subs(delta_unit, 2),
            z,
            domain=sp.QQ,
        )
        reduced_coefficients = {
            degree: rational_residue(
                truncated_reduction.coeff_monomial(z**degree),
                3,
            )
            for degree in range(1, 5)
        }
        expected_quadratic = sp.expand(2 * z - center_u * z**2)
        expected_coefficients = {
            degree: int(expected_quadratic.coeff(z, degree)) % 3
            for degree in range(1, 5)
        }
        require(
            reduced_coefficients == expected_coefficients,
            f"wrong affine reduction at u={center_u}",
        )
        require(
            inverse_root_tail["status"] == "PASS",
            f"inverse-root tail failed at u={center_u}",
        )
        # Delta terms of degree n>=2 have valuation
        # n-1-v_3(n)>=1 by v_3(n)<=n-2.
        # Non-delta terms of degree n>=4 have valuation
        # n-2-v_3(n)>=2 by the stronger v_3(n)<=n-4.

        second_root = 2 if center_u == 1 else 1
        reduced = sp.Poly(expected_quadratic, z, modulus=3)
        require(reduced.eval(0) == 0, "known affine zero disappeared")
        require(
            reduced.eval(second_root) == 0,
            "second affine zero class disappeared",
        )
        derivative = reduced.diff()
        require(
            derivative.eval(0) % 3 != 0,
            "known affine zero is not simple",
        )
        require(
            derivative.eval(second_root) % 3 != 0,
            "second affine zero is not simple",
        )

        records.append(
            {
                "u_center": center_u,
                "r_centers": [1, -1],
                "local_parameter": f"u-({center_u})=3*z",
                "normalized_primitive_reduction": str(expected_quadratic),
                "simple_zero_classes_z_mod_3": [0, second_root],
                "second_zero_u_mod_9": (center_u + 3 * second_root) % 9,
                "zeros_per_r_disk": 2,
                "tail_scope": "all primitive degrees, with no cutoff",
            }
        )

    return {
        "records": records,
        "weierstrass_degree_per_affine_disk": 2,
        "total_affine_disks": 4,
        "total_affine_coleman_zeros": 8,
        "universal_tail_lemmas": integer_lemmas,
        "conclusion": (
            "Each affine disk contains its known rational point and one "
            "additional simple Q_3 Coleman zero."
        ),
    }


def infinity_disk_audit(annihilator: dict[str, object]) -> dict[str, object]:
    """Prove uniqueness in each of the two infinity residue disks."""

    require(
        annihilator.get("lambda_valuation") == 0,
        "infinity audit lacks a certified integral lambda",
    )
    integer_lemmas = certify_universal_integer_lemmas()
    require(integer_lemmas["status"] == "PASS", "infinity tail lemma failed")
    t, z, lam = sp.symbols("t z lambda")
    infinity_rhs = 4 - 8 * t**6 + 5 * t**8
    inverse_root_tail = certify_inverse_square_root_integrality(
        infinity_rhs,
        t,
        sp.Rational(2),
        "C3 infinity branches",
    )
    records = []
    for sign in (1, -1):
        inverse_s = sign * sp.series(
            1 / sp.sqrt(infinity_rhs),
            t,
            0,
            9,
        ).removeO()
        integrand = sp.series(
            (1 - lam * t**2) * inverse_s,
            t,
            0,
            9,
        ).removeO()
        primitive = sp.integrate(integrand, t)
        leading = sp.expand(primitive).coeff(t, 1)
        require(
            rational_residue(leading, 3) != 0,
            f"infinity branch {sign} has non-unit leading coefficient",
        )
        # Every degree n>=2 has valuation n-1-v_3(n)>=1 after t=3z
        # and division by 3, by the universal n-2 lemma.
        records.append(
            {
                "infinity_branch": "+2" if sign == 1 else "-2",
                "local_parameter": "t=1/u=3*z",
                "normalized_linear_coefficient_mod_3": rational_residue(
                    leading, 3
                ),
                "zeros_in_disk": 1,
            }
        )
    require(
        inverse_root_tail["status"] == "PASS",
        "infinity inverse-square-root tail failed",
    )
    return {
        "records": records,
        "total_infinity_coleman_zeros": 2,
        "universal_tail": {
            "inverse_square_root": inverse_root_tail,
            "integer_bound": "v_3(n)<=n-2 for every integer n>=2",
        },
        "conclusion": "Each infinity disk contains only its known point.",
    }


def prime_7_index_audit() -> dict[str, object]:
    """Prove that the unknown odd Mordell--Weil index is prime to 3."""

    divisors = checked_all_reduced_divisors(7, 42)
    d_mod_7 = checked_point_divisor(1, 1, 7)
    require(d_mod_7 in divisors, "D mod 7 is absent from the complete divisor set")
    jacobian_order = len(divisors)
    d_order = checked_divisor_order(d_mod_7, 7, jacobian_order)
    require(jacobian_order == 42, "J(F_7) does not have order 42")
    require(d_order == 21, "D mod 7 does not have order 21")

    possible_orders: set[int] = set()
    possible_pairs: list[list[int]] = []
    for order in range(1, jacobian_order + 1):
        if jacobian_order % order:
            continue
        for odd_index in range(1, 2 * jacobian_order + 1, 2):
            if order // gcd(order, odd_index) == d_order:
                possible_orders.add(order)
                possible_pairs.append([order, odd_index % 21])
    require(
        possible_orders == {21},
        "finite-group divisibility allowed an unexpected generator order",
    )
    require(
        all(gcd(residue, 21) == 1 for _, residue in possible_pairs),
        "finite-group divisibility did not prove 3-saturation",
    )

    return {
        "J_F7_order": jacobian_order,
        "D_mod_7_order": d_order,
        "possible_order_of_G_mod_7": [21],
        "unknown_index": "D=mG with m odd",
        "conclusion": "gcd(m,21)=1, in particular 3 does not divide m",
        "scope": (
            "Only the complete finite group and the order of D are used. "
            "Every imported finite Mumford output is validated."
        ),
    }


def rational_lattice_refinement(
    annihilator: dict[str, object],
) -> dict[str, object]:
    """Remove the four extra Coleman zeros for rational points."""

    require(
        annihilator.get("lambda_minus_1")
        == {"valuation": 1, "unit_mod_3": 2},
        "lattice refinement lacks the certified lambda-1 input",
    )
    integer_lemmas = certify_universal_integer_lemmas()
    require(integer_lemmas["status"] == "PASS", "refined-disk tail lemma failed")
    x, z, delta, delta_unit = sp.symbols("x z delta delta_unit")
    a = sp.symbols("a")
    original_curve = 4 * a**5 - 8 * a**2 + 5 * a
    records: list[dict[str, object]] = []

    for r_sign in (1, -1):
        h0_certificate = certify_h0_unit(
            original_curve, a, x, r_sign
        )
        require(
            h0_certificate["status"] == "PASS",
            f"H0 unit certificate failed at R={r_sign}",
        )
        inverse_r = r_sign * sp.series(
            1 / sp.sqrt(original_curve.subs(a, 1 + x)),
            x,
            0,
            5,
        ).removeO()
        first_log_primitive = sp.expand(
            sp.integrate(sp.series(inverse_r, x, 0, 5).removeO(), x)
        )
        require(
            rational_residue(first_log_primitive.coeff(x, 1), 3) != 0,
            f"H0 leading coefficient is not a unit at R={r_sign}",
        )

        annihilator_integrand = sp.series(
            (delta - x) * inverse_r,
            x,
            0,
            5,
        ).removeO()
        annihilator_primitive = sp.expand(
            sp.integrate(annihilator_integrand, x)
        )
        normalized = sp.expand(
            annihilator_primitive.subs(
                {x: 9 * z, delta: 3 * delta_unit}
            )
            / 27
        )
        reduction_coefficients = {
            degree: rational_residue(
                sp.Poly(
                    normalized.subs(delta_unit, 2),
                    z,
                    domain=sp.QQ,
                ).coeff_monomial(z**degree),
                3,
            )
            for degree in range(1, 6)
        }
        expected_linear = 2 * r_sign % 3
        require(
            reduction_coefficients[1] == expected_linear,
            f"wrong refined linear coefficient at R={r_sign}",
        )
        require(
            all(
                reduction_coefficients[degree] == 0
                for degree in range(2, 6)
            ),
            f"unexpected refined nonlinear coefficient at R={r_sign}",
        )
        # Delta terms of primitive degree n>=2 have lower bound
        # 2n-2-v_3(n) >= n >=1, using v_3(n)<=n-2.
        # Terms from -x have lower bound
        # 2n-3-v_3(n) >= n-1 >=1, again for every n>=2.

        records.append(
            {
                "D_plus_center": f"(1,{r_sign})",
                "local_coordinate": "x=a-1",
                "first_log": "H_0(x)=x*unit for every x in 3*Z_3",
                "H0_universal_certificate": h0_certificate,
                "rational_lattice_constraint": "x in 9*Z_3",
                "refined_parameter": "x=9*z",
                "normalized_annihilator_reduction": (
                    f"{expected_linear}*z over F_3"
                ),
                "rational_zero": "z=0 only",
            }
        )

    return {
        "records": records,
        "universal_tail_lemmas": integer_lemmas,
        "argument": (
            "For Q in the same affine disk as P, log_0([Q-P]) is an "
            "integral multiple of log_0(G), hence lies in 9*Z_3. The "
            "universal formal-series certificate proves H_0(x)=x times a "
            "unit on the entire disk, so x=a(Q)-1 lies in 9*Z_3. The "
            "annihilating primitive is then z times a unit."
        ),
        "conclusion": (
            "The additional Coleman zero has a-1 congruent to 3 modulo 9 "
            "and cannot be rational. Every rational affine point has a=1."
        ),
    }


@dataclass(frozen=True)
class ArtifactContract:
    """Exact metadata and digest contract for one dependency artifact."""

    checksum: str
    schema: int = 1
    status: str | None = None
    target: str | None = None


def _strict_json_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    """Reject duplicate JSON keys instead of silently accepting the last one."""

    answer: dict[str, object] = {}
    for key, value in pairs:
        require(key not in answer, f"dependency artifact repeats JSON key {key!r}")
        answer[key] = value
    return answer


def checked_artifact(
    relative_path: str,
    contract: ArtifactContract,
    *,
    root: Path | None = None,
) -> dict[str, object]:
    """Load a dependency and enforce its exact digest and metadata contract."""

    relative = Path(relative_path)
    require(
        not relative.is_absolute() and ".." not in relative.parts,
        "dependency artifact path escapes the repository root",
    )
    path = (ROOT if root is None else Path(root)) / relative
    try:
        text = path.read_text(encoding="utf-8")
    except Exception as error:
        raise CertificateFailure(f"cannot read dependency artifact {relative_path}") from error
    try:
        payload = json.loads(text, object_pairs_hook=_strict_json_object)
    except CertificateFailure:
        raise
    except Exception as error:
        raise CertificateFailure(
            f"dependency artifact {relative_path} is not valid JSON"
        ) from error
    require(
        isinstance(payload, dict),
        f"dependency artifact {relative_path} is not a JSON object",
    )
    require(
        payload.get("schema") == contract.schema,
        f"dependency artifact {relative_path} has the wrong schema",
    )
    if contract.status is not None:
        require(
            payload.get("status") == contract.status,
            f"dependency artifact {relative_path} is not status {contract.status}",
        )
    if contract.target is not None:
        require(
            payload.get("target") == contract.target,
            f"dependency artifact {relative_path} has the wrong target",
        )
    checksum = payload.get("sha256_without_checksum")
    require(
        isinstance(checksum, str)
        and len(checksum) == 64
        and all(character in "0123456789abcdef" for character in checksum),
        f"dependency artifact {relative_path} has a malformed checksum",
    )
    require(
        checksum == contract.checksum,
        f"dependency artifact {relative_path} is not the pinned version",
    )
    canonical_payload = dict(payload)
    del canonical_payload["sha256_without_checksum"]
    canonical = json.dumps(
        canonical_payload, sort_keys=True, separators=(",", ":")
    ).encode()
    require(
        hashlib.sha256(canonical).hexdigest() == checksum,
        f"dependency artifact {relative_path} checksum does not verify",
    )
    return payload


def checked_dependencies(
    rank_source: str,
) -> tuple[dict[str, object], dict[str, object], dict[str, object], list[dict[str, object]]]:
    """Check all rank/quotient dependencies and return normalized contracts."""

    require(
        rank_source in {"richelot", "legacy"},
        "rank source must be 'richelot' or 'legacy'",
    )
    elliptic = checked_artifact(
        ELLIPTIC_RANK_PATH,
        ArtifactContract(ELLIPTIC_RANK_CHECKSUM),
    )
    require(elliptic.get("rank") == 1, "elliptic dependency does not prove rank one")
    require(
        isinstance(elliptic.get("non_torsion_certificate"), dict)
        and elliptic["non_torsion_certificate"].get("P") == "(0,2)",
        "elliptic dependency has the wrong non-torsion point",
    )

    structure = checked_artifact(
        STRUCTURE_PATH,
        ArtifactContract(STRUCTURE_CHECKSUM, status="PASS"),
    )
    require(
        isinstance(structure.get("quotients"), dict)
        and structure["quotients"].get("jacobian_isogeny")
        == "Jac(C3) ~ E1 x Jac(D+) over Q",
        "structure dependency has the wrong Jacobian isogeny",
    )

    contracts = [
        {
            "schema": 1,
            "status": "PASS",
            "target": "rank E1(Q)=1",
            "path": ELLIPTIC_RANK_PATH,
            "checksum": ELLIPTIC_RANK_CHECKSUM,
            "legacy_metadata_adapter": True,
        },
        {
            "schema": 1,
            "status": "PASS",
            "target": "C3 quotient structure",
            "path": STRUCTURE_PATH,
            "checksum": STRUCTURE_CHECKSUM,
            "legacy_metadata_adapter": "target only",
        },
    ]

    if rank_source == "legacy":
        genus_two = checked_artifact(
            OLD_SCHAEFER_STOLL_PATH,
            ArtifactContract(OLD_SCHAEFER_STOLL_CHECKSUM),
        )
        require(genus_two.get("rank") == 1, "old descent does not prove rank one")
        require(
            genus_two.get("rank_upper_bound") == 1,
            "old descent has the wrong rank upper bound",
        )
        require(
            genus_two.get("rational_2_torsion_dimension") == 1
            and genus_two.get("torsion") == "Z/2Z generated by T",
            "old descent has the wrong rational torsion",
        )
        require(
            genus_two.get("D_and_T_independent_mod_2") is True,
            "old descent does not certify D,T independence modulo 2",
        )
        require(
            genus_two.get("successive_local_survivor_counts")
            == {"square_norm": 512, "at_2": 64, "at_5": 8, "at_17": 4},
            "old descent has the wrong complete local survivor chain",
        )
        contracts.append(
            {
                "schema": 1,
                "status": "PASS",
                "target": "rank Jac(D+)(Q)=1 and D,T independent modulo 2",
                "path": OLD_SCHAEFER_STOLL_PATH,
                "checksum": OLD_SCHAEFER_STOLL_CHECKSUM,
                "legacy_metadata_adapter": True,
            }
        )
    else:
        target_b_contract = ArtifactContract(
            TARGET_B_CHECKSUM,
            schema=2,
            status="PASS",
            target="B",
        )
        target_b_override = os.environ.get("CUBOID_TARGET_B_ARTIFACT")
        if target_b_override is None:
            genus_two = checked_artifact(TARGET_B_PATH, target_b_contract)
        else:
            # This exact-pin-preserving override exists only so Target A can
            # be replayed against a newly generated Target B before that
            # artifact is copied to its canonical repository path.
            override_path = Path(target_b_override).resolve()
            require(
                override_path.is_file(),
                "CUBOID_TARGET_B_ARTIFACT is not a readable artifact file",
            )
            genus_two = checked_artifact(
                override_path.name,
                target_b_contract,
                root=override_path.parent,
            )
        rank_inequality = genus_two.get("rank_inequality")
        require(
            isinstance(rank_inequality, dict)
            and rank_inequality.get("rank") == 1
            and rank_inequality.get("torsion") == "Z/2Z generated by T",
            "Target B has the wrong rank/torsion conclusion",
        )
        descent = genus_two.get("descent")
        require(
            isinstance(descent, dict)
            and isinstance(descent.get("generalized_descent_function"), dict)
            and descent["generalized_descent_function"].get(
                "D_T_images_independent"
            )
            is True,
            "Target B does not certify D,T independence",
        )
        conservatism = genus_two.get("conservatism")
        require(
            isinstance(conservatism, dict)
            and conservatism.get(
                "existing_full_descent_is_a_logical_dependency"
            )
            is False,
            "Target B still depends logically on the old full descent",
        )
        contracts.append(
            {
                "schema": 2,
                "status": "PASS",
                "target": "B",
                "path": TARGET_B_PATH,
                "checksum": TARGET_B_CHECKSUM,
                "legacy_metadata_adapter": False,
            }
        )
    return elliptic, genus_two, structure, contracts


def verify(*, rank_source: str = "legacy") -> dict[str, object]:
    """Run every exact gate and return the canonical Target A payload."""

    _, _, _, dependency_contracts = checked_dependencies(rank_source)

    u, a = sp.symbols("u a")
    c3_rhs = 4 * u**8 - 8 * u**2 + 5
    d_plus_rhs = 4 * a**5 - 8 * a**2 + 5 * a
    require(
        int(sp.discriminant(c3_rhs, u)) % 3 != 0,
        "C3 does not have good reduction at 3",
    )
    require(
        int(sp.discriminant(d_plus_rhs, a)) % 3 != 0,
        "D+ does not have good reduction at 3",
    )

    integer_lemmas = certify_universal_integer_lemmas()
    points = c3_points_mod_3()
    require(points["cardinality"] == 6, "C3(F_3) cardinality is not six")
    divisors_at_3 = checked_all_reduced_divisors(3, 22)
    d_mod_3 = checked_point_divisor(1, 1, 3)
    require(d_mod_3 in divisors_at_3, "D mod 3 is absent from J(F_3)")
    require(
        checked_divisor_order(d_mod_3, 3, len(divisors_at_3)) == 11,
        "D mod 3 does not have order 11",
    )
    mumford_u, _, multiple_data = multiple_11D_data()
    annihilator = annihilator_ratio(mumford_u)
    affine = affine_disk_audit(annihilator)
    infinity = infinity_disk_audit(annihilator)
    index_at_7 = prime_7_index_audit()
    lattice = rational_lattice_refinement(annihilator)

    checked_paths = [entry["path"] for entry in dependency_contracts]
    payload: dict[str, object] = {
        "schema": 1,
        "status": "PASS",
        "target": "A",
        "curve": "C3: r^2=4*u^8-8*u^2+5",
        "prime": 3,
        "rank_inputs": {
            "Jac_C3_isogeny": "Jac(C3) ~ E1 x Jac(D+) over Q",
            "rank_E1_Q": 1,
            "rank_Jac_D_plus_Q": 1,
            "rank_Jac_C3_Q": 2,
            "annihilator_dimension": 1,
            "primitive_generator_assumed": False,
            "genus_two_rank_source": rank_source,
            "reason": (
                "Both non-torsion factor logarithms are nonzero; the "
                "prime-to-3 quotient isogeny separates their tangent directions."
            ),
            "checked_artifacts": checked_paths,
            "dependency_contracts": dependency_contracts,
            "good_reduction_at_3": True,
        },
        "universal_integer_lemmas": integer_lemmas,
        "finite_reduction": points,
        "formal_log_input": multiple_data,
        "annihilator": annihilator,
        "affine_disks": affine,
        "infinity_disks": infinity,
        "raw_coleman_zero_count": {
            "known_rational_points": 6,
            "affine_zeros": 8,
            "infinity_zeros": 2,
            "total": 10,
            "additional_Q3_zeros": 4,
        },
        "prime_7_index_audit": index_at_7,
        "rational_lattice_refinement": lattice,
        "rational_points": [
            "infinity_+",
            "infinity_-",
            "(1,1)",
            "(1,-1)",
            "(-1,1)",
            "(-1,-1)",
        ],
        "target_A_conclusion": (
            "SUCCESS. Direct p=3 Chabauty plus the integral Mordell--Weil "
            "lattice refinement proves that C3(Q) consists exactly of the "
            "two infinities and (u,r)=(+/-1,+/-1)."
        ),
        "proof_dependency_change": {
            "removed": [
                "p=23 Mordell--Weil sieve",
                "p=7 square-abscissa class tables",
                "exact 42D p=7 formal logarithm",
                "p=7 Coleman differential and disk bound",
                "coefficient comparison modulo 21/231",
            ],
            "retained": [
                (
                    "rank Jac(D+)(Q)=1 from the pinned Schaefer--Stoll descent"
                    if rank_source == "legacy"
                    else "rank Jac(D+)(Q)=1 from Target B"
                ),
                "#J(F7)=42 and ord(D mod 7)=21 for rank and 3-saturation",
            ],
        },
        "failure_policy": (
            "Every gate raises CertificateFailure; optimization cannot remove "
            "proof checks, and imported helper outputs are validated."
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def main() -> None:
    """Run the certificate and write output only after every gate passes."""

    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--rank-source",
        choices=("legacy", "richelot"),
        default="legacy",
    )
    args = parser.parse_args()
    if (
        args.rank_source != "legacy"
        and args.output.resolve() == DEFAULT_OUTPUT.resolve()
    ):
        parser.error(
            "--rank-source richelot requires an explicit noncanonical --output"
        )
    payload = verify(rank_source=args.rank_source)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print("direct p=3 genus-three Chabauty audit: PASS")
    print("four raw extra Q_3 zeros; integral MW lattice removes all four")
    print("Target A replacement: SUCCESS")
    print("wrote", args.output)


if __name__ == "__main__":
    try:
        main()
    except CertificateFailure as error:
        print(f"direct p=3 genus-three Chabauty audit: FAIL: {error}", file=sys.stderr)
        raise SystemExit(1) from error
