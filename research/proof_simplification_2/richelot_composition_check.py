#!/usr/bin/env python3
"""Exact theorem-backed composition check for the C041 Richelot isogeny.

This file checks the *correspondences*, not merely the equations of the two
curves or their degrees.  Work first over ``F=Q(i)``.  For a nonsingular
quadratic splitting ``f=p1*p2*p3``, the classical Richelot theorem attaches a
correspondence ``Z`` between ``C:y^2=f`` and its bracket curve.  Pull-push by
``Z`` and by its transpose gives polarized (2,2)-isogenies ``phi`` and
``hat(phi)``, and the theorem proves

    hat(phi) * phi = [2],       phi * hat(phi) = [2].

See Chow--Jarvis, *A p-adic study of the Richelot isogeny*, Section 3,
especially the displayed correspondence and the paragraph immediately after
it (which in turn cites Cassels--Flynn, Section 8.4):

    https://eprints.whiterose.ac.uk/id/eprint/194471/1/Chow-Jarvis1RJrev1.pdf

For the fact that a Galois-stable splitting whose individual factors need not
be rational gives the correctly twisted isogeny over the ground field, see
Bruin--Doerksen, *The arithmetic of genus two curves with (4,4)-split
Jacobians*, Section 4 (notably its stable-splitting construction and
Proposition 11):

    https://arxiv.org/abs/0902.3480

The theorem is general; the obligations for this particular instance are:

1. verify the splitting, nonzero determinants, smooth source and target;
2. construct the forward correspondence by exact polynomial equations and
   verify that it lies on the product of the displayed curves;
3. construct the bracket correspondence in the reverse direction and prove
   that, after the exact model identifications, it is literally the transpose
   of the forward correspondence;
4. verify Galois stability of the unordered splittings, so the two maps descend
   from ``Q(i)`` to ``Q``.

All four obligations are polynomial identities over ``Q(i)`` checked below
with exact SymPy arithmetic.  Consequently the cited theorem proves the
composition identity over ``Q(i)``.  Since both isogenies descend to ``Q`` and
base extension is faithful on homomorphisms of abelian varieties, it proves
the identity over ``Q`` as well.

This is deliberately not a finite-field fingerprint, a degree-only argument,
or a point sample.  It is a reproducible exact specialization of the
Richelot correspondence theorem.  It does not reimplement generic Cantor
arithmetic, because the pull-push correspondence itself is the theorem's
definition of the two Jacobian maps.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import sympy as sp


class CertificateFailure(RuntimeError):
    """Raised when an exact correspondence identity fails."""


def require(condition: bool, message: str) -> None:
    """Fail closed rather than emitting a claimed composition certificate."""

    if not condition:
        raise CertificateFailure(message)


def coefficient_determinant(
    factors: tuple[sp.Expr, sp.Expr, sp.Expr], variable: sp.Symbol
) -> sp.Expr:
    """Return the determinant of the quadratic coefficient rows."""

    rows = [
        [sp.Poly(factor, variable).nth(degree) for degree in (2, 1, 0)]
        for factor in factors
    ]
    return sp.expand(sp.det(sp.Matrix(rows)))


def brackets(
    factors: tuple[sp.Expr, sp.Expr, sp.Expr], variable: sp.Symbol
) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
    """Return the cyclic Richelot brackets ``[p2,p3],[p3,p1],[p1,p2]``."""

    def bracket(left: sp.Expr, right: sp.Expr) -> sp.Expr:
        return sp.expand(
            sp.diff(left, variable) * right
            - left * sp.diff(right, variable)
        )

    first, second, third = factors
    return (
        bracket(second, third),
        bracket(third, first),
        bracket(first, second),
    )


def exact_quotient(
    numerator: sp.Expr, denominator: sp.Expr, variables: tuple[sp.Symbol, ...]
) -> sp.Expr:
    """Prove exact polynomial divisibility over ``Q(i)`` and return the quotient."""

    quotient = sp.cancel(numerator / denominator)
    require(
        sp.denom(quotient) == 1,
        "a claimed correspondence identity is not polynomially divisible",
    )
    require(
        sp.expand(numerator - denominator * quotient) == 0,
        "a claimed correspondence quotient is not exact",
    )
    require(
        sp.Poly(quotient, *variables, extension=sp.I).as_expr()
        == sp.Poly(sp.expand(quotient), *variables, extension=sp.I).as_expr(),
        "the correspondence quotient did not normalize over Q(i)",
    )
    return sp.factor(quotient)


def conjugate_over_q(expr: sp.Expr, variables: tuple[sp.Symbol, ...]) -> sp.Expr:
    """Apply the nontrivial automorphism of ``Q(i)/Q`` to an exact expression."""

    result = sp.conjugate(expr)
    for variable in variables:
        result = result.subs(sp.conjugate(variable), variable)
    return sp.expand(result)


def certify() -> dict[str, object]:
    """Construct both correspondences and certify dual composition over ``Q``."""

    x, t = sp.symbols("x t")
    i = sp.I

    def source_factors(variable: sp.Symbol) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
        return (
            variable,
            2 * variable**2 + 2 * i * variable - 1 - 2 * i,
            2 * variable**2 - 2 * i * variable - 1 + 2 * i,
        )

    def target_factors(variable: sp.Symbol) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
        return (
            -2 * (2 * variable**2 - 4 * variable + 1),
            2 * variable**2 + 1 - 2 * i,
            2 * variable**2 + 1 + 2 * i,
        )

    p_x = source_factors(x)
    p_t = source_factors(t)
    f_x = sp.expand(sp.prod(p_x))
    expected_f_x = x * (4 * x**4 - 8 * x + 5)
    require(sp.expand(f_x - expected_f_x) == 0, "source splitting is wrong")

    source_delta = coefficient_determinant(p_x, x)
    require(source_delta == -8 * i, "source determinant is not -8*i")
    r_x = brackets(p_x, x)
    r_t = tuple(value.subs(x, t) for value in r_x)

    h_x = target_factors(x)
    h_t = target_factors(t)
    target_t = sp.expand(sp.prod(h_t))
    expected_target_t = sp.expand(
        -2
        * (2 * t**2 - 4 * t + 1)
        * (4 * t**4 + 4 * t**2 + 5)
    )
    require(
        sp.expand(target_t - expected_target_t) == 0,
        "displayed Richelot neighbour has the wrong equation",
    )

    # These scalings identify the raw bracket curve
    # w^2=r1*r2*r3/source_delta with Dhat by Y=2*w.
    require(sp.expand(r_x[0] - 2 * i * h_x[0]) == 0, "r1 scaling is wrong")
    require(sp.expand(r_x[1] - h_x[1]) == 0, "r2 scaling is wrong")
    require(sp.expand(r_x[2] + h_x[2]) == 0, "r3 scaling is wrong")
    raw_target_t = sp.cancel(sp.prod(r_t) / source_delta)
    require(
        sp.expand(target_t - 4 * raw_target_t) == 0,
        "Y=2*w does not identify the raw bracket curve with Dhat",
    )

    # Forward correspondence on C x Dhat.  If E=0 and y*Y=B, the exact
    # divisibility below proves compatibility with y^2=f and Y^2=target.
    forward_e = sp.expand(p_x[0] * r_t[0] + p_x[1] * r_t[1])
    forward_b = sp.expand(2 * i * p_x[0] * r_t[0] * (x - t))
    forward_quotient = exact_quotient(
        sp.expand(f_x * target_t - forward_b**2),
        forward_e,
        (x, t),
    )

    # Reverse Richelot construction on the displayed target triple.
    target_delta = coefficient_determinant(h_x, x)
    require(target_delta == -64 * i, "target determinant is not -64*i")
    s_x = brackets(h_x, x)
    expected_s_x = (
        16 * i * p_x[0],
        8 * p_x[1],
        -8 * p_x[2],
    )
    for index, (actual, expected) in enumerate(zip(s_x, expected_s_x), 1):
        require(
            sp.expand(actual - expected) == 0,
            f"reverse bracket s{index} has the wrong scaling",
        )

    recovered_x = sp.cancel(sp.prod(s_x) / target_delta)
    require(
        sp.expand(recovered_x - 16 * f_x) == 0,
        "the reverse bracket curve is not Z^2=16*f",
    )

    # Reverse correspondence between Dhat(t,Y) and Z^2=16*f(x).  The two
    # identities say exactly that, under Z=4*y, this is the transpose of the
    # forward correspondence, including its ordinate equation.
    reverse_e = sp.expand(h_t[0] * s_x[0] + h_t[1] * s_x[1])
    reverse_b = sp.expand(-i * h_t[0] * s_x[0] * (t - x))
    require(
        sp.expand(reverse_e - 8 * forward_e) == 0,
        "the reverse abscissa correspondence is not the transpose",
    )
    require(
        sp.expand(reverse_b - 4 * forward_b) == 0,
        "the reverse ordinate correspondence is not the transpose under Z=4*y",
    )
    reverse_quotient = exact_quotient(
        sp.expand(target_t * recovered_x - reverse_b**2),
        reverse_e,
        (x, t),
    )

    # Smoothness and nondegeneracy are the exact hypotheses needed by the
    # Richelot correspondence theorem.
    require(
        sp.Poly(sp.gcd(f_x, sp.diff(f_x, x)), x).degree() == 0,
        "the source curve is singular",
    )
    require(
        sp.Poly(sp.gcd(target_t, sp.diff(target_t, t)), t).degree() == 0,
        "the target curve is singular",
    )
    require(
        source_delta != 0 and target_delta != 0,
        "a Richelot determinant vanished",
    )

    # Galois descent: conjugation fixes the unordered pair partitions.  The
    # Richelot homomorphism depends on this maximal isotropic partition, not
    # its ordering.  Thus both maps are Q-rational.  Equality after base
    # extension to Q(i) therefore implies equality over Q.
    p_conjugates = tuple(conjugate_over_q(value, (x, t)) for value in p_x)
    h_conjugates = tuple(conjugate_over_q(value, (x, t)) for value in h_x)
    require(
        p_conjugates == (p_x[0], p_x[2], p_x[1]),
        "source splitting is not Galois stable",
    )
    require(
        h_conjugates == (h_x[0], h_x[2], h_x[1]),
        "target splitting is not Galois stable",
    )

    return {
        "status": "PASS",
        "base_field_for_exact_identities": "Q(i)",
        "source_determinant": str(source_delta),
        "target_determinant": str(target_delta),
        "source_smooth": True,
        "target_smooth": True,
        "forward_correspondence": {
            "abscissa_equation": str(forward_e),
            "ordinate_equation": f"y*Y={forward_b}",
            "curve_compatibility_quotient": str(forward_quotient),
        },
        "reverse_correspondence": {
            "abscissa_equation": str(reverse_e),
            "ordinate_equation": f"Y*Z={reverse_b}",
            "recovered_curve": "Z^2=16*(4*x^5-8*x^2+5*x)",
            "model_identification": "Z=4*y",
            "curve_compatibility_quotient": str(reverse_quotient),
        },
        "transpose_checks": {
            "reverse_E_over_forward_E": 8,
            "reverse_B_over_forward_B": 4,
            "Z_over_y": 4,
        },
        "galois_descent": {
            "source_factor_permutation": "(p2 p3)",
            "target_factor_permutation": "(h2 h3)",
            "maps_defined_over_Q": True,
        },
        "theorem": {
            "name": "polarized Richelot correspondence theorem",
            "reference": (
                "Chow--Jarvis, A p-adic study of the Richelot isogeny, "
                "Section 3; Cassels--Flynn, Section 8.4; "
                "Bruin--Doerksen, Section 4 and Proposition 11"
            ),
            "maps": (
                "phi and hat_phi are pull-push by the exact forward "
                "correspondence and its transpose"
            ),
            "conclusion_over_Qi": (
                "hat_phi o phi=[2] and phi o hat_phi=[2]"
            ),
            "conclusion_over_Q": (
                "same, by Galois descent and faithful base extension"
            ),
        },
        "method": (
            "exact symbolic correspondence arithmetic plus the standard "
            "Richelot theorem; no finite-field samples and no degree-only step"
        ),
    }


def main() -> int:
    """Run the exact certificate and optionally write a canonical JSON transcript."""

    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()
    try:
        payload = certify()
    except CertificateFailure as error:
        print(f"Richelot composition correspondence check: FAIL: {error}")
        return 1

    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if arguments.output is not None:
        arguments.output.write_text(rendered, encoding="utf-8")
    print("Richelot composition correspondence check: PASS")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
