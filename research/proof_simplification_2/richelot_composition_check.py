#!/usr/bin/env python3
"""Exact theorem-backed certificate for the C041 Richelot isogeny.

The nonzero kernel points have etale algebra ``Q x Q(i)``.  Its discriminant
squareclass is ``-1``, so Bruin--Doerksen Proposition 4.3 selects the
quadratic twist

    C  : y^2 = x (4*x^4 - 8*x + 5)
    C' : V^2 = 2 (2*t^2 - 4*t + 1) (4*t^4 + 4*t^2 + 5).

The script proves exact rational equations for the forward correspondence and
its literal transpose, then invokes polarized Richelot duality to certify both
compositions as multiplication by two.  It also contains an exact failure
witness for the former untwisted negative target.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import sympy as sp


class CertificateFailure(RuntimeError):
    """Raised when an exact corrected-twist identity fails."""


def require(condition: bool, message: str) -> None:
    """Fail closed on every asserted algebraic identity."""

    if not condition:
        raise CertificateFailure(message)


def coefficient_determinant(
    factors: tuple[sp.Expr, sp.Expr, sp.Expr],
    variable: sp.Symbol,
) -> sp.Expr:
    """Use Bruin--Doerksen's coefficient order: constant, linear, quadratic."""

    rows = [
        [sp.Poly(factor, variable).nth(degree) for degree in (0, 1, 2)]
        for factor in factors
    ]
    return sp.expand(sp.det(sp.Matrix(rows)))


def brackets(
    factors: tuple[sp.Expr, sp.Expr, sp.Expr],
    variable: sp.Symbol,
) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
    """Return ``[F2,F3], [F3,F1], [F1,F2]`` with ``[A,B]=A'B-AB'``."""

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


def conjugate_over_q(
    expression: sp.Expr,
    variables: tuple[sp.Symbol, ...],
) -> sp.Expr:
    """Conjugate coefficients in ``Q(i)`` while fixing the variables."""

    result = sp.conjugate(expression)
    for variable in variables:
        result = result.subs(sp.conjugate(variable), variable)
    return sp.expand(result)


def exact_quotient(
    numerator: sp.Expr,
    denominator: sp.Expr,
    variables: tuple[sp.Symbol, ...],
) -> sp.Expr:
    """Certify polynomial divisibility over ``Q`` and return the quotient."""

    quotient = sp.cancel(numerator / denominator)
    require(
        sp.denom(quotient) == 1,
        "correspondence compatibility quotient is not a polynomial",
    )
    require(
        sp.expand(numerator - denominator * quotient) == 0,
        "correspondence compatibility division is not exact",
    )
    require(
        sp.Poly(quotient, *variables, domain=sp.QQ).as_expr()
        == sp.Poly(sp.expand(quotient), *variables, domain=sp.QQ).as_expr(),
        "correspondence quotient is not rational",
    )
    return sp.factor(quotient)


def certify() -> dict[str, object]:
    """Certify the corrected Q-rational map, transpose, and old-twist failure."""

    x, t = sp.symbols("x t")
    i = sp.I

    def q1(variable: sp.Symbol) -> sp.Expr:
        return variable

    def q2(variable: sp.Symbol) -> sp.Expr:
        return 2 * variable**2 + 2 * i * variable - 1 - 2 * i

    def q3(variable: sp.Symbol) -> sp.Expr:
        return 2 * variable**2 - 2 * i * variable - 1 + 2 * i

    def h1(variable: sp.Symbol) -> sp.Expr:
        return 2 * variable**2 - 4 * variable + 1

    def h2(variable: sp.Symbol) -> sp.Expr:
        return 2 * variable**2 + 1 - 2 * i

    def h3(variable: sp.Symbol) -> sp.Expr:
        return 2 * variable**2 + 1 + 2 * i

    # Put the conjugate source factors first, exactly as in the easy
    # non-transitive case immediately before Bruin--Doerksen Proposition 4.3.
    source_factors_x = (q2(x), q3(x), q1(x))
    source_factors_t = (q2(t), q3(t), q1(t))
    source = sp.expand(sp.prod(source_factors_x))
    require(
        sp.expand(source - x * (4 * x**4 - 8 * x + 5)) == 0,
        "source splitting is wrong",
    )
    source_delta = coefficient_determinant(source_factors_x, x)
    require(source_delta == 8 * i, "Bruin--Doerksen source delta is not 8*i")

    source_brackets_x = brackets(source_factors_x, x)
    expected_source_brackets = (
        h2(x),
        -h3(x),
        -4 * i * h1(x),
    )
    require(
        all(
            sp.expand(actual - expected) == 0
            for actual, expected in zip(
                source_brackets_x,
                expected_source_brackets,
            )
        ),
        "source bracket triple is wrong",
    )
    source_brackets_t = tuple(
        value.subs(x, t) for value in source_brackets_x
    )
    g_factors_t = tuple(
        sp.cancel(value / source_delta)
        for value in source_brackets_t
    )
    expected_g_factors_t = (
        -i * h2(t) / 8,
        i * h3(t) / 8,
        -h1(t) / 2,
    )
    require(
        all(
            sp.expand(actual - expected) == 0
            for actual, expected in zip(g_factors_t, expected_g_factors_t)
        ),
        "normalized Bruin--Doerksen G_i factors are wrong",
    )
    g_target = sp.cancel(sp.prod(g_factors_t))
    require(
        sp.expand(g_target + h1(t) * h2(t) * h3(t) / 128) == 0,
        "untwisted bracket sextic g is not -h1*h2*h3/128",
    )

    # The nonzero kernel algebra is Q x Q(i), so its exact discriminant is
    # disc(t^2+1)=-4 and its squareclass is -1.  Proposition 4.3 only depends
    # on the squareclass.  If -4*Ytilde^2=g, put Y0=2*Ytilde; then
    # -Y0^2=g.  We use d0=-1 and sqrt(d0)=i in the correspondence formulas.
    kernel_etale_discriminant = sp.discriminant(t**2 + 1, t)
    require(
        kernel_etale_discriminant == -4,
        "kernel etale algebra discriminant is not -4",
    )
    twist_d_exact = kernel_etale_discriminant
    twist_d_squareclass = sp.Integer(-1)
    target = sp.expand(2 * h1(t) * h2(t) * h3(t))
    require(
        sp.expand(target - 2 * h1(t) * (4 * t**4 + 4 * t**2 + 5))
        == 0,
        "correct displayed target does not have the +2 equation",
    )
    # V=16*Y0=32*Ytilde: V^2 = (16^2/d0)*g.
    require(
        sp.expand(
            target
            - sp.Rational(16**2, twist_d_squareclass) * g_target
        )
        == 0,
        "V=16*Y0 does not identify Ctilde_d with the +2 model",
    )

    target_factors_t = (h2(t), h3(t), 2 * h1(t))
    target_factors_x = tuple(value.subs(t, x) for value in target_factors_t)
    require(
        sp.expand(sp.prod(target_factors_t) - target) == 0,
        "displayed target factor triple is wrong",
    )
    target_delta = coefficient_determinant(target_factors_t, t)
    require(
        target_delta == -64 * i,
        "Bruin--Doerksen target delta is not -64*i",
    )
    target_brackets_t = brackets(target_factors_t, t)
    expected_target_brackets_t = (
        -8 * q2(t),
        8 * q3(t),
        16 * i * q1(t),
    )
    require(
        all(
            sp.expand(actual - expected) == 0
            for actual, expected in zip(
                target_brackets_t,
                expected_target_brackets_t,
            )
        ),
        "dual bracket triple is wrong",
    )
    target_brackets_x = tuple(
        value.subs(t, x) for value in target_brackets_t
    )
    dual_g_factors_x = tuple(
        sp.cancel(value / target_delta)
        for value in target_brackets_x
    )
    expected_dual_g_factors_x = (
        -i * q2(x) / 8,
        i * q3(x) / 8,
        -q1(x) / 4,
    )
    require(
        all(
            sp.expand(actual - expected) == 0
            for actual, expected in zip(
                dual_g_factors_x,
                expected_dual_g_factors_x,
            )
        ),
        "normalized dual G_i factors are wrong",
    )
    dual_g = sp.cancel(sp.prod(dual_g_factors_x))
    require(
        sp.expand(dual_g + source / 256) == 0,
        "dual untwisted bracket sextic is not -f/256",
    )
    # For the same squareclass d0=-1, y=-16*Z0 recovers the source exactly.
    # The minus sign is the model identification making the reverse
    # Bruin--Doerksen correspondence literally the forward transpose.
    require(
        sp.expand(
            source
            - sp.Rational((-16) ** 2, twist_d_squareclass) * dual_g
        )
        == 0,
        "the Bruin--Doerksen dual twist does not recover the source",
    )

    # Rational generators for Gamma_d.  They are obtained by taking the
    # conjugate-first equations in Proposition 4.3 and replacing either
    # conjugate ordinate product by their average modulo E=0.
    forward_e_from_theorem = sp.expand(
        source_factors_x[0] * g_factors_t[0]
        + source_factors_x[1] * g_factors_t[1]
    )
    rational_e = sp.expand(
        2 * t**2 * x - 2 * t**2 - 2 * x**2 + x
    )
    require(
        sp.expand(forward_e_from_theorem - rational_e / 2) == 0,
        "the rational abscissa equation is not the theorem's equation",
    )

    rational_b = sp.expand(
        -(
            source_factors_x[0] * h2(t)
            + source_factors_x[1] * h3(t)
        )
        * (x - t)
    )
    expected_rational_b = sp.expand(
        -2
        * (x - t)
        * (4 * t**2 * x**2 - 2 * t**2 + 2 * x**2 + 4 * x - 5)
    )
    require(
        sp.expand(rational_b - expected_rational_b) == 0,
        "the rational ordinate equation has the wrong expansion",
    )

    # With d0=-1, sqrt(d0)=i, and V=16*Y0, Proposition 4.3 gives
    #
    #   F1*G1*(x-t) = i*y*Y0 = (i/16)*y*V.
    #
    # Thus the first theorem branch is exactly the following expression,
    # rather than an independently guessed compatible ordinate equation.
    sqrt_twist_d = i
    target_display_scale = sp.Integer(16)
    first_branch_from_theorem = sp.expand(
        target_display_scale
        / sqrt_twist_d
        * source_factors_x[0]
        * g_factors_t[0]
        * (x - t)
    )
    first_branch_b = sp.expand(
        -2 * source_factors_x[0] * h2(t) * (x - t)
    )
    second_branch_b = sp.expand(
        -2 * source_factors_x[1] * h3(t) * (x - t)
    )
    require(
        sp.expand(first_branch_from_theorem - first_branch_b) == 0,
        "first ordinate branch is not the scaled Proposition 4.3 branch",
    )
    require(
        sp.expand(
            first_branch_b
            - rational_b
            + 4 * i * (x - t) * rational_e
        )
        == 0,
        "Bc-B is not -4*i*(x-t)*E",
    )
    require(
        sp.rem(
            sp.Poly(second_branch_b - rational_b, x, t, extension=i),
            sp.Poly(rational_e, x, t, extension=i),
        ).as_expr()
        == 0,
        "second Bruin--Doerksen ordinate branch is not rational modulo E",
    )
    require(
        conjugate_over_q(rational_e, (x, t)) == rational_e
        and conjugate_over_q(rational_b, (x, t)) == rational_b,
        "the corrected correspondence is not literally defined over Q",
    )

    compatibility_quotient = exact_quotient(
        sp.expand(source * target - rational_b**2),
        rational_e,
        (x, t),
    )

    # Apply Proposition 4.3 to the target splitting with sqrt(d0)=i and
    # identify the recovered source by y=-16*Z0.  From
    #
    #   H1*S1*(t-x) = i*V*Z0 = -(i/16)*V*y
    #
    # we get V*y=16*i*H1*S1*(t-x), literally the forward transpose modulo E.
    reverse_e_from_theorem = sp.expand(
        target_factors_t[0] * dual_g_factors_x[0]
        + target_factors_t[1] * dual_g_factors_x[1]
    )
    require(
        sp.expand(reverse_e_from_theorem - rational_e / 2) == 0,
        "dual abscissa equation is not the forward transpose",
    )
    reverse_first_branch_from_theorem = sp.expand(
        16
        * i
        * target_factors_t[0]
        * dual_g_factors_x[0]
        * (t - x)
    )
    reverse_first_branch_b = sp.expand(
        -2 * q2(x) * h2(t) * (x - t)
    )
    require(
        sp.expand(
            reverse_first_branch_from_theorem - reverse_first_branch_b
        )
        == 0,
        "reverse ordinate branch is not the scaled Proposition 4.3 branch",
    )
    require(
        sp.expand(
            reverse_first_branch_b
            - rational_b
            + 4 * i * (x - t) * rational_e
        )
        == 0,
        "dual ordinate equation is not the forward transpose modulo E",
    )
    reverse_compatibility_quotient = exact_quotient(
        sp.expand(target * source - rational_b**2),
        rational_e,
        (x, t),
    )
    require(
        sp.expand(reverse_compatibility_quotient - compatibility_quotient) == 0,
        "forward and transpose compatibility quotients differ",
    )

    # Exact failure witness for the former -2 certificate.  Its displayed
    # correspondence equation is compatible over Q(i), but its abscissa
    # polynomial and its conjugate are coprime, so that individual graph is
    # not Galois-stable.  Stable factor *sets* alone do not repair this.
    old_r1_t = -4 * i * h1(t)
    old_r2_t = h2(t)
    old_e = sp.expand(q1(x) * old_r1_t + q2(x) * old_r2_t)
    old_e_conjugate = conjugate_over_q(old_e, (x, t))
    old_e_gcd = sp.gcd(
        sp.Poly(old_e, x, t, extension=i),
        sp.Poly(old_e_conjugate, x, t, extension=i),
    ).monic()
    require(
        old_e_gcd.total_degree() == 0,
        "former negative-target abscissa graph unexpectedly became Galois-stable",
    )
    old_target = sp.expand(-2 * h1(t) * h2(t) * h3(t))
    require(
        sp.expand(old_target - 16**2 * g_target) == 0,
        "former -2 curve is not the untwisted Ctilde_1 model",
    )

    require(
        sp.Poly(source, x).sqf_part().degree() == 5
        and sp.Poly(target, t).sqf_part().degree() == 6,
        "source or corrected target is singular",
    )
    require(
        sp.Poly(
            4 * x**4 - 8 * x + 5,
            x,
            domain=sp.QQ,
        ).is_irreducible,
        "source quartic is reducible over Q",
    )
    require(
        sp.Poly(h1(t), t, domain=sp.QQ).is_irreducible
        and sp.Poly(
            4 * t**4 + 4 * t**2 + 5,
            t,
            domain=sp.QQ,
        ).is_irreducible,
        "corrected target quadratic or quartic is reducible over Q",
    )
    require(
        tuple(
            conjugate_over_q(value, (x, t))
            for value in source_factors_x
        )
        == (source_factors_x[1], source_factors_x[0], source_factors_x[2]),
        "source splitting does not have the claimed conjugation action",
    )
    require(
        tuple(
            conjugate_over_q(value, (x, t))
            for value in target_factors_x
        )
        == (target_factors_x[1], target_factors_x[0], target_factors_x[2]),
        "target splitting does not have the claimed conjugation action",
    )

    return {
        "status": "PASS",
        "source_curve": "y^2=x*(4*x^4-8*x+5)",
        "kernel_etale_algebra": "Q x Q(i)",
        "kernel_etale_discriminant": -4,
        "bruin_doerksen_twist_squareclass": -1,
        "twist_normalization": (
            "-4*Ytilde^2=g; Y0=2*Ytilde gives -Y0^2=g"
        ),
        "source_ordered_factors": ["q2", "q3", "q1"],
        "source_quartic_irreducible_over_Q": True,
        "source_delta_constant_linear_quadratic": "8*I",
        "source_normalized_brackets": [
            "-I*h2/8",
            "I*h3/8",
            "-h1/2",
        ],
        "untwisted_g": "-h1*h2*h3/128",
        "correct_target_curve": (
            "V^2=2*(2*t^2-4*t+1)*(4*t^4+4*t^2+5)"
        ),
        "correct_target_identification": (
            "V=16*Y0=32*Ytilde on -Y0^2=-4*Ytilde^2=g"
        ),
        "target_ordered_factors": ["h2", "h3", "2*h1"],
        "target_quadratic_and_quartic_irreducible_over_Q": True,
        "source_and_target_splittings_Galois_stable": True,
        "target_delta_constant_linear_quadratic": "-64*I",
        "dual_normalized_brackets": [
            "-I*q2/8",
            "I*q3/8",
            "-q1/4",
        ],
        "dual_untwisted_g": "-f/256",
        "dual_source_identification": (
            "y=-16*Z0 on -Z0^2=-f/256"
        ),
        "q_rational_correspondence": {
            "E": str(rational_e),
            "ordinate_equation": f"y*V={rational_b}",
            "curve_compatibility_quotient": str(compatibility_quotient),
            "coefficients_fixed_by_conjugation": True,
        },
        "transpose": {
            "same_E": True,
            "same_ordinate_equation": True,
            "sqrt_twist_squareclass_choice": "I",
            "recovered_source_coordinate": "y=-16*Z0",
            "literal_transpose": True,
        },
        "composition": {
            "theorem": (
                "Bruin--Doerksen Proposition 4.3 plus polarized Richelot "
                "duality"
            ),
            "maps_defined_over_Q": True,
            "hat_phi_o_phi": "[2]",
            "phi_o_hat_phi": "[2]",
        },
        "former_negative_target_diagnostic": {
            "curve": "W^2=-2*h1*h2*h3",
            "identification": "W=16*Ytilde on the untwisted Ytilde^2=g",
            "is_bruin_doerksen_quotient": False,
            "old_abscissa_gcd_with_conjugate": "1",
            "old_correspondence_graph_Galois_stable": False,
            "precise_failure": (
                "the old check verified stable factor sets, but not the "
                "Galois stability of the actual correspondence graph"
            ),
        },
    }


def main() -> int:
    """Run the exact certificate and optionally write a JSON transcript."""

    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()
    try:
        payload = certify()
    except Exception as error:
        print(f"Correct-twist Richelot geometry: FAIL: {error}")
        return 1
    if arguments.output is not None:
        arguments.output.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    print("Correct-twist Richelot geometry: PASS")
    print("target: V^2=+2*(2*t^2-4*t+1)*(4*t^4+4*t^2+5)")
    print("Q-rational correspondence and literal transpose: PASS")
    print("former -2 target rejected: its conjugate graphs are coprime")
    if arguments.output is not None:
        print("wrote", arguments.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
