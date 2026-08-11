#!/usr/bin/env python3
"""Derive the simultaneous-reciprocal quotient of the positive compact model.

Everything here is over ``QQ``.  The calculation starts from the 71-term
positive compact model, rather than from a separately copied plane equation.
Writing ``S=z^2`` and ``K=k^2``, the involution

    (S,K) -> (1/S,1/K)

becomes ``(x,y)->(-x,-y)`` after the two Cayley transforms.  Its fixed field
is ``QQ(U,V)`` with ``U=x/y`` and ``V=x*y``.  The output is the primitive
29-term equation C8(U,V)=0 and an exact audit of the omitted affine charts.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import sympy as sp

DEFAULT_OUTPUT = Path(__file__).with_name("reciprocal_quotient.json")
SOURCE = Path(__file__).parents[1] / "compact_signed_square.json"
z, k, S, K, x, y, X, r, U, V = sp.symbols("z k S K x y X r U V")


def sparse(poly: sp.Expr, variables: tuple[sp.Symbol, ...]) -> list[dict[str, object]]:
    return [
        {"powers": list(powers), "coefficient": str(coefficient)}
        for powers, coefficient in sp.Poly(poly, *variables).terms()
    ]


def even_relabel(poly: sp.Expr) -> sp.Expr:
    """Replace z^(2i)k^(2j) by S^i K^j, checking evenness."""
    answer = 0
    for (ez, ek), coefficient in sp.Poly(poly, z, k).terms():
        assert ez % 2 == ek % 2 == 0
        answer += coefficient * S ** (ez // 2) * K ** (ek // 2)
    return sp.expand(answer)


def load_source_models() -> tuple[dict[str, sp.Expr], dict[str, object]]:
    source = json.loads(SOURCE.read_text(encoding="utf-8"))
    assert source["schema"] == 1
    models: dict[str, sp.Expr] = {}
    for label in ("positive", "negative"):
        models[label] = sp.Poly.from_dict(
            {
                tuple(int(power) for power in record["powers"]): sp.Integer(
                    record["coefficient"]
                )
                for record in source["models"][label]["Q_terms"]
            },
            (z, k),
            domain=sp.ZZ,
        ).as_expr()
    assert sp.expand(models["negative"] + models["positive"].subs(k, sp.I * k)) == 0
    return models, source


def cayley_numerator(qbar: sp.Expr) -> sp.Expr:
    """Clear the known Cayley denominator without rational simplification."""
    answer = 0
    for (i, j), coefficient in sp.Poly(qbar, S, K).terms():
        answer += (
            coefficient
            * (1 + x) ** i
            * (1 - x) ** (8 - i)
            * (1 + y) ** j
            * (1 - y) ** (10 - j)
        )
    return sp.expand(answer)


def radial_polynomial(pxy: sp.Expr, x_power: int) -> sp.Expr:
    radial = sp.Poly(sp.expand(pxy.subs(y, r * x)), x, r)
    assert min(exponents[0] for exponents, _ in radial.terms()) == x_power
    quotient, remainder = sp.div(radial, sp.Poly(x**x_power, x, r))
    assert remainder.is_zero
    assert all(exponent % 2 == 0 for (exponent, _), _ in quotient.terms())
    return sp.expand(
        sum(
            coefficient * X ** (exponent // 2) * r**r_exponent
            for (exponent, r_exponent), coefficient in quotient.terms()
        )
    )


def primitive_integer(poly: sp.Expr, variables: tuple[sp.Symbol, ...]) -> sp.Expr:
    item = sp.Poly(sp.expand(poly), *variables, domain=sp.QQ)
    _, primitive = item.clear_denoms(convert=True)
    _, primitive = primitive.primitive()
    if primitive.LC() < 0:
        primitive = -primitive
    return primitive.as_expr()


def verify() -> dict[str, object]:
    models, source = load_source_models()
    q_plus = models["positive"]
    q_minus = models["negative"]
    qbar = even_relabel(q_plus)
    qbar_minus = even_relabel(q_minus)
    assert sp.expand(qbar_minus + qbar.subs(K, -K)) == 0

    cayley_num = cayley_numerator(qbar)
    cayley_num_minus = cayley_numerator(qbar_minus)
    assert sp.Poly(cayley_num, x, y).content() == 1024
    assert sp.Poly(cayley_num_minus, x, y).content() == 1024
    pxy = sp.expand(-cayley_num / 1024)
    pxy_minus = sp.expand(cayley_num_minus / 1024)
    assert len(sp.Poly(pxy, x, y).terms()) == 29
    assert len(sp.Poly(pxy_minus, x, y).terms()) == 29
    assert sp.expand(pxy.subs({x: -x, y: -y}, simultaneous=True) - pxy) == 0
    assert sp.expand(pxy_minus - y**10 * pxy.subs(y, 1 / y)) == 0

    f_xr = radial_polynomial(pxy, 6)
    f_minus = radial_polynomial(pxy_minus, 4)
    assert sp.expand(
        f_minus - r**10 * X**6 * f_xr.subs(r, 1 / (X * r))
    ) == 0
    assert sp.factor(f_minus.subs(r, 0) - (X**2 + 34 * X - 31)) == 0
    assert sp.discriminant(X**2 + 34 * X - 31, X) == 2**8 * 5

    c8 = sp.cancel(-U**6 * f_xr.subs({X: U * V, r: 1 / U}))
    assert sp.denom(c8) == 1
    c8 = primitive_integer(c8, (U, V))
    assert sp.Poly(c8, U, V).coeff_monomial(U**6) == 16
    assert (sp.degree(c8, U), sp.degree(c8, V), sp.Poly(c8, U, V).total_degree()) == (
        6,
        6,
        8,
    )
    assert len(sp.Poly(c8, U, V).terms()) == 29
    assert sp.Poly(c8, U, V).is_irreducible
    assert sp.expand(pxy + y**6 * c8.subs({U: x / y, V: x * y})) == 0

    # The two physical square branches share UV=x^2.  Their third characters
    # differ by the sign of the original K square.
    substitutions = {
        x: (S - 1) / (S + 1),
        y: (K - 1) / (K + 1),
        U: ((S - 1) * (K + 1)) / ((S + 1) * (K - 1)),
        V: ((S - 1) * (K - 1)) / ((S + 1) * (K + 1)),
    }
    character_checks = {
        "UV": (U * V, (S - 1) ** 2 / (S + 1) ** 2),
        "1-UV": (1 - U * V, 4 * S / (S + 1) ** 2),
        "V/U": (V / U, (K - 1) ** 2 / (K + 1) ** 2),
        "1-V/U": (1 - V / U, 4 * K / (K + 1) ** 2),
        "1-U/V": (1 - U / V, -4 * K / (K - 1) ** 2),
    }
    for left, right in character_checks.values():
        assert sp.factor(sp.cancel(left.subs(substitutions) - right)) == 0

    # All possible losses from the affine Cayley/fixed-field chart are
    # evaluated directly on the source curve.
    fibres = {
        "K=1": sp.factor(qbar.subs(K, 1)),
        "K=-1": sp.factor(qbar.subs(K, -1)),
        "K=0": sp.factor(qbar.subs(K, 0)),
        "S=1": sp.factor(qbar.subs(S, 1)),
        "S=0": sp.factor(qbar.subs(S, 0)),
        "S=-1": sp.factor(qbar.subs(S, -1)),
    }
    expected_fibres = {
        "K=1": 64 * (S - 1) ** 6 * (S + 1) ** 2,
        "K=-1": -16
        * (S - 1) ** 4
        * (S**4 - 32 * S**3 - 62 * S**2 - 32 * S + 1),
        "K=0": -S**4,
        "S=1": -(K - 1) ** 6 * (K + 1) ** 4,
        "S=0": K**3 * (K**2 + 6 * K + 1) ** 2,
        "S=-1": -(K - 1) ** 10,
    }
    assert all(sp.expand(fibres[name] - expected) == 0 for name, expected in expected_fibres.items())
    exceptional_quartic = S**4 - 32 * S**3 - 62 * S**2 - 32 * S + 1
    assert exceptional_quartic.subs(S, 1) == -124
    assert exceptional_quartic.subs(S, -1) == 4
    negative_fibres = {
        "K=1": sp.factor(qbar_minus.subs(K, 1)),
        "K=-1": sp.factor(qbar_minus.subs(K, -1)),
        "K=0": sp.factor(qbar_minus.subs(K, 0)),
        "S=1": sp.factor(qbar_minus.subs(S, 1)),
        "S=0": sp.factor(qbar_minus.subs(S, 0)),
        "S=-1": sp.factor(qbar_minus.subs(S, -1)),
    }
    expected_negative_fibres = {
        "K=1": 16 * (S - 1) ** 4 * exceptional_quartic,
        "K=-1": -64 * (S - 1) ** 6 * (S + 1) ** 2,
        "K=0": S**4,
        "S=1": (K + 1) ** 6 * (K - 1) ** 4,
        "S=0": K**3 * (K**2 - 6 * K + 1) ** 2,
        "S=-1": (K + 1) ** 10,
    }
    assert all(
        sp.expand(negative_fibres[name] - expected) == 0
        for name, expected in expected_negative_fibres.items()
    )

    payload: dict[str, object] = {
        "schema": 1,
        "status": "MACHINE-VERIFIED",
        "source": "both 71-term compact signed-square models Q_+(z,k), Q_-(z,k)",
        "source_checksum": source["sha256_without_checksum"],
        "source_relabeling": "S=z^2, K=k^2",
        "involution": "(S,K)->(1/S,1/K)",
        "cayley_coordinates": {
            "x": "(S-1)/(S+1)",
            "y": "(K-1)/(K+1)",
            "action": "(x,y)->(-x,-y)",
            "fixed_generators": {"U": "x/y", "V": "x*y"},
        },
        "cayley_identity": (
            "Qbar((1+x)/(1-x),(1+y)/(1-y))="
            "-2^10*P(x,y)/((x-1)^8*(y-1)^10)"
        ),
        "P_terms": sparse(pxy, (x, y)),
        "radial_identity": "P(x,r*x)=x^6*F(x^2,r)",
        "F_terms": sparse(f_xr, (X, r)),
        "quotient_identity": "C8(U,V)=-U^6*F(U*V,1/U)",
        "C8_terms": sparse(c8, (U, V)),
        "C8_degrees_U_V_total": [6, 6, 8],
        "C8_term_count": 29,
        "C8_irreducible_over_QQ": True,
        "negative_branch": {
            "twist": "Qbar_-(S,K)=-Qbar_+(S,-K)",
            "cayley_identity": (
                "Qbar_-((1+x)/(1-x),(1+y)/(1-y))="
                "+2^10*P_-(x,y)/((x-1)^8*(y-1)^10)"
            ),
            "P_relation": "P_-(x,y)=y^10*P_+(x,1/y)",
            "radial_identity": "P_-(x,r_-*x)=x^4*F_-(x^2,r_-)",
            "F_terms": sparse(f_minus, (X, r)),
            "F_relation": "F_-(X,r)=r^10*X^6*F_+(X,1/(X*r))",
            "coordinate_relation": "r_+=1/(X*r_-)",
            "natural_quotient": "C8(V_-,U_-)=0 for U_-=1/r_-, V_-=X*r_-",
            "same_C8_map": "(U,V)=(V_-,U_-)",
            "lost_r_minus_zero_fibre": "F_-(X,0)=X^2+34*X-31",
            "lost_r_minus_zero_discriminant": "2^8*5",
            "lost_r_minus_zero_rational_points": [],
        },
        "characters": {
            "common": ["UV=x^2", "1-UV=4*S/(S+1)^2"],
            "positive_third": "1-V/U=4*K/(K+1)^2",
            "negative_third": "1-U/V=-4*K/(K-1)^2",
        },
        "chart_exception_fibres": {
            "positive": {name: str(value) for name, value in fibres.items()},
            "negative": {name: str(value) for name, value in negative_fibres.items()},
        },
        "chart_exception_proof": (
            "For physical S>0, S!=1.  On the positive branch K=1 forces "
            "S=+/-1 and K=-1 leaves the displayed quartic; on the negative "
            "branch these two roles are reversed.  The quartic is monic with "
            "constant one, so its possible rational roots are +/-1, neither "
            "a root.  K=0 and S=0 are boundary.  Thus every admissible "
            "rational datum reaches a finite affine quotient point."
        ),
        "logical_scope": (
            "This is an exact quotient and character reduction.  It does not "
            "classify C8(Q) or prove C010."
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    payload = verify()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print("reciprocal quotient C8: 29 terms, degree (6,6), total degree 8")
    print("fixed-field identities and every rational affine-chart exception: OK")
    print("wrote", args.output)


if __name__ == "__main__":
    main()
