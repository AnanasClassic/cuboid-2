import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]


def _polynomial(record, variables):
    return sum(
        sp.Integer(term["coefficient"])
        * sp.prod(variable**power for variable, power in zip(variables, term["powers"], strict=True))
        for term in record["terms"]
    )


def test_genus4_and_elliptic_plane_models_are_compatible():
    payload = json.loads((ROOT / "artifacts" / "genus4_quotient.json").read_text())
    X, A, q = sp.symbols("X A q")
    G = _polynomial(payload["genus4_model"], (X, A))
    H = _polynomial(payload["elliptic_plane_model"], (q, A))

    assert (sp.degree(G, X), sp.degree(G, A)) == (16, 10)
    assert (sp.degree(H, q), sp.degree(H, A)) == (8, 10)
    assert sp.expand(G - X**16 * G.subs(X, 1 / X)) == 0
    assert sp.expand(G - X**8 * H.subs(q, X + 1 / X)) == 0
    assert sp.factor(H.subs(q, -2)) == 2**16 * (A - 2) ** 10
    assert sp.factor(H.subs(q, 2)) == 2**27 * A**3 * (A - 6) * (A**2 - 12 * A + 4) ** 3


def test_nontrivial_elliptic_plane_point_and_failed_square_lift():
    payload = json.loads((ROOT / "artifacts" / "genus4_quotient.json").read_text())
    q, A = sp.symbols("q A")
    H = _polynomial(payload["elliptic_plane_model"], (q, A))

    assert H.subs({q: 6, A: sp.Rational(6, 7)}) == 0
    U = sp.Rational(2) * (q + 6) / (q - 2)
    assert U.subs(q, 6) == 6
    assert sp.sqrt(U.subs(q, 6) + 2).is_rational is False
