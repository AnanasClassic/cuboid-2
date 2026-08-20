#!/usr/bin/env python3
"""Generate exact coefficient certificates for the Session 1 Lean transport.

The research JSON intentionally records only the public maps and the two
65-term inverse coefficients.  Lean needs the omitted multiplication-back
quotients as explicit data.  This generator reconstructs them over ``ZZ``
from the checked source formulas and writes a deterministic JSON payload.

Run from the repository root with SymPy 1.14:

    python research/lean_generation/session1_transport/generate_transport_certificates.py

No numerical or probabilistic calculation is used.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import sympy as sp

from research.arithmetic_geometry.low_degree_transport import (
    E,
    U,
    V,
    exact_division,
    f1,
    f2,
    f3,
    load_c8,
    primitive,
    x,
    y,
)
from research.compact_signed_square.compact_signed_square import (
    compact_equations,
    compact_model,
    expected_lift,
    phi32,
)


ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT / "research" / "arithmetic_geometry" / "low_degree_transport.json"
OUTPUT = Path(__file__).with_name("transport_certificates.json")
LEAN_OUTPUT = (
    ROOT
    / "lean"
    / "Cuboid2"
    / "QuadraticReduction"
    / "TransportCertificateData.lean"
)


def sparse(poly: sp.Expr, variables: tuple[sp.Symbol, ...]) -> list[dict[str, object]]:
    """Return a deterministic sparse integer representation."""

    item = sp.Poly(sp.expand(poly), *variables, domain=sp.ZZ)
    return [
        {"powers": list(powers), "coefficient": str(coefficient)}
        for powers, coefficient in item.terms()
    ]


def load_sparse(
    records: list[dict[str, object]], variables: tuple[sp.Symbol, ...]
) -> sp.Expr:
    """Load the sparse representation emitted by the research scripts."""

    return sp.Poly.from_dict(
        {
            tuple(int(power) for power in record["powers"]): sp.Integer(
                record["coefficient"]
            )
            for record in records
        },
        variables,
        domain=sp.ZZ,
    ).as_expr()


def quotient_inverse_payload() -> dict[str, object]:
    """Reconstruct R5, E6, and their exact C8 multiplication-back quotients."""

    source = json.loads(SOURCE.read_text(encoding="utf-8"))
    inverse = source["inverse_subresultant"]
    A = load_sparse(inverse["A_terms"], (U, V))
    B = load_sparse(inverse["B_terms"], (U, V))
    c8, _ = load_c8()

    g_u = sp.expand(f1 - 2 * U * f3)
    g_v = sp.expand(f2 - V * f3)
    g_u_poly = sp.Poly(g_u, y)
    g_v_poly = sp.Poly(g_v, y)
    a1 = g_u_poly.coeff_monomial(y)
    b1 = g_u_poly.coeff_monomial(1)
    a2 = g_v_poly.coeff_monomial(y)
    b2 = g_v_poly.coeff_monomial(1)

    projection = sp.expand(a1 * b2 - a2 * b1)
    r5 = primitive(
        exact_division(
            projection,
            (x - 2) * (576 * x - 352225),
            (x, U, V),
        ),
        (x, U, V),
    )
    curve_after_y = sp.expand(b1**2 - a1**2 * (x**3 - 5 * x + 4))
    e6 = primitive(
        exact_division(
            curve_after_y,
            (576 * x - 352225) * (x**2 - 5),
            (x, U),
        ),
        (x, U),
    )

    r5_back = sp.prem(r5, A * x + B, x)
    e6_back = sp.prem(e6, A * x + B, x)
    r5_quotient, r5_remainder = sp.div(
        sp.Poly(r5_back, U, V), sp.Poly(c8, U, V)
    )
    e6_quotient, e6_remainder = sp.div(
        sp.Poly(e6_back, U, V), sp.Poly(c8, U, V)
    )
    assert r5_remainder.is_zero
    assert e6_remainder.is_zero

    # For a linear divisor ``A*x+B``, SymPy's pseudo-remainder is the
    # homogeneous evaluation ``A^degree * p(-B/A)``.  Lean checks that
    # convention independently from the sparse R5/E6 and A/B data; expanding
    # it here would duplicate the most expensive part of the kernel check.

    return {
        "C8_terms": sparse(c8, (U, V)),
        "A_terms": sparse(A, (U, V)),
        "B_terms": sparse(B, (U, V)),
        "R5_terms": sparse(r5, (x, U, V)),
        "E6_terms": sparse(e6, (x, U, V)),
        "R5_back_terms": sparse(r5_back, (U, V)),
        "E6_back_terms": sparse(e6_back, (U, V)),
        "R5_back_quotient_terms": sparse(r5_quotient.as_expr(), (U, V)),
        "E6_back_quotient_terms": sparse(e6_quotient.as_expr(), (U, V)),
        "term_counts": {
            "A": len(sp.Poly(A, U, V).terms()),
            "B": len(sp.Poly(B, U, V).terms()),
            "R5": len(sp.Poly(r5, x, U, V).terms()),
            "E6": len(sp.Poly(e6, x, U, V).terms()),
            "R5_back": len(sp.Poly(r5_back, U, V).terms()),
            "E6_back": len(sp.Poly(e6_back, U, V).terms()),
            "R5_back_quotient": len(r5_quotient.terms()),
            "E6_back_quotient": len(e6_quotient.terms()),
        },
    }


def compact_inverse_payload() -> dict[str, object]:
    """Emit the two exact reverse-lift quotients for both physical signs."""

    records: dict[str, object] = {}
    z, k, y = sp.symbols("z k y")
    for epsilon, label in ((1, "positive"), (-1, "negative")):
        f_1, f_0 = compact_equations(epsilon)
        q_model, _ = compact_model(epsilon)
        l1, l0, ell = expected_lift(epsilon)
        quotients: dict[str, object] = {}
        for name, equation, degree in (("F1", f_1, 4), ("F0", f_0, 3)):
            cleared = sp.together(
                l1**degree * equation.subs(y, -l0 / l1)
            ).as_numer_denom()[0]
            quotient, remainder = sp.div(
                sp.Poly(sp.expand(cleared), z, k),
                sp.Poly(q_model, z, k),
            )
            assert remainder.is_zero
            quotients[name] = {
                "clearing_power": degree,
                "cleared_terms": sparse(cleared, (z, k)),
                "quotient_terms": sparse(quotient.as_expr(), (z, k)),
            }
        records[label] = {
            "epsilon": epsilon,
            "Q_terms": sparse(q_model, (z, k)),
            "ell_terms": sparse(ell, (z, k)),
            "quotients": quotients,
        }

    return {
        "signs": records,
        "Phi32_terms": sparse(phi32(), (z,)),
    }


def verify() -> dict[str, object]:
    """Build the complete deterministic payload and attach its checksum."""

    payload: dict[str, object] = {
        "schema": 1,
        "status": "EXACT-INTEGER-CERTIFICATES",
        "source_transport_checksum": json.loads(SOURCE.read_text(encoding="utf-8"))[
            "sha256_without_checksum"
        ],
        "quotient_inverse": quotient_inverse_payload(),
        "compact_inverse": compact_inverse_payload(),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def lean_integer(value: int) -> str:
    """Render an integer as an unambiguous Lean rational coefficient."""

    return str(value) if value >= 0 else f"({value})"


def lean_horner(
    records: list[dict[str, object]], variables: tuple[str, ...]
) -> str:
    """Render sparse records as a nested Horner expression."""

    coefficients = {
        tuple(int(power) for power in record["powers"]): int(record["coefficient"])
        for record in records
    }

    def render(table: dict[tuple[int, ...], int], names: tuple[str, ...]) -> str:
        if not names:
            return lean_integer(table.get((), 0))
        maximum = max((powers[0] for powers in table), default=0)
        grouped: dict[int, dict[tuple[int, ...], int]] = {}
        for powers, coefficient in table.items():
            grouped.setdefault(powers[0], {})[powers[1:]] = coefficient
        expression = render(grouped.get(maximum, {}), names[1:])
        previous = maximum
        for exponent in range(maximum - 1, -1, -1):
            gap = previous - exponent
            expression = f"({expression}) * {names[0]} ^ {gap}"
            coefficient = render(grouped.get(exponent, {}), names[1:])
            if coefficient != "0":
                expression = f"{expression} + ({coefficient})"
            previous = exponent
        return expression

    return render(coefficients, variables)


def lean_sparse_list(records: list[dict[str, object]]) -> str:
    """Render sparse records as a list of exponent tuples and coefficients."""

    entries = []
    for record in records:
        fields = [
            *(str(int(power)) for power in record["powers"]),
            lean_integer(int(record["coefficient"])),
        ]
        entries.append(f"({', '.join(fields)})")
    return "[" + ", ".join(entries) + "]"


def lean_chunked_sparse_list(
    records: list[dict[str, object]], chunk_size: int = 220
) -> str:
    """Render a large list as a shallow concatenation of bounded chunks."""

    chunks = [
        lean_sparse_list(records[index : index + chunk_size])
        for index in range(0, len(records), chunk_size)
    ]
    return " ++\n    ".join(chunks)


def lean_sparse_string(records: list[dict[str, object]]) -> str:
    """Encode sparse records compactly for Lean's executable parser."""

    return ";".join(
        ",".join(
            [
                *(str(int(power)) for power in record["powers"]),
                str(int(record["coefficient"])),
            ]
        )
        for record in records
    )


def write_lean_data(payload: dict[str, object]) -> None:
    """Write the generated rational-polynomial definitions used by Lean."""

    inverse = payload["quotient_inverse"]
    definitions = [
        (
            "quotientInverseACertificateTerms",
            "TransportUVTerm",
            inverse["A_terms"],
            "The 65-term coefficient A of the inverse linear subresultant.",
        ),
        (
            "quotientInverseBCertificateTerms",
            "TransportUVTerm",
            inverse["B_terms"],
            "The 65-term constant B of the inverse linear subresultant.",
        ),
        (
            "quotientInverseR5CertificateTerms",
            "TransportXUVTerm",
            inverse["R5_terms"],
            "The degree-five projection polynomial R5.",
        ),
        (
            "quotientInverseE6CertificateTerms",
            "TransportXUVTerm",
            inverse["E6_terms"],
            "The degree-six elliptic-substitution polynomial E6.",
        ),
        (
            "quotientInverseR5BackCertificateTerms",
            "TransportUVTerm",
            inverse["R5_back_terms"],
            "Expanded pseudo-remainder of R5 by A*x+B.",
        ),
        (
            "quotientInverseE6BackCertificateTerms",
            "TransportUVTerm",
            inverse["E6_back_terms"],
            "Expanded pseudo-remainder of E6 by A*x+B.",
        ),
        (
            "quotientInverseR5BackQuotientTerms",
            "TransportUVTerm",
            inverse["R5_back_quotient_terms"],
            "Exact quotient R5Back/C8.",
        ),
        (
            "quotientInverseE6BackQuotientTerms",
            "TransportUVTerm",
            inverse["E6_back_quotient_terms"],
            "Exact quotient E6Back/C8.",
        ),
    ]

    lines = [
        "import Cuboid2.QuadraticReduction.TransportPolynomial",
        "",
        "/-!",
        "# Generated exact inverse-transport coefficient data",
        "",
        "Generated by",
        "`research/lean_generation/session1_transport/generate_transport_certificates.py`.",
        f"Certificate checksum: `{payload['sha256_without_checksum']}`.",
        "-/",
        "",
        "namespace Cuboid2",
        "",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 100000",
        "",
    ]
    for name, term_type, records, doc in definitions:
        parser = (
            "transportParseUVTerms"
            if term_type == "TransportUVTerm"
            else "transportParseXUVTerms"
        )
        lines.extend(
            [
                f"/-- {doc} -/",
                f"def {name} : List {term_type} :=",
                f'  {parser} "{lean_sparse_string(records)}"',
                "",
            ]
        )
    lines.extend(
        [
            "/-- Evaluation of the generated inverse coefficient `A`. -/",
            "def quotientInverseACertificate (U V : ℚ) : ℚ :=",
            "  transportEvalUVTerms quotientInverseACertificateTerms U V",
            "",
            "/-- Evaluation of the generated inverse coefficient `B`. -/",
            "def quotientInverseBCertificate (U V : ℚ) : ℚ :=",
            "  transportEvalUVTerms quotientInverseBCertificateTerms U V",
            "",
            "/-- Evaluation of the generated degree-five factor. -/",
            "def quotientInverseR5Certificate (x U V : ℚ) : ℚ :=",
            "  transportEvalXUVTerms quotientInverseR5CertificateTerms x U V",
            "",
            "/-- Evaluation of the generated degree-six factor. -/",
            "def quotientInverseE6Certificate (x U V : ℚ) : ℚ :=",
            "  transportEvalXUVTerms quotientInverseE6CertificateTerms x U V",
            "",
            "/-- Evaluation of the generated degree-five C8 quotient. -/",
            "def quotientInverseR5BackQuotient (U V : ℚ) : ℚ :=",
            "  transportEvalUVTerms quotientInverseR5BackQuotientTerms U V",
            "",
            "/-- Evaluation of the generated degree-six C8 quotient. -/",
            "def quotientInverseE6BackQuotient (U V : ℚ) : ℚ :=",
            "  transportEvalUVTerms quotientInverseE6BackQuotientTerms U V",
            "",
        ]
    )
    lines.extend(["end Cuboid2", ""])
    LEAN_OUTPUT.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    """Write the exact Session 1 certificate payload."""

    payload = verify()
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    write_lean_data(payload)
    print("wrote", OUTPUT)
    print("wrote", LEAN_OUTPUT)
    print("checksum", payload["sha256_without_checksum"])
    print("inverse counts", payload["quotient_inverse"]["term_counts"])


if __name__ == "__main__":
    main()
