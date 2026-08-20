#!/usr/bin/env python3
"""Generate the exact fixed-curve Cantor trace used by the Lean checker.

The implementation deliberately uses only :mod:`fractions` and a small,
independent univariate-polynomial kernel.  It computes ``11D`` on

    R^2 = 4*a^5 - 8*a^2 + 5*a,   D = (a - 1, 1)

with the addition chain ``D, 2D, 4D, 8D, 10D, 11D``.  Besides every reduced
pair, the output contains the Bézout, composition, quotient, and reduction
witnesses consumed by ``Cuboid2.DPlus.Cantor``.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from typing import Iterable


Polynomial = tuple[Fraction, ...]
Pair = tuple[Polynomial, Polynomial]


def trim(values: Iterable[Fraction]) -> Polynomial:
    """Return the canonical low-to-high coefficient tuple."""

    result = list(values)
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return tuple(result) if result else (Fraction(0),)


ZERO: Polynomial = (Fraction(0),)
ONE: Polynomial = (Fraction(1),)


def add(left: Polynomial, right: Polynomial) -> Polynomial:
    """Add two canonical polynomials."""

    size = max(len(left), len(right))
    return trim(
        (left[index] if index < len(left) else 0)
        + (right[index] if index < len(right) else 0)
        for index in range(size)
    )


def neg(value: Polynomial) -> Polynomial:
    """Negate a canonical polynomial."""

    return trim(-coefficient for coefficient in value)


def sub(left: Polynomial, right: Polynomial) -> Polynomial:
    """Subtract two canonical polynomials."""

    return add(left, neg(right))


def scale(scalar: Fraction, value: Polynomial) -> Polynomial:
    """Scale a canonical polynomial."""

    return trim(scalar * coefficient for coefficient in value)


def mul(left: Polynomial, right: Polynomial) -> Polynomial:
    """Multiply two canonical polynomials."""

    result = [Fraction(0)] * (len(left) + len(right) - 1)
    for left_index, left_value in enumerate(left):
        for right_index, right_value in enumerate(right):
            result[left_index + right_index] += left_value * right_value
    return trim(result)


def divmod_poly(
    dividend: Polynomial, divisor: Polynomial
) -> tuple[Polynomial, Polynomial]:
    """Perform exact Euclidean division over the rationals."""

    if divisor == ZERO:
        raise ZeroDivisionError("polynomial division by zero")
    work = list(dividend)
    quotient = [Fraction(0)] * max(1, len(dividend) - len(divisor) + 1)
    while len(work) >= len(divisor) and trim(work) != ZERO:
        coefficient = work[-1] / divisor[-1]
        shift = len(work) - len(divisor)
        quotient[shift] += coefficient
        for index, divisor_value in enumerate(divisor):
            work[index + shift] -= coefficient * divisor_value
        work = list(trim(work))
    return trim(quotient), trim(work)


def exact_quotient(dividend: Polynomial, divisor: Polynomial) -> Polynomial:
    """Divide and fail closed unless the remainder vanishes."""

    quotient, remainder = divmod_poly(dividend, divisor)
    if remainder != ZERO:
        raise ArithmeticError("claimed exact polynomial quotient has a remainder")
    return quotient


def monic(value: Polynomial) -> Polynomial:
    """Normalize a nonzero polynomial to leading coefficient one."""

    if value == ZERO:
        raise ArithmeticError("the zero polynomial cannot be made monic")
    return scale(1 / value[-1], value)


def xgcd(
    first: Polynomial, second: Polynomial
) -> tuple[Polynomial, Polynomial, Polynomial]:
    """Return monic ``g,s,t`` with ``g=s*first+t*second``."""

    old_r, current_r = first, second
    old_s, current_s = ONE, ZERO
    old_t, current_t = ZERO, ONE
    while current_r != ZERO:
        quotient, remainder = divmod_poly(old_r, current_r)
        old_r, current_r = current_r, remainder
        old_s, current_s = current_s, sub(old_s, mul(quotient, current_s))
        old_t, current_t = current_t, sub(old_t, mul(quotient, current_t))
    factor = 1 / old_r[-1]
    return scale(factor, old_r), scale(factor, old_s), scale(factor, old_t)


def xgcd_three(
    first: Polynomial, second: Polynomial, third: Polynomial
) -> tuple[Polynomial, Polynomial, Polynomial, Polynomial]:
    """Return monic ``g,s1,s2,s3`` for a three-polynomial Bézout identity."""

    first_gcd, first_s, second_s = xgcd(first, second)
    gcd, gcd_s, third_s = xgcd(first_gcd, third)
    return (
        gcd,
        mul(gcd_s, first_s),
        mul(gcd_s, second_s),
        third_s,
    )


def polynomial_power(value: Polynomial, exponent: int) -> Polynomial:
    """Raise a polynomial to a nonnegative integer power."""

    result = ONE
    for _ in range(exponent):
        result = mul(result, value)
    return result


def curve_remainder(pair: Pair, curve: Polynomial) -> Polynomial:
    """Return the remainder of ``f-v^2`` modulo ``u``."""

    u, v = pair
    return divmod_poly(sub(curve, mul(v, v)), u)[1]


def validate_pair(pair: Pair, curve: Polynomial, *, reduced: bool) -> None:
    """Check the exact curve, monicity, and degree contracts for a pair."""

    u, v = pair
    if u == ZERO or u[-1] != 1:
        raise ArithmeticError("Mumford u must be nonzero and monic")
    if len(v) >= len(u) and v != ZERO:
        raise ArithmeticError("Mumford v is not reduced modulo u")
    if reduced and len(u) - 1 > 2:
        raise ArithmeticError("Mumford pair is not genus-two reduced")
    if curve_remainder(pair, curve) != ZERO:
        raise ArithmeticError("Mumford pair fails the curve relation")


@dataclass(frozen=True)
class Composition:
    """An exact generalized Cantor-composition witness."""

    first: Pair
    second: Pair
    output: Pair
    gcd: Polynomial
    bezout_first: Polynomial
    bezout_second: Polynomial
    bezout_sum_v: Polynomial
    v_quotient: Polynomial


@dataclass(frozen=True)
class Reduction:
    """An exact genus-two reduction witness."""

    input: Pair
    output: Pair
    curve_scale: Fraction
    v_quotient: Polynomial


@dataclass(frozen=True)
class Addition:
    """One Cantor addition, including all required reduction steps."""

    name: str
    left_name: str
    right_name: str
    composition: Composition
    reductions: tuple[Reduction, ...]
    output: Pair


def cantor_add(
    first: Pair, second: Pair, curve: Polynomial
) -> tuple[Pair, Composition, tuple[Reduction, ...]]:
    """Add two reduced pairs and return every exact witness."""

    validate_pair(first, curve, reduced=True)
    validate_pair(second, curve, reduced=True)
    u1, v1 = first
    u2, v2 = second
    gcd, s1, s2, s3 = xgcd_three(u1, u2, add(v1, v2))
    if gcd != ONE:
        raise ArithmeticError(
            "the specialized Lean certificate requires coprime d=1 composition"
        )
    u_product = exact_quotient(mul(u1, u2), mul(gcd, gcd))
    u_composed = monic(u_product)
    if u_composed != u_product:
        raise ArithmeticError("monic inputs unexpectedly produced nonmonic composition")
    numerator = add(
        add(mul(mul(s1, u1), v2), mul(mul(s2, u2), v1)),
        mul(s3, add(mul(v1, v2), curve)),
    )
    divided_v = exact_quotient(numerator, gcd)
    v_quotient, v_composed = divmod_poly(divided_v, u_composed)
    composed = (u_composed, v_composed)
    validate_pair(composed, curve, reduced=False)
    composition = Composition(
        first=first,
        second=second,
        output=composed,
        gcd=gcd,
        bezout_first=s1,
        bezout_second=s2,
        bezout_sum_v=s3,
        v_quotient=v_quotient,
    )

    reductions: list[Reduction] = []
    current = composed
    while len(current[0]) - 1 > 2:
        current_u, current_v = current
        raw_next_u = exact_quotient(
            sub(curve, mul(current_v, current_v)), current_u
        )
        curve_scale = raw_next_u[-1]
        next_u = monic(raw_next_u)
        next_v_quotient, next_v = divmod_poly(neg(current_v), next_u)
        following = (next_u, next_v)
        validate_pair(following, curve, reduced=False)
        reductions.append(
            Reduction(
                input=current,
                output=following,
                curve_scale=curve_scale,
                v_quotient=next_v_quotient,
            )
        )
        current = following

    validate_pair(current, curve, reduced=True)
    return current, composition, tuple(reductions)


def encode_fraction(value: Fraction) -> str:
    """Encode a rational in a stable Lean-friendly form."""

    return (
        str(value.numerator)
        if value.denominator == 1
        else f"{value.numerator}/{value.denominator}"
    )


def encode_polynomial(value: Polynomial) -> list[str]:
    """Encode low-to-high rational coefficients."""

    return [encode_fraction(coefficient) for coefficient in value]


def encode_pair(
    value: Pair, curve: Polynomial | None = None
) -> dict[str, object]:
    """Encode a Mumford pair and, when requested, its exact curve quotient."""

    answer: dict[str, object] = {
        "u": encode_polynomial(value[0]),
        "v": encode_polynomial(value[1]),
    }
    if curve is not None:
        answer["curve_quotient"] = encode_polynomial(
            exact_quotient(sub(curve, mul(value[1], value[1])), value[0])
        )
    return answer


def encode_composition(
    value: Composition, curve: Polynomial
) -> dict[str, object]:
    """Encode a composition certificate."""

    return {
        "first": encode_pair(value.first, curve),
        "second": encode_pair(value.second, curve),
        "output": encode_pair(value.output, curve),
        "gcd": encode_polynomial(value.gcd),
        "bezout_first": encode_polynomial(value.bezout_first),
        "bezout_second": encode_polynomial(value.bezout_second),
        "bezout_sum_v": encode_polynomial(value.bezout_sum_v),
        "v_quotient": encode_polynomial(value.v_quotient),
    }


def encode_reduction(value: Reduction, curve: Polynomial) -> dict[str, object]:
    """Encode a reduction certificate."""

    return {
        "input": encode_pair(value.input, curve),
        "output": encode_pair(value.output, curve),
        "curve_scale": encode_fraction(value.curve_scale),
        "v_quotient": encode_polynomial(value.v_quotient),
    }


def generate() -> dict[str, object]:
    """Compute and independently validate the five-step addition chain."""

    curve: Polynomial = (
        Fraction(0),
        Fraction(5),
        Fraction(-8),
        Fraction(0),
        Fraction(0),
        Fraction(4),
    )
    divisor: Pair = (
        (Fraction(-1), Fraction(1)),
        (Fraction(1),),
    )
    validate_pair(divisor, curve, reduced=True)
    pairs: dict[str, Pair] = {"D": divisor}
    additions: list[Addition] = []
    for name, left_name, right_name in (
        ("2D", "D", "D"),
        ("4D", "2D", "2D"),
        ("8D", "4D", "4D"),
        ("10D", "8D", "2D"),
        ("11D", "10D", "D"),
    ):
        output, composition, reductions = cantor_add(
            pairs[left_name], pairs[right_name], curve
        )
        pairs[name] = output
        if (name == "2D" and reductions) or (
            name != "2D" and len(reductions) != 1
        ):
            raise ArithmeticError(
                "unexpected reduction count for the fixed addition chain"
            )
        additions.append(
            Addition(
                name=name,
                left_name=left_name,
                right_name=right_name,
                composition=composition,
                reductions=reductions,
                output=output,
            )
        )

    payload: dict[str, object] = {
        "schema": 1,
        "curve": encode_polynomial(curve),
        "coordinate": "R",
        "addition_chain": [
            {
                "name": addition.name,
                "left": addition.left_name,
                "right": addition.right_name,
                "composition": encode_composition(addition.composition, curve),
                "reductions": [
                    encode_reduction(reduction, curve)
                    for reduction in addition.reductions
                ],
                "output": encode_pair(addition.output, curve),
            }
            for addition in additions
        ],
        "final": encode_pair(pairs["11D"], curve),
    }
    canonical = json.dumps(
        payload, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def lean_rational(value: str) -> str:
    """Render one encoded rational as an explicitly typed Lean term."""

    rational = Fraction(value)
    if rational.denominator == 1:
        return f"({rational.numerator} : ℚ)"
    return (
        f"({rational.numerator} / {rational.denominator} : ℚ)"
    )


def lean_polynomial(coefficients: list[str]) -> str:
    """Render low-to-high coefficients in a compact Horner form."""

    result = f"C {lean_rational(coefficients[-1])}"
    for coefficient in reversed(coefficients[:-1]):
        result = f"C {lean_rational(coefficient)} + X * ({result})"
    return result


def lean_pair_definition(name: str, encoded: dict[str, object]) -> str:
    """Render one raw pair, its curve quotient, and its admissible bundle."""

    raw_name = f"dplusCantor{name}"
    quotient = encoded["curve_quotient"]
    assert isinstance(quotient, list)
    u = encoded["u"]
    v = encoded["v"]
    assert isinstance(u, list) and isinstance(v, list)
    return f"""
private def {raw_name} : MumfordPair ℚ where
  u := {lean_polynomial(u)}
  v := {lean_polynomial(v)}

private theorem {raw_name}_admissible :
    DPlusCantorAdmissible {raw_name} := by
  refine ⟨{lean_polynomial(quotient)}, ?_⟩
  apply Polynomial.funext
  intro x
  simp [{raw_name}, dplusPolynomial]
  ring

private def {raw_name}Pair : DPlusCantorPair :=
  ⟨{raw_name}, {raw_name}_admissible⟩
"""


def lean_polynomial_certificate(
    definitions: list[str],
) -> str:
    """Render the standard kernel proof used for every exact identity."""

    unfolded = ", ".join([*definitions, "dplusPolynomial"])
    return f"""by
    apply Polynomial.funext
    intro x
    simp [{unfolded}]
    ring"""


def generate_lean(payload: dict[str, object]) -> str:
    """Render the complete Lean trace from the canonical JSON payload."""

    additions = payload["addition_chain"]
    assert isinstance(additions, list)
    names = {
        "D": "dplusGeneratorCantorPair",
        "2D": "dplusCantorTwoDPair",
        "4D": "dplusCantorFourDPair",
        "8D": "dplusCantorEightDPair",
        "10D": "dplusCantorTenDPair",
        "11D": "dplusElevenDCantorPair",
    }
    raw_names = {
        "D": "dplusGeneratorD",
        "2D": "dplusCantorTwoD",
        "4D": "dplusCantorFourD",
        "8D": "dplusCantorEightD",
        "10D": "dplusCantorTenD",
        "11D": "dplusElevenD",
    }
    word_names = {
        "2D": "TwoD",
        "4D": "FourD",
        "8D": "EightD",
        "10D": "TenD",
        "11D": "ElevenD",
    }
    rendered = [
        """import Cuboid2.DPlus.CantorSemantics
import Cuboid2.DPlus.GlobalMumfordCertificate

/-!
# Generated exact Cantor trace for `11D`

This file is generated by
`research/lean_generation/session1_cantor/generate_dplus_cantor.py`.
Every displayed rational polynomial identity is rechecked by the Lean
kernel.  Raw Mumford pairs carry no addition instance.
-/

namespace Cuboid2

open Polynomial

noncomputable section

set_option linter.unusedSimpArgs false

def dplusGeneratorCantorPair : DPlusCantorPair :=
  ⟨dplusGeneratorD,
    DPlusCantorAdmissible.ofValid dplusGeneratorD_valid⟩

def dplusElevenDCantorPair : DPlusCantorPair :=
  ⟨dplusElevenD,
    DPlusCantorAdmissible.ofValid dplusElevenD_valid⟩
"""
    ]

    # Render every intermediate reduced and semireduced pair once.
    for addition in additions:
        assert isinstance(addition, dict)
        name = str(addition["name"])
        composition = addition["composition"]
        assert isinstance(composition, dict)
        composed = composition["output"]
        assert isinstance(composed, dict)
        if name == "2D":
            rendered.append(lean_pair_definition("TwoD", composed))
        elif name != "11D":
            stem = f"{word_names[name]}Composed"
            rendered.append(lean_pair_definition(stem, composed))
            output = addition["output"]
            assert isinstance(output, dict)
            rendered.append(
                lean_pair_definition(word_names[name], output)
            )
        else:
            rendered.append(
                lean_pair_definition("ElevenDComposed", composed)
            )

    composition_names = word_names
    composed_pairs = {
        "2D": "dplusCantorTwoDPair",
        "4D": "dplusCantorFourDComposedPair",
        "8D": "dplusCantorEightDComposedPair",
        "10D": "dplusCantorTenDComposedPair",
        "11D": "dplusCantorElevenDComposedPair",
    }
    composed_raws = {
        "2D": "dplusCantorTwoD",
        "4D": "dplusCantorFourDComposed",
        "8D": "dplusCantorEightDComposed",
        "10D": "dplusCantorTenDComposed",
        "11D": "dplusCantorElevenDComposed",
    }

    for addition in additions:
        assert isinstance(addition, dict)
        name = str(addition["name"])
        left = str(addition["left"])
        right = str(addition["right"])
        composition = addition["composition"]
        assert isinstance(composition, dict)
        definitions = [
            names[left],
            names[right],
            composed_pairs[name],
            raw_names[left],
            raw_names[right],
            composed_raws[name],
        ]
        rendered.append(
            f"""
private def dplusCantorCompose{composition_names[name]} :
    DPlusCantorComposition {names[left]} {names[right]}
      {composed_pairs[name]} where
  bezoutFirst := {lean_polynomial(composition["bezout_first"])}
  bezoutSecond := {lean_polynomial(composition["bezout_second"])}
  bezoutSumV := {lean_polynomial(composition["bezout_sum_v"])}
  vQuotient := {lean_polynomial(composition["v_quotient"])}
  bezout_identity := {lean_polynomial_certificate(definitions)}
  u_identity := {lean_polynomial_certificate(definitions)}
  v_identity := {lean_polynomial_certificate(definitions)}
"""
        )
        reductions = addition["reductions"]
        assert isinstance(reductions, list)
        if reductions:
            reduction = reductions[0]
            assert isinstance(reduction, dict)
            output_pair = names[name]
            definitions = [
                composed_pairs[name],
                output_pair,
                composed_raws[name],
                raw_names[name],
            ]
            if name == "11D":
                definitions.extend(
                    [
                        "dplusElevenDRaw",
                        "FiniteMumford.toMumfordPair",
                        "FiniteMumford.u",
                        "FiniteMumford.v",
                        "dplusElevenDU1",
                        "dplusElevenDU0",
                        "dplusElevenDV1",
                        "dplusElevenDV0",
                    ]
                )
            rendered.append(
                f"""
private def dplusCantorReduce{composition_names[name]} :
    DPlusCantorReduction {composed_pairs[name]} {output_pair} where
  curveScale := {lean_rational(str(reduction["curve_scale"]))}
  curveScale_ne_zero := by norm_num
  vQuotient := {lean_polynomial(reduction["v_quotient"])}
  curve_identity := {lean_polynomial_certificate(definitions)}
  v_identity := {lean_polynomial_certificate(definitions)}
"""
            )

    rendered.append(
        """
private theorem dplusCantorTwoD_class :
    dplusCantorClass dplusCantorTwoDPair =
      2 • dplusCantorClass dplusGeneratorCantorPair := by
  rw [dplusCantorClass_compose dplusCantorComposeTwoD]
  simp [two_nsmul]

private theorem dplusCantorFourD_class :
    dplusCantorClass dplusCantorFourDPair =
      4 • dplusCantorClass dplusGeneratorCantorPair := by
  rw [dplusCantorClass_reduce dplusCantorReduceFourD,
    dplusCantorClass_compose dplusCantorComposeFourD,
    dplusCantorTwoD_class]
  module

private theorem dplusCantorEightD_class :
    dplusCantorClass dplusCantorEightDPair =
      8 • dplusCantorClass dplusGeneratorCantorPair := by
  rw [dplusCantorClass_reduce dplusCantorReduceEightD,
    dplusCantorClass_compose dplusCantorComposeEightD,
    dplusCantorFourD_class]
  module

private theorem dplusCantorTenD_class :
    dplusCantorClass dplusCantorTenDPair =
      10 • dplusCantorClass dplusGeneratorCantorPair := by
  rw [dplusCantorClass_reduce dplusCantorReduceTenD,
    dplusCantorClass_compose dplusCantorComposeTenD,
    dplusCantorEightD_class, dplusCantorTwoD_class]
  module

/--
The stored checked rational Mumford pair represents eleven times
`D=[(1,1)-∞]` in the fixed-curve Cantor presentation.
-/
theorem dplusCantorClass_eleven_generator :
    dplusCantorClass dplusElevenDCantorPair =
      11 • dplusCantorClass dplusGeneratorCantorPair := by
  rw [dplusCantorClass_reduce dplusCantorReduceElevenD,
    dplusCantorClass_compose dplusCantorComposeElevenD,
    dplusCantorTenD_class]
  module

/-- Public semantic-equivalence spelling of the exact `11D` certificate. -/
theorem dplusElevenD_is_eleven_generator :
    dplusCantorClass dplusElevenDCantorPair =
      11 • dplusCantorClass dplusGeneratorCantorPair :=
  dplusCantorClass_eleven_generator

end

end Cuboid2
"""
    )
    return "\n".join(rendered)


def main() -> None:
    """Write the canonical certificate or print it to standard output."""

    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--lean-output", type=Path)
    arguments = parser.parse_args()
    payload = generate()
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if arguments.output is None:
        print(encoded, end="")
    else:
        arguments.output.write_text(encoded, encoding="utf-8")
        print(f"wrote {arguments.output}")
    if arguments.lean_output is not None:
        arguments.lean_output.write_text(
            generate_lean(payload), encoding="utf-8"
        )
        print(f"wrote {arguments.lean_output}")
    print("D+ exact Cantor trace: PASS")


if __name__ == "__main__":
    main()
