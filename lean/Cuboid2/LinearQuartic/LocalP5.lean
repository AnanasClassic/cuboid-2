import Cuboid2.LinearQuartic.FiniteCounts
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Exact local `p = 5` rows for the linear--quartic curve

This file kernel-checks the finite algebraic part of the local Chabauty
certificate.  The two coefficients `c₀,c₁` of the annihilating differential

`(c₀ + c₁ t) dt / (2w)`

are left as parameters.  The external Coleman computation is used only to
discover the two residue facts

`c₀ ≡ c₁ ≡ 1 (mod 5)` and `v₅(c₀-c₁)=1`;

it is not a premise of any polynomial identity below.

Every ``series'' in this file is an explicit polynomial.  Agreement through
an indicated order means divisibility of the difference by a power of `X`,
and is therefore checked by the Lean kernel.
-/

namespace Cuboid2

open Polynomial

noncomputable section

local instance linearQuarticLocalFactPrime5 : Fact (Nat.Prime 5) :=
  ⟨by norm_num⟩

/-- The derivative of the linear--quartic right-hand side. -/
def linearQuarticCurveDerivative {R : Type*} [CommRing R] (t : R) : R :=
  5 * t ^ 4 + 84 * t ^ 3 + 78 * t ^ 2 + 20 * t + 5

/-- Differentiating the curve polynomial gives the displayed formula. -/
theorem derivative_linearQuarticPolynomial
    {R : Type*} [CommRing R] :
    derivative (linearQuarticPolynomial : R[X]) =
      C 5 * X ^ 4 + C 84 * X ^ 3 + C 78 * X ^ 2 + C 20 * X + C 5 := by
  simp [linearQuarticPolynomial, derivative_add, derivative_mul,
    derivative_pow]
  simp only [Polynomial.C_ofNat]
  ring

/-- The reduction at `5` is squarefree: the curve equation and its
derivative have no common finite zero. -/
theorem linearQuartic_good_reduction_row
    (t : ZMod 5) :
    ¬(linearQuarticCurveRhs t = 0 ∧
      linearQuarticCurveDerivative t = 0) := by
  decide +revert

/-- Two polynomials have the same coefficients below degree `n`. -/
def AgreeBelow (n : ℕ) (p q : ℚ[X]) : Prop :=
  X ^ n ∣ p - q

/-- The `5`-adic residue-disc parameter `5X`. -/
def p5Parameter : ℚ[X] :=
  C 5 * X

/-- The local `t` coordinate in the residue disc centred at `a`. -/
def ordinaryLocalT (a : ℚ) : ℚ[X] :=
  C a + p5Parameter

/-- Positive branch above `t=0`, through order two in `t`. -/
def ordinaryWZeroPlus : ℚ[X] :=
  1 +
    C (5 / 2 : ℚ) * p5Parameter +
    C (15 / 8 : ℚ) * p5Parameter ^ 2

/-- Negative branch above `t=0`. -/
def ordinaryWZeroMinus : ℚ[X] :=
  -ordinaryWZeroPlus

/-- Positive branch above `t=1`, through order two in `t-1`. -/
def ordinaryWOnePlus : ℚ[X] :=
  8 + 12 * p5Parameter + 5 * p5Parameter ^ 2

/-- Negative branch above `t=1`. -/
def ordinaryWOneMinus : ℚ[X] :=
  -ordinaryWOnePlus

/-- Primitive of `(c₀+c₁t)dt/(2w)` in the disc of `(0,1)`. -/
def ordinaryPrimitiveZeroPlus (c₀ c₁ : ℚ) : ℚ[X] :=
  C (c₀ / 2) * p5Parameter +
    C (-5 * c₀ / 8 + c₁ / 4) * p5Parameter ^ 2 +
    C (35 * c₀ / 48 - 5 * c₁ / 12) * p5Parameter ^ 3

/-- Primitive in the disc of `(0,-1)`. -/
def ordinaryPrimitiveZeroMinus (c₀ c₁ : ℚ) : ℚ[X] :=
  -ordinaryPrimitiveZeroPlus c₀ c₁

/-- Primitive in the disc of `(1,8)`. -/
def ordinaryPrimitiveOnePlus (c₀ c₁ : ℚ) : ℚ[X] :=
  C ((c₀ + c₁) / 16) * p5Parameter +
    C (-3 * c₀ / 64 - c₁ / 64) * p5Parameter ^ 2 +
    C (13 * c₀ / 384 + c₁ / 384) * p5Parameter ^ 3

/-- Primitive in the disc of `(1,-8)`. -/
def ordinaryPrimitiveOneMinus (c₀ c₁ : ℚ) : ℚ[X] :=
  -ordinaryPrimitiveOnePlus c₀ c₁

/-- Exact quotient left after truncating the `(0,±1)` curve equation. -/
def ordinaryCurveRemainderZero : ℚ[X] :=
  C (-16625 / 8 : ℚ) +
    C (-699375 / 64 : ℚ) * X -
    3125 * X ^ 2

/-- Exact quotient left after truncating the `(1,±8)` curve equation. -/
def ordinaryCurveRemainderOne : ℚ[X] :=
  -625 * X - 3125 * X ^ 2

/-- Exact differential quotient in the `(0,±1)` discs. -/
def ordinaryDifferentialRemainderZero (c₀ c₁ : ℚ) : ℚ[X] :=
  C (15625 * c₀ / 4 - 21875 * c₁ / 8) +
    C (1640625 * c₀ / 64 - 234375 * c₁ / 16) * X

/-- Exact differential quotient in the `(1,±8)` discs. -/
def ordinaryDifferentialRemainderOne (c₀ c₁ : ℚ) : ℚ[X] :=
  C (1875 * c₀ / 2 - 625 * c₁ / 8) +
    C (203125 * c₀ / 64 + 15625 * c₁ / 64) * X

/-- The `(0,1)` branch satisfies the curve equation through degree two. -/
theorem ordinaryWZeroPlus_curve :
    AgreeBelow 3 (ordinaryWZeroPlus ^ 2)
      (linearQuarticCurveRhs (ordinaryLocalT 0)) := by
  unfold AgreeBelow
  refine ⟨ordinaryCurveRemainderZero, ?_⟩
  apply Polynomial.funext
  intro x
  simp [ordinaryCurveRemainderZero, ordinaryWZeroPlus, ordinaryLocalT,
    p5Parameter, linearQuarticCurveRhs]
  ring

/-- The `(0,-1)` branch satisfies the same curve equation. -/
theorem ordinaryWZeroMinus_curve :
    AgreeBelow 3 (ordinaryWZeroMinus ^ 2)
      (linearQuarticCurveRhs (ordinaryLocalT 0)) := by
  simpa [ordinaryWZeroMinus] using ordinaryWZeroPlus_curve

/-- The `(1,8)` branch satisfies the curve equation through degree two. -/
theorem ordinaryWOnePlus_curve :
    AgreeBelow 3 (ordinaryWOnePlus ^ 2)
      (linearQuarticCurveRhs (ordinaryLocalT 1)) := by
  unfold AgreeBelow
  refine ⟨ordinaryCurveRemainderOne, ?_⟩
  apply Polynomial.funext
  intro x
  simp [ordinaryCurveRemainderOne, ordinaryWOnePlus, ordinaryLocalT,
    p5Parameter, linearQuarticCurveRhs]
  ring

/-- The `(1,-8)` branch satisfies the same curve equation. -/
theorem ordinaryWOneMinus_curve :
    AgreeBelow 3 (ordinaryWOneMinus ^ 2)
      (linearQuarticCurveRhs (ordinaryLocalT 1)) := by
  simpa [ordinaryWOneMinus] using ordinaryWOnePlus_curve

/--
The displayed primitive in the `(0,1)` disc differentiates to the
annihilating differential through degree two.
-/
theorem ordinaryPrimitiveZeroPlus_certificate (c₀ c₁ : ℚ) :
    AgreeBelow 3
      (2 * ordinaryWZeroPlus *
        (ordinaryPrimitiveZeroPlus c₀ c₁).derivative)
      ((C c₀ + C c₁ * ordinaryLocalT 0) *
        (ordinaryLocalT 0).derivative) := by
  unfold AgreeBelow
  refine ⟨ordinaryDifferentialRemainderZero c₀ c₁, ?_⟩
  apply Polynomial.funext
  intro x
  simp [ordinaryDifferentialRemainderZero, ordinaryWZeroPlus,
    ordinaryPrimitiveZeroPlus, ordinaryLocalT, p5Parameter,
    derivative_mul, derivative_pow]
  ring

/-- The corresponding certificate in the `(0,-1)` disc. -/
theorem ordinaryPrimitiveZeroMinus_certificate (c₀ c₁ : ℚ) :
    AgreeBelow 3
      (2 * ordinaryWZeroMinus *
        (ordinaryPrimitiveZeroMinus c₀ c₁).derivative)
      ((C c₀ + C c₁ * ordinaryLocalT 0) *
        (ordinaryLocalT 0).derivative) := by
  simpa [ordinaryWZeroMinus, ordinaryPrimitiveZeroMinus] using
    ordinaryPrimitiveZeroPlus_certificate c₀ c₁

/-- The displayed primitive in the `(1,8)` disc differentiates to the
annihilating differential through degree two. -/
theorem ordinaryPrimitiveOnePlus_certificate (c₀ c₁ : ℚ) :
    AgreeBelow 3
      (2 * ordinaryWOnePlus *
        (ordinaryPrimitiveOnePlus c₀ c₁).derivative)
      ((C c₀ + C c₁ * ordinaryLocalT 1) *
        (ordinaryLocalT 1).derivative) := by
  unfold AgreeBelow
  refine ⟨ordinaryDifferentialRemainderOne c₀ c₁, ?_⟩
  apply Polynomial.funext
  intro x
  simp [ordinaryDifferentialRemainderOne, ordinaryWOnePlus,
    ordinaryPrimitiveOnePlus, ordinaryLocalT, p5Parameter,
    derivative_mul, derivative_pow]
  ring

/-- The corresponding certificate in the `(1,-8)` disc. -/
theorem ordinaryPrimitiveOneMinus_certificate (c₀ c₁ : ℚ) :
    AgreeBelow 3
      (2 * ordinaryWOneMinus *
        (ordinaryPrimitiveOneMinus c₀ c₁).derivative)
      ((C c₀ + C c₁ * ordinaryLocalT 1) *
        (ordinaryLocalT 1).derivative) := by
  simpa [ordinaryWOneMinus, ordinaryPrimitiveOneMinus] using
    ordinaryPrimitiveOnePlus_certificate c₀ c₁

/-- The four ordinary primitives have the expected linear coefficients. -/
theorem ordinaryPrimitive_linear_coefficients (c₀ c₁ : ℚ) :
    (ordinaryPrimitiveZeroPlus c₀ c₁).coeff 1 = 5 * c₀ / 2 ∧
    (ordinaryPrimitiveZeroMinus c₀ c₁).coeff 1 = -(5 * c₀ / 2) ∧
    (ordinaryPrimitiveOnePlus c₀ c₁).coeff 1 = 5 * (c₀ + c₁) / 16 ∧
    (ordinaryPrimitiveOneMinus c₀ c₁).coeff 1 =
      -(5 * (c₀ + c₁) / 16) := by
  have hcoeff (p : ℚ[X]) : p.coeff 1 = p.derivative.eval 0 := by
    rw [← coeff_zero_eq_eval_zero]
    simpa using (coeff_derivative p 0).symm
  constructor
  · rw [hcoeff]
    simp [ordinaryPrimitiveZeroPlus, p5Parameter,
      derivative_mul, derivative_pow]
    ring
  constructor
  · rw [hcoeff]
    simp [ordinaryPrimitiveZeroMinus, ordinaryPrimitiveZeroPlus, p5Parameter,
      derivative_mul, derivative_pow]
    ring
  constructor
  · rw [hcoeff]
    simp [ordinaryPrimitiveOnePlus, p5Parameter,
      derivative_mul, derivative_pow]
    ring
  · rw [hcoeff]
    simp [ordinaryPrimitiveOneMinus, ordinaryPrimitiveOnePlus, p5Parameter,
      derivative_mul, derivative_pow]
    ring

/-- Modulo `5`, the annihilator numerator `1+t` is nonzero at the four
ordinary points and vanishes only at the exceptional finite residue point. -/
theorem annihilatorNumerator_residue_rows :
    (1 + (0 : ZMod 5) ≠ 0) ∧
    (1 + (1 : ZMod 5) ≠ 0) ∧
    (1 + (4 : ZMod 5) = 0) := by
  decide

/-! ## The residue disc at infinity -/

/-- The unit series `g` in the infinity chart
`s = 1/t = r² g(r)`, with `r=t²/w`. -/
def infinityUnitSeries : ℚ[X] :=
  1 + 21 * p5Parameter ^ 2 + 467 * p5Parameter ^ 4

/-- The truncated reciprocal coordinate `s=r²g`. -/
def infinityS : ℚ[X] :=
  p5Parameter ^ 2 * infinityUnitSeries

/-- The reversed curve polynomial occurring in the infinity chart. -/
def infinityReversedRhs (s : ℚ[X]) : ℚ[X] :=
  1 + 21 * s + 26 * s ^ 2 + 10 * s ^ 3 + 5 * s ^ 4 + s ^ 5

/-- Exact quotient for the terms through degree four in the infinity chart. -/
def infinityCurveRemainder : ℚ[X] :=
  -170296875 -
    13964843750 * X ^ 2 -
    4980117187500 * X ^ 4 -
    1384354003906250 * X ^ 6

/-- The finite primitive row at infinity. -/
def infinityPrimitive (c₀ c₁ : ℚ) : ℚ[X] :=
  C (-c₁) * p5Parameter +
    C (-c₀ / 3 - 7 * c₁) * p5Parameter ^ 3 +
    C (-42 * c₀ / 5 - 493 * c₁ / 5) * p5Parameter ^ 5

/-- Exact quotient in the infinity differential row. -/
def infinityDifferentialRemainder (c₀ c₁ : ℚ) : ℚ[X] :=
  C (218906250 * c₀ - 3150000000 * c₁) +
    C (114925781250 * c₀ - 899339843750 * c₁) * X ^ 2 +
    C (63893261718750 * c₀) * X ^ 4

/-- The displayed `g` solves the truncated infinity-chart equation through
degree five. -/
theorem infinityUnitSeries_truncated_curve :
    AgreeBelow 6 infinityUnitSeries
      (1 + 21 * infinityS + 26 * infinityS ^ 2) := by
  unfold AgreeBelow
  refine ⟨infinityCurveRemainder, ?_⟩
  apply Polynomial.funext
  intro x
  simp [infinityCurveRemainder, infinityUnitSeries, infinityS, p5Parameter]
  ring

/-- Terms omitted from the truncated reversed polynomial start in degree six. -/
theorem infinityReversedRhs_tail :
    AgreeBelow 6
      (1 + 21 * infinityS + 26 * infinityS ^ 2)
      (infinityReversedRhs infinityS) := by
  unfold AgreeBelow
  refine ⟨
    -(C 5 ^ 2 * infinityUnitSeries) ^ 3 *
      (10 + 5 * infinityS + infinityS ^ 2), ?_⟩
  simp [infinityReversedRhs, infinityS, p5Parameter]
  ring

/-- The exact infinity chart is satisfied through degree five. -/
theorem infinityUnitSeries_curve :
    AgreeBelow 6 infinityUnitSeries (infinityReversedRhs infinityS) := by
  have h₁ := infinityUnitSeries_truncated_curve
  have h₂ := infinityReversedRhs_tail
  unfold AgreeBelow at h₁ h₂ ⊢
  convert dvd_add h₁ h₂ using 1
  ring

/--
The primitive at infinity satisfies the differential identity

`2g G' + (c₀ r²g+c₁)(2r'g+r g') = 0`

through degree five.
-/
theorem infinityPrimitive_certificate (c₀ c₁ : ℚ) :
    AgreeBelow 6
      (2 * infinityUnitSeries * (infinityPrimitive c₀ c₁).derivative +
        (C c₀ * p5Parameter ^ 2 * infinityUnitSeries + C c₁) *
          (2 * p5Parameter.derivative * infinityUnitSeries +
            p5Parameter * infinityUnitSeries.derivative))
      0 := by
  unfold AgreeBelow
  refine ⟨infinityDifferentialRemainder c₀ c₁, ?_⟩
  apply Polynomial.funext
  intro x
  simp [infinityDifferentialRemainder, infinityUnitSeries,
    infinityPrimitive, p5Parameter, derivative_mul, derivative_pow]
  ring

/-- The infinity primitive has unit-controlled leading coefficient `-5c₁`. -/
theorem infinityPrimitive_linear_coefficient (c₀ c₁ : ℚ) :
    (infinityPrimitive c₀ c₁).coeff 1 = -5 * c₁ := by
  have hcoeff (p : ℚ[X]) : p.coeff 1 = p.derivative.eval 0 := by
    rw [← coeff_zero_eq_eval_zero]
    simpa using (coeff_derivative p 0).symm
  rw [hcoeff]
  simp [infinityPrimitive, p5Parameter, derivative_mul, derivative_pow]
  ring

/-- The coefficient of `t` in the reduced annihilator is a unit, which is
the nonvanishing row at infinity. -/
theorem annihilator_infinity_residue_unit :
    (1 : ZMod 5) ≠ 0 := by
  decide

/-! ## The exceptional Weierstrass disc at `(-1,0)` -/

/-- The curve equation after shifting `t=-1+v`. -/
def exceptionalShiftedRhs (v : ℚ[X]) : ℚ[X] :=
  -16 * v + 48 * v ^ 2 - 48 * v ^ 3 + 16 * v ^ 4 + v ^ 5

/-- The first two nonzero terms of the unique even solution `v=v(u²)`,
already specialized to the disc parameter `u=5X`. -/
def exceptionalV : ℚ[X] :=
  C (-1 / 16 : ℚ) * p5Parameter ^ 2 +
    C (3 / 256 : ℚ) * p5Parameter ^ 4

/-- The corresponding shifted `t=-1+v`. -/
def exceptionalT : ℚ[X] :=
  -1 + exceptionalV

/-- Exact quotient of the exceptional curve equation after the two-term
series is substituted. -/
def exceptionalCurveRemainder : ℚ[X] :=
  C (234375 / 256 : ℚ) -
    C (390625 / 4096 : ℚ) * X ^ 2 -
    C (10771484375 / 1048576 : ℚ) * X ^ 4 +
    C (101806640625 / 16777216 : ℚ) * X ^ 6 +
    C (5548095703125 / 134217728 : ℚ) * X ^ 8 -
    C (119476318359375 / 2147483648 : ℚ) * X ^ 10 +
    C (1544952392578125 / 68719476736 : ℚ) * X ^ 12 -
    C (23174285888671875 / 1099511627776 : ℚ) * X ^ 14

/-- The first two terms of the local Coleman primitive at `(-1,0)`. -/
def exceptionalPrimitive (c₀ c₁ : ℚ) : ℚ[X] :=
  C ((c₁ - c₀) / 16) * p5Parameter +
    C ((6 * c₀ - 5 * c₁) / 768) * p5Parameter ^ 3

/-- Exact quotient of the exceptional differential identity. -/
def exceptionalDifferentialRemainder (_c₀ c₁ : ℚ) : ℚ[X] :=
  C (140625 * c₁ / 2048) * X -
    C (3515625 * c₁ / 16384) * X ^ 3

/-- The exact shift identity used to obtain the exceptional local chart. -/
theorem linearQuartic_exceptional_shift (v : ℚ[X]) :
    linearQuarticCurveRhs (-1 + v) = exceptionalShiftedRhs v := by
  simp [linearQuarticCurveRhs, exceptionalShiftedRhs]
  ring

/-- The displayed two-term even series solves the full shifted curve equation
through degree five in `X` (equivalently through `u⁴`). -/
theorem exceptionalV_curve :
    AgreeBelow 6 (p5Parameter ^ 2)
      (exceptionalShiftedRhs exceptionalV) := by
  unfold AgreeBelow
  refine ⟨exceptionalCurveRemainder, ?_⟩
  apply Polynomial.funext
  intro x
  simp [exceptionalCurveRemainder, exceptionalShiftedRhs, exceptionalV,
    p5Parameter]
  ring

/-- Therefore `(t,w)=(-1+v(25X²),5X)` satisfies the original curve equation
through the same order. -/
theorem exceptional_chart_curve :
    AgreeBelow 6 (p5Parameter ^ 2)
      (linearQuarticCurveRhs exceptionalT) := by
  simpa [exceptionalT, linearQuartic_exceptional_shift] using
    exceptionalV_curve

/--
The exceptional primitive satisfies

`2u G' = (c₀+c₁t)t'`

through degree three.  This is the finite differential identity behind the
Strassmann row.
-/
theorem exceptionalPrimitive_certificate (c₀ c₁ : ℚ) :
    AgreeBelow 4
      (2 * p5Parameter * (exceptionalPrimitive c₀ c₁).derivative)
      ((C c₀ + C c₁ * exceptionalT) * exceptionalT.derivative) := by
  unfold AgreeBelow
  refine ⟨exceptionalDifferentialRemainder c₀ c₁, ?_⟩
  apply Polynomial.funext
  intro x
  simp [exceptionalDifferentialRemainder, exceptionalPrimitive,
    exceptionalT, exceptionalV, p5Parameter, derivative_mul, derivative_pow]
  ring

/-- The exceptional local chart starts with
`v=-u²/16+3u⁴/256`. -/
theorem exceptionalV_coefficients :
    exceptionalV.coeff 2 = -(25 / 16 : ℚ) ∧
      exceptionalV.coeff 4 = (1875 / 256 : ℚ) := by
  have heq :
      exceptionalV =
        C (-25 / 16 : ℚ) * X ^ 2 +
          C (1875 / 256 : ℚ) * X ^ 4 := by
    apply Polynomial.funext
    intro x
    simp [exceptionalV, p5Parameter]
    ring
  rw [heq]
  norm_num

/-- The first two odd coefficients of the exceptional primitive are exactly
the rows printed by the Sage certificate. -/
theorem exceptionalPrimitive_coefficients (c₀ c₁ : ℚ) :
    (exceptionalPrimitive c₀ c₁).coeff 1 =
        5 * (c₁ - c₀) / 16 ∧
      (exceptionalPrimitive c₀ c₁).coeff 3 =
        125 * (6 * c₀ - 5 * c₁) / 768 := by
  have heq :
      exceptionalPrimitive c₀ c₁ =
        C (5 * (c₁ - c₀) / 16) * X +
          C (125 * (6 * c₀ - 5 * c₁) / 768) * X ^ 3 := by
    apply Polynomial.funext
    intro x
    simp [exceptionalPrimitive, p5Parameter]
    ring
  rw [heq]
  norm_num

/-- The exact rational coefficient formula agrees with the form
`(6(c₀-c₁)+c₁)/(3·256)` used in the external note. -/
theorem exceptional_cubic_formula (c₀ c₁ : ℚ) :
    (6 * c₀ - 5 * c₁) / 768 =
      (6 * (c₀ - c₁) + c₁) / (3 * 256) := by
  ring

/-! ## Normalized Strassmann rows -/

/-- After division by the common factor `5`, the leading coefficients in
the four ordinary discs and at infinity are all nonzero modulo `5`.
The order is `(0,1)`, `(0,-1)`, `(1,8)`, `(1,-8)`, infinity. -/
theorem ordinary_and_infinity_normalized_leading_units :
    ((1 / 2 : ZMod 5) ≠ 0) ∧
      (-(1 / 2 : ZMod 5) ≠ 0) ∧
      ((2 / 16 : ZMod 5) ≠ 0) ∧
      (-(2 / 16 : ZMod 5) ≠ 0) ∧
      (-(1 : ZMod 5) ≠ 0) := by
  have h1 : (1 : ZMod 5) ≠ 0 := by decide
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  have h16 : (16 : ZMod 5) ≠ 0 := by decide
  simp [h1, h2, h16]

/-- If the exceptional numerator is exactly `5k`, division of the local
primitive by `25` gives the two displayed normalized coefficients. -/
theorem exceptional_normalized_coefficients
    {c₀ c₁ k : ℚ} (hdiff : c₀ - c₁ = 5 * k) :
    (exceptionalPrimitive c₀ c₁).coeff 1 / 25 = -k / 16 ∧
      (exceptionalPrimitive c₀ c₁).coeff 3 / 25 =
        5 * (6 * c₀ - 5 * c₁) / 768 := by
  rcases exceptionalPrimitive_coefficients c₀ c₁ with ⟨h₁, h₃⟩
  rw [h₁, h₃]
  constructor <;> nlinarith

/-- Reduction of the normalized exceptional primitive.  Every higher term
shown by the local computation vanishes, leaving a nonzero linear term when
the exact quotient `(c₀-c₁)/5` is a unit. -/
def exceptionalReducedStrassmann (k : ZMod 5) : (ZMod 5)[X] :=
  C (-k / 16) * X

/-- The reduced exceptional row has precisely the known zero `z=0`. -/
theorem exceptionalReducedStrassmann_eval_eq_zero_iff
    {k z : ZMod 5} (hk : k ≠ 0) :
    eval z (exceptionalReducedStrassmann k) = 0 ↔ z = 0 := by
  have h16 : (16 : ZMod 5) ≠ 0 := by decide
  simp [exceptionalReducedStrassmann, hk, h16]

/-- The displayed normalized cubic coefficient vanishes modulo `5`. -/
theorem exceptional_normalized_cubic_vanishes
    (c₀ c₁ : ZMod 5) :
    5 * (6 * c₀ - 5 * c₁) / 768 = 0 := by
  have h5 : (5 : ZMod 5) = 0 := ZMod.natCast_self 5
  simp only [h5, zero_mul, zero_div]

/--
The denominator-loss inequality used for every omitted odd term of degree
`n ≥ 3` after substituting `u=5z` and dividing the primitive by `25`:

`n - 2 - v₅(n) ≥ 1`.
-/
theorem exceptional_tail_valuation_bound
    {n : ℕ} (hn : 3 ≤ n) :
    1 ≤ n - 2 - padicValNat 5 n := by
  by_cases hsmall : n < 6
  · have hnle : n ≤ 5 := by omega
    have hcases : n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hcases with rfl | rfl | rfl
    · rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬5 ∣ 3)]
    · rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬5 ∣ 4)]
      omega
    · rw [padicValNat_self]
      omega
  · have hlarge : 5 < n := by omega
    have hval := padicValNat_add_le_self (p := 5) hlarge
    omega

/-- Equivalent addition form of the tail bound, convenient for transporting
coefficient valuations. -/
theorem exceptional_tail_valuation_bound'
    {n : ℕ} (hn : 3 ≤ n) :
    padicValNat 5 n + 3 ≤ n := by
  by_cases hsmall : n < 6
  · have hnle : n ≤ 5 := by omega
    have hcases : n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hcases with rfl | rfl | rfl
    · rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬5 ∣ 3)]
    · rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬5 ∣ 4)]
      omega
    · rw [padicValNat_self]
      omega
  · have hlarge : 5 < n := by omega
    have hval := padicValNat_add_le_self (p := 5) hlarge
    omega
