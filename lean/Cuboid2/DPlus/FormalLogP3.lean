import Cuboid2.DPlus.GlobalMumfordCertificate
import Cuboid2.DPlus.LocalP3
import Mathlib.Algebra.Polynomial.Div
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Exact formal-logarithm rows for `D+` at `p = 3`

This file contains only fixed-curve algebra.  In particular, it does not
postulate a Coleman integral or a rational-point classification.  The
displayed polynomials are the finite initial rows used by the direct
certificate, and the valuation lemmas cover every omitted degree.
-/

namespace Cuboid2

open Polynomial

noncomputable section

local instance dplusFormalLogFactPrime3 : Fact (Nat.Prime 3) :=
  ⟨by norm_num⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## The genuine infinity implicit equation -/

/--
The infinity relation, viewed as a polynomial in `w` with `t` fixed.
This is deliberately separate from the older placeholder derivative row.
-/
def dplusInfinityPolynomialW (t : ℚ) : ℚ[X] :=
  X - C (t ^ 2) * (1 - C 2 * X ^ 3 + C (5 / 4 : ℚ) * X ^ 4)

@[simp] theorem eval_dplusInfinityPolynomialW (t w : ℚ) :
    eval w (dplusInfinityPolynomialW t) =
      dplusInfinityRelation t w := by
  simp [dplusInfinityPolynomialW, dplusInfinityRelation]

/-- The actual infinity equation passes through `(t,w)=(0,0)`. -/
theorem dplusInfinityPolynomialW_origin :
    eval 0 (dplusInfinityPolynomialW 0) = 0 := by
  norm_num [dplusInfinityPolynomialW]

/--
The genuine partial derivative of
`w - t²(1 - 2w³ + 5w⁴/4)` with respect to `w` is a unit at the origin.
-/
theorem dplusInfinityPolynomialW_derivative_at_origin :
    eval 0 (derivative (dplusInfinityPolynomialW 0)) = 1 := by
  norm_num [dplusInfinityPolynomialW]

/-- All denominators in the fixed infinity equation are prime to `3`. -/
theorem dplusInfinityPolynomialW_denominators_are_three_units :
    padicValRat 3 (1 : ℚ) = 0 ∧
      padicValRat 3 (2 : ℚ) = 0 ∧
      padicValRat 3 (5 / 4 : ℚ) = 0 := by
  native_decide

/-! ## The two branches above `a = 1` -/

/-- The shifted curve polynomial `dplusRhs (1+x)`. -/
def dplusShiftedRhsPolynomial : ℚ[X] :=
  C 4 * X ^ 5 + C 20 * X ^ 4 + C 40 * X ^ 3 +
    C 32 * X ^ 2 + C 9 * X + 1

/-- Exact coordinate shift of the fixed curve equation. -/
theorem dplusShiftedRhsPolynomial_eval (x : ℚ) :
    eval x dplusShiftedRhsPolynomial = dplusRhs (1 + x) := by
  simp [dplusShiftedRhsPolynomial, dplusRhs]
  ring_nf

/-- Cubic initial row of `1 / sqrt (dplusRhs (1+x))`. -/
def dplusInverseRootTrunc : ℚ[X] :=
  1 - C (9 / 2 : ℚ) * X + C (115 / 8 : ℚ) * X ^ 2 -
    C (509 / 16 : ℚ) * X ^ 3

/-- Exact quotient in the inverse-square-root residual. -/
def dplusInverseRootResidualQuotient : ℚ[X] :=
  C (259081 / 64 : ℚ) * X ^ 7 +
    C (1061265 / 64 : ℚ) * X ^ 6 +
    C (773153 / 32 : ℚ) * X ^ 5 +
    C (78205 / 16 : ℚ) * X ^ 4 -
    C (1050895 / 256 : ℚ) * X ^ 3 +
    C (455437 / 256 : ℚ) * X ^ 2 -
    C (27841 / 32 : ℚ) * X -
    C (1027 / 64 : ℚ)

/--
The stored inverse-root row solves `f I² = 1` through degree three.  The
identity is exact; no truncated numerical equality is used.
-/
theorem dplusInverseRootTrunc_residual :
    dplusShiftedRhsPolynomial * dplusInverseRootTrunc ^ 2 - 1 =
      X ^ 4 * dplusInverseRootResidualQuotient := by
  apply Polynomial.funext
  intro x
  simp [dplusShiftedRhsPolynomial, dplusInverseRootTrunc,
    dplusInverseRootResidualQuotient]
  ring

/-- Cubic primitive row for `da/R` on the positive branch at `a=1`. -/
def dplusH0Trunc : ℚ[X] :=
  X - C (9 / 4 : ℚ) * X ^ 2 + C (115 / 24 : ℚ) * X ^ 3

/-- Its derivative agrees with the inverse-root row through degree two. -/
theorem dplusH0Trunc_derivative_residual :
    derivative dplusH0Trunc - dplusInverseRootTrunc =
      C (509 / 16 : ℚ) * X ^ 3 := by
  apply Polynomial.funext
  intro x
  simp [dplusH0Trunc, dplusInverseRootTrunc, derivative_sub,
    derivative_mul, derivative_pow]
  ring

/-- The leading coefficient of the first local primitive is a `3`-unit. -/
theorem dplusH0Trunc_linear_unit :
    padicValRat 3 (dplusH0Trunc.coeff 1) = 0 := by
  rw [show dplusH0Trunc.coeff 1 = (1 : ℚ) by
    norm_num [dplusH0Trunc]]
  native_decide

/-! ## The exact `11D` logarithm direction -/

/-- Divided first logarithm through primitive degree three. -/
def dplusLog0UnitApprox : ℚ :=
  1 + (9 / 4 : ℚ) * dplusElevenDShiftB +
    (115 / 24 : ℚ) *
      (dplusElevenDShiftB ^ 2 - dplusElevenDShiftC)

/-- Divided second logarithm through primitive degree three. -/
def dplusLog1UnitApprox : ℚ :=
  1 + (7 / 4 : ℚ) * dplusElevenDShiftB +
    (79 / 24 : ℚ) *
      (dplusElevenDShiftB ^ 2 - dplusElevenDShiftC)

/-- Exact rational representative of the logarithm ratio modulo `27`. -/
def dplusLambdaApprox : ℚ :=
  dplusLog1UnitApprox / dplusLog0UnitApprox

/-- The shifted support coefficients have valuations `1` and `2`. -/
theorem dplusElevenD_shift_valuations :
    padicValRat 3 dplusElevenDShiftB = 1 ∧
      padicValRat 3 dplusElevenDShiftC = 2 := by
  native_decide

/-- The shifted support discriminant has exact valuation four. -/
theorem dplusElevenD_discriminant_valuation :
    padicValRat 3 dplusElevenDDiscriminant = 4 := by
  native_decide

/-- Both divided logarithm approximations are `3`-adic units. -/
theorem dplusLogUnitApprox_valuations :
    padicValRat 3 dplusLog0UnitApprox = 0 ∧
      padicValRat 3 dplusLog1UnitApprox = 0 := by
  native_decide

/-- The exact rational ratio is congruent to `7` modulo `27`. -/
theorem dplusLambdaApprox_mod_twentySeven :
    3 ≤ padicValRat 3 (dplusLambdaApprox - 7) := by
  native_decide

/-- In particular the annihilator coefficient differs from `1` by valuation one. -/
theorem dplusLambdaApprox_sub_one_valuation :
    padicValRat 3 (dplusLambdaApprox - 1) = 1 := by
  native_decide

/-! ## Normalized Strassmann rows -/

/--
Finite primitive obtained from `(6-x) dx/R`, with the representative
`lambda - 1 = 6` selected by `lambda = 7`.
-/
def dplusOneDiskPrimitiveTrunc : ℚ[X] :=
  C 6 * X - C 14 * X ^ 2 + C (121 / 4 : ℚ) * X ^ 3 -
    C (821 / 16 : ℚ) * X ^ 4 + C (509 / 80 : ℚ) * X ^ 5

/-- Exact derivative identity for the finite one-disk primitive row. -/
theorem dplusOneDiskPrimitiveTrunc_derivative :
    derivative dplusOneDiskPrimitiveTrunc =
      (C 6 - X) * dplusInverseRootTrunc := by
  apply Polynomial.funext
  intro x
  simp [dplusOneDiskPrimitiveTrunc, dplusInverseRootTrunc,
    derivative_sub, derivative_mul, derivative_pow]
  ring

/-- The positive-branch row after `x=9z` and division by `27`. -/
def dplusOneDiskNormalizedTrunc : ℚ[X] :=
  C 2 * X - C 42 * X ^ 2 + C (3267 / 4 : ℚ) * X ^ 3 -
    C (199503 / 16 : ℚ) * X ^ 4 +
    C (1113183 / 80 : ℚ) * X ^ 5

/-- Exact normalization of the one-disk primitive. -/
theorem dplusOneDiskNormalizedTrunc_eval (z : ℚ) :
    eval z dplusOneDiskNormalizedTrunc =
      eval (9 * z) dplusOneDiskPrimitiveTrunc / 27 := by
  simp [dplusOneDiskNormalizedTrunc, dplusOneDiskPrimitiveTrunc]
  ring_nf

/--
The normalized positive-branch row is linear and nonzero modulo `3`; every
displayed nonlinear coefficient has positive valuation.
-/
theorem dplusOneDiskNormalizedTrunc_valuation_row :
    padicValRat 3 (dplusOneDiskNormalizedTrunc.coeff 1) = 0 ∧
      1 ≤ padicValRat 3 (dplusOneDiskNormalizedTrunc.coeff 2) ∧
      1 ≤ padicValRat 3 (dplusOneDiskNormalizedTrunc.coeff 3) ∧
      1 ≤ padicValRat 3 (dplusOneDiskNormalizedTrunc.coeff 4) ∧
      1 ≤ padicValRat 3 (dplusOneDiskNormalizedTrunc.coeff 5) := by
  rw [show dplusOneDiskNormalizedTrunc.coeff 1 = (2 : ℚ) by
      norm_num [dplusOneDiskNormalizedTrunc],
    show dplusOneDiskNormalizedTrunc.coeff 2 = (-42 : ℚ) by
      norm_num [dplusOneDiskNormalizedTrunc],
    show dplusOneDiskNormalizedTrunc.coeff 3 = (3267 / 4 : ℚ) by
      norm_num [dplusOneDiskNormalizedTrunc],
    show dplusOneDiskNormalizedTrunc.coeff 4 = (-199503 / 16 : ℚ) by
      norm_num [dplusOneDiskNormalizedTrunc],
    show dplusOneDiskNormalizedTrunc.coeff 5 = (1113183 / 80 : ℚ) by
      norm_num [dplusOneDiskNormalizedTrunc]]
  native_decide

/-- The negative branch is obtained by multiplication by `-1`. -/
def dplusOneDiskNormalizedTruncNeg : ℚ[X] :=
  -dplusOneDiskNormalizedTrunc

/-- Its linear coefficient remains a `3`-unit. -/
theorem dplusOneDiskNormalizedTruncNeg_linear_unit :
    padicValRat 3 (dplusOneDiskNormalizedTruncNeg.coeff 1) = 0 := by
  rw [show dplusOneDiskNormalizedTruncNeg.coeff 1 = (-2 : ℚ) by
    norm_num [dplusOneDiskNormalizedTruncNeg,
      dplusOneDiskNormalizedTrunc]]
  native_decide

/-- Finite primitive row at infinity for `lambda = 7`. -/
def dplusInfinityPrimitiveTrunc : ℚ[X] :=
  X - C (7 / 3 : ℚ) * X ^ 3 - C (6 / 7 : ℚ) * X ^ 7 +
    C (61 / 9 : ℚ) * X ^ 9 - C (175 / 44 : ℚ) * X ^ 11 -
    C (12 / 13 : ℚ) * X ^ 13

/-- Normalized infinity row `F(3z)/3`. -/
def dplusInfinityNormalizedTrunc : ℚ[X] :=
  X - C 21 * X ^ 3 - C (4374 / 7 : ℚ) * X ^ 7 +
    C 44469 * X ^ 9 - C (10333575 / 44 : ℚ) * X ^ 11 -
    C (6377292 / 13 : ℚ) * X ^ 13

/-- Exact normalization of the infinity primitive. -/
theorem dplusInfinityNormalizedTrunc_eval (z : ℚ) :
    eval z dplusInfinityNormalizedTrunc =
      eval (3 * z) dplusInfinityPrimitiveTrunc / 3 := by
  simp [dplusInfinityNormalizedTrunc, dplusInfinityPrimitiveTrunc]
  ring_nf

/--
The normalized infinity row has unit linear coefficient and every displayed
higher coefficient has positive valuation.
-/
theorem dplusInfinityNormalizedTrunc_valuation_row :
    padicValRat 3 (dplusInfinityNormalizedTrunc.coeff 1) = 0 ∧
      1 ≤ padicValRat 3 (dplusInfinityNormalizedTrunc.coeff 3) ∧
      1 ≤ padicValRat 3 (dplusInfinityNormalizedTrunc.coeff 7) ∧
      1 ≤ padicValRat 3 (dplusInfinityNormalizedTrunc.coeff 9) ∧
      1 ≤ padicValRat 3 (dplusInfinityNormalizedTrunc.coeff 11) ∧
      1 ≤ padicValRat 3 (dplusInfinityNormalizedTrunc.coeff 13) := by
  rw [show dplusInfinityNormalizedTrunc.coeff 1 = (1 : ℚ) by
      norm_num [dplusInfinityNormalizedTrunc],
    show dplusInfinityNormalizedTrunc.coeff 3 = (-21 : ℚ) by
      norm_num [dplusInfinityNormalizedTrunc, Polynomial.coeff_X],
    show dplusInfinityNormalizedTrunc.coeff 7 = (-4374 / 7 : ℚ) by
      norm_num [dplusInfinityNormalizedTrunc, Polynomial.coeff_X],
    show dplusInfinityNormalizedTrunc.coeff 9 = (44469 : ℚ) by
      norm_num [dplusInfinityNormalizedTrunc, Polynomial.coeff_X],
    show dplusInfinityNormalizedTrunc.coeff 11 =
        (-10333575 / 44 : ℚ) by
      norm_num [dplusInfinityNormalizedTrunc, Polynomial.coeff_X],
    show dplusInfinityNormalizedTrunc.coeff 13 =
        (-6377292 / 13 : ℚ) by
      norm_num [dplusInfinityNormalizedTrunc, Polynomial.coeff_X]]
  native_decide

/-! ## Universal tail bounds in the form used by the rows -/

/-- Every omitted infinity term vanishes modulo `3` after normalization. -/
theorem dplusInfinityTailVanishesModuloThree
    {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ n - 1 - padicValNat 3 n :=
  one_le_degree_sub_one_sub_padicValNat_three hn

/-- Every `delta`-part term in an `a=1` disk vanishes modulo `3`. -/
theorem dplusOneDiskDeltaTailVanishesModuloThree
    {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ 2 * n - 2 - padicValNat 3 n :=
  one_le_twice_degree_sub_two_sub_padicValNat_three hn

/-- Every `-x`-part term in an `a=1` disk vanishes modulo `3`. -/
theorem dplusOneDiskXTailVanishesModuloThree
    {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ 2 * n - 3 - padicValNat 3 n :=
  one_le_twice_degree_sub_three_sub_padicValNat_three hn

end

end Cuboid2
