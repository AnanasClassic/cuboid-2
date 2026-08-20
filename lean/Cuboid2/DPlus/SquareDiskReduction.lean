import Cuboid2.DPlus.GlobalBridge
import Cuboid2.DPlus.LocalP3
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Rational valuation cases for square abscissas on `D+`

These lemmas are independent of the missing global Jacobian/Coleman bridge.
They make the projective `p=3` disk reduction precise at the level of
rational coordinates.
-/

namespace Cuboid2

noncomputable section

local instance dplusSquareDiskFactPrime3 : Fact (Nat.Prime 3) :=
  ⟨by norm_num⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem dplus_val_two :
    padicValRat 3 (2 : ℚ) = 0 := by
  native_decide

private theorem dplus_val_four :
    padicValRat 3 (4 : ℚ) = 0 := by
  native_decide

private theorem dplus_val_neg_eight :
    padicValRat 3 (-8 : ℚ) = 0 := by
  native_decide

private theorem dplus_val_five :
    padicValRat 3 (5 : ℚ) = 0 := by
  native_decide

/-- A rational square has even `3`-adic valuation. -/
theorem dplus_square_abscissa_valuation_even
    {a u : ℚ} (ha : a = u ^ 2) :
    Even (padicValRat 3 a) := by
  rw [ha]
  simp only [padicValRat.pow]
  exact even_two_mul (padicValRat 3 u)

/--
For a nonzero square abscissa of positive valuation, the curve equation
makes the affine cofactor a rational square.  The subsequent nonsquare-unit
contradiction is the local `3`-adic step.
-/
theorem dplus_positive_square_abscissa_cofactor_square
    (P : DPlusAffinePoint)
    {u : ℚ}
    (ha : P.a = u ^ 2)
    (hpositive : 0 < padicValRat 3 P.a) :
    u ≠ 0 ∧ (P.R / u) ^ 2 = dplusCofactor P.a := by
  have ha0 : P.a ≠ 0 := by
    intro hzero
    rw [hzero, padicValRat.zero] at hpositive
    omega
  have hu : u ≠ 0 := by
    intro hzero
    apply ha0
    simp [ha, hzero]
  exact ⟨hu, dplus_zero_disk_square_quotient ha P.onCurve hu⟩

/-- A point whose abscissa is literally zero is the known Weierstrass point. -/
theorem dplus_zero_abscissa_fiber
    (P : DPlusAffinePoint) (ha : P.a = 0) :
    P = dplusZero :=
  dplus_eq_zero_of_abscissa_eq_zero P ha

private theorem dplus_val_four_mul_pow_four
    {a : ℚ} (ha : a ≠ 0) :
    padicValRat 3 (4 * a ^ 4) = 4 * padicValRat 3 a := by
  rw [padicValRat.mul (by norm_num) (pow_ne_zero 4 ha),
    padicValRat.pow]
  rw [dplus_val_four]
  omega

private theorem dplus_val_neg_eight_mul
    {a : ℚ} (ha : a ≠ 0) :
    padicValRat 3 (-8 * a) = padicValRat 3 a := by
  rw [padicValRat.mul (by norm_num) ha]
  rw [dplus_val_neg_eight]
  omega

private theorem dplus_negative_tail_ne_zero
    {a : ℚ} (_ha : a ≠ 0) (hnegative : padicValRat 3 a < 0) :
    -8 * a + 5 ≠ 0 := by
  intro hzero
  have haeq : a = (5 / 8 : ℚ) := by
    linarith
  rw [haeq] at hnegative
  have hval : padicValRat 3 (5 / 8 : ℚ) = 0 := by
    native_decide
  rw [hval] at hnegative
  omega

/-- At negative valuation the affine cofactor has valuation `4 v₃(a)`. -/
theorem dplus_negative_abscissa_cofactor_valuation
    {a : ℚ} (ha : a ≠ 0) (hnegative : padicValRat 3 a < 0) :
    padicValRat 3 (dplusCofactor a) = 4 * padicValRat 3 a := by
  have h4 := dplus_val_four_mul_pow_four ha
  have h8 := dplus_val_neg_eight_mul ha
  have htail0 := dplus_negative_tail_ne_zero ha hnegative
  have htail :
      padicValRat 3 (-8 * a + 5) = padicValRat 3 (-8 * a) := by
    apply padicValRat.add_eq_of_lt htail0
      (mul_ne_zero (by norm_num) ha) (by norm_num)
    rw [h8, dplus_val_five]
    omega
  have hsum0 : 4 * a ^ 4 + (-8 * a + 5) ≠ 0 := by
    intro hzero
    have heq : 4 * a ^ 4 = -(-8 * a + 5) := by
      linarith
    have hval := congrArg (padicValRat 3) heq
    rw [padicValRat.neg, h4, htail, h8] at hval
    omega
  change
    padicValRat 3 (4 * a ^ 4 - 8 * a + 5) =
      4 * padicValRat 3 a
  rw [show 4 * a ^ 4 - 8 * a + 5 =
    4 * a ^ 4 + (-8 * a + 5) by ring]
  rw [padicValRat.add_eq_of_lt hsum0
    (mul_ne_zero (by norm_num) (pow_ne_zero 4 ha)) htail0]
  · exact h4
  · rw [h4, htail, h8]
    omega

/--
At negative valuation the leading `4a⁵` term controls the curve equation:
`2 v₃(R) = 5 v₃(a)`.
-/
theorem dplus_negative_abscissa_curve_valuation
    (P : DPlusAffinePoint)
    (hnegative : padicValRat 3 P.a < 0) :
    2 * padicValRat 3 P.R = 5 * padicValRat 3 P.a := by
  have ha : P.a ≠ 0 := by
    intro ha0
    rw [ha0, padicValRat.zero] at hnegative
    omega
  have hcofactor0 : dplusCofactor P.a ≠ 0 := by
    intro hzero
    have hval := dplus_negative_abscissa_cofactor_valuation ha hnegative
    rw [hzero, padicValRat.zero] at hval
    omega
  have hR : P.R ≠ 0 := by
    intro hR0
    have hproduct : P.a * dplusCofactor P.a = 0 := by
      calc
        P.a * dplusCofactor P.a = dplusRhs P.a :=
          (dplusRhs_eq_mul_cofactor P.a).symm
        _ = P.R ^ 2 := P.onCurve.symm
        _ = 0 := by rw [hR0]; norm_num
    exact (mul_ne_zero ha hcofactor0) hproduct
  have hcurveVal := congrArg (padicValRat 3) P.onCurve
  rw [padicValRat.pow, dplusRhs_eq_mul_cofactor,
    padicValRat.mul ha hcofactor0,
    dplus_negative_abscissa_cofactor_valuation ha hnegative] at hcurveVal
  omega

/--
For a negative-valuation square abscissa, the rational infinity parameter
`t = 2a²/R` has positive valuation, and `w=1/a` satisfies the exact chart
equation.
-/
theorem dplus_negative_square_abscissa_infinity_chart
    (P : DPlusAffinePoint)
    {u : ℚ}
    (haSquare : P.a = u ^ 2)
    (hnegative : padicValRat 3 P.a < 0) :
    let t := 2 * P.a ^ 2 / P.R
    let w := 1 / P.a
    0 < padicValRat 3 t ∧ dplusInfinityRelation t w = 0 := by
  dsimp
  have ha : P.a ≠ 0 := by
    intro ha0
    rw [ha0, padicValRat.zero] at hnegative
    omega
  have hcofactor0 : dplusCofactor P.a ≠ 0 := by
    intro hzero
    have hval := dplus_negative_abscissa_cofactor_valuation ha hnegative
    rw [hzero, padicValRat.zero] at hval
    omega
  have hR : P.R ≠ 0 := by
    intro hR0
    have hproduct : P.a * dplusCofactor P.a = 0 := by
      calc
        P.a * dplusCofactor P.a = dplusRhs P.a :=
          (dplusRhs_eq_mul_cofactor P.a).symm
        _ = P.R ^ 2 := P.onCurve.symm
        _ = 0 := by rw [hR0]; norm_num
    exact (mul_ne_zero ha hcofactor0) hproduct
  constructor
  · have hvalR := dplus_negative_abscissa_curve_valuation P hnegative
    have ht :
        padicValRat 3 (2 * P.a ^ 2 / P.R) =
          2 * padicValRat 3 P.a - padicValRat 3 P.R := by
      rw [padicValRat.div
          (mul_ne_zero (by norm_num) (pow_ne_zero 2 ha)) hR,
        padicValRat.mul (by norm_num) (pow_ne_zero 2 ha),
        padicValRat.pow]
      rw [dplus_val_two]
      omega
    have heven := dplus_square_abscissa_valuation_even haSquare
    rw [ht]
    rcases heven with ⟨k, hk⟩
    omega
  · exact dplus_infinity_chart_relation ha hR P.onCurve rfl rfl

end

end Cuboid2
