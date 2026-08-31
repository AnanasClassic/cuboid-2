import Cuboid2.QuadraticReduction.GaussianProjectiveReduction
import Cuboid2.QuadraticReduction.GaussianP37

/-!
# First-order formal coordinates on the actual split local curves

For a point in the infinity disk of an integral model
`y² = x³ + A x² + B x`, this module constructs the actual local parameters
`t = -x/y` and `r = 1/x`.  Both are integral and reduce to zero, and they
satisfy the exact formal-curve relation
`r = t²(1 + A r + B r²)`.
-/

namespace Cuboid2
namespace GaussianFormalLocal

noncomputable section

open GaussianProjectiveReduction GaussianGoodReduction GaussianP37

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : DecidableEq ℚ_[37] := Classical.decEq _

/-- The factored equation on the actual normalized local model. -/
theorem local_curve_equation
    (A B : ℤ_[37]) {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y) :
    y ^ 2 =
      x * (x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37])) := by
  have h := hpoint.left
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [localPadicCurve, localCurve, WeierstrassCurve.map,
    map_zero, zero_mul, add_zero] at h
  calc
    y ^ 2 =
        x ^ 3 + (A : ℚ_[37]) * x ^ 2 + (B : ℚ_[37]) * x := h
    _ = x * (x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37])) := by
      ring

/-- An affine local point reduces to infinity exactly through the
nonintegral-`x` branch, hence its abscissa has norm greater than one. -/
theorem norm_x_gt_one_of_reduce_none
    (A B : ℤ_[37]) [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hred :
      finiteReducePoint A B
        (.some x y hpoint) = none) :
    1 < ‖x‖ := by
  by_contra hx
  have hxInt : ‖x‖ ≤ 1 := le_of_not_gt hx
  have hred' := hred
  unfold finiteReducePoint at hred'
  simp only [reducePoint, hxInt, ↓reduceDIte] at hred'
  simp [finitePointOfResidue, WeierstrassCurve.Affine.Point.mk] at hred'

private theorem norm_inner_eq_norm_x_sq
    (A B : ℤ_[37]) {x : ℚ_[37]} (hx : 1 < ‖x‖) :
    ‖x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37])‖ = ‖x‖ ^ 2 := by
  have hA : ‖(A : ℚ_[37])‖ ≤ 1 := A.property
  have hB : ‖(B : ℚ_[37])‖ ≤ 1 := B.property
  have hAx : ‖(A : ℚ_[37]) * x‖ ≤ ‖x‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg (A : ℚ_[37]), norm_nonneg x]
  have hsmall :
      ‖(A : ℚ_[37]) * x + (B : ℚ_[37])‖ ≤ ‖x‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    exact max_le hAx (hB.trans hx.le)
  have hlt :
      ‖(A : ℚ_[37]) * x + (B : ℚ_[37])‖ < ‖x ^ 2‖ := by
    rw [norm_pow]
    nlinarith [norm_nonneg x]
  calc
    ‖x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37])‖ =
        ‖x ^ 2 + ((A : ℚ_[37]) * x + (B : ℚ_[37]))‖ := by
          congr 1
          ring
    _ = max ‖x ^ 2‖ ‖(A : ℚ_[37]) * x + (B : ℚ_[37])‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (ne_of_gt hlt)
    _ = ‖x ^ 2‖ := max_eq_left hlt.le
    _ = ‖x‖ ^ 2 := norm_pow x 2

/-- In the infinity disk, the parameter `t=-x/y` lies in the maximal ideal. -/
theorem norm_parameter_lt_one
    (A B : ℤ_[37]) {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hx : 1 < ‖x‖) :
    ‖-x / y‖ < 1 := by
  have hEq := local_curve_equation A B hpoint
  have hinner := norm_inner_eq_norm_x_sq A B hx
  have hySq : ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
    calc
      ‖y‖ ^ 2 = ‖y ^ 2‖ := (norm_pow y 2).symm
      _ =
          ‖x * (x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37]))‖ := by
            rw [hEq]
      _ =
          ‖x‖ *
            ‖x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37])‖ :=
            norm_mul _ _
      _ = ‖x‖ ^ 3 := by rw [hinner]; ring
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0, norm_zero] at hySq
    have hx0 : 0 < ‖x‖ := lt_trans (by norm_num) hx
    nlinarith
  have htSq : ‖-x / y‖ ^ 2 = ‖x‖⁻¹ := by
    rw [norm_div, norm_neg, div_pow, hySq]
    field_simp [show ‖x‖ ≠ 0 by
      exact ne_of_gt (lt_trans (by norm_num) hx)]
  have hinv : ‖x‖⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ hx
  nlinarith [norm_nonneg (-x / y)]

/-- The reciprocal abscissa is also in the maximal ideal. -/
theorem norm_reciprocal_x_lt_one
    {x : ℚ_[37]} (hx : 1 < ‖x‖) :
    ‖x⁻¹‖ < 1 := by
  rw [norm_inv]
  exact inv_lt_one_of_one_lt₀ hx

/-- Exact relation between the two standard formal coordinates. -/
theorem reciprocal_eq_parameter_sq_mul
    (A B : ℤ_[37]) {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    x⁻¹ =
      (-x / y) ^ 2 *
        (1 + (A : ℚ_[37]) * x⁻¹ + (B : ℚ_[37]) * x⁻¹ ^ 2) := by
  have hEq := local_curve_equation A B hpoint
  field_simp [hx, hy]
  linear_combination hEq

private theorem toZMod_eq_zero_of_norm_lt_one
    (z : ℚ_[37]) (hz : ‖z‖ < 1) :
    PadicInt.toZMod (⟨z, hz.le⟩ : ℤ_[37]) = 0 := by
  let zInt : ℤ_[37] := ⟨z, hz.le⟩
  change PadicInt.toZMod zInt = 0
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
  apply (PadicInt.norm_lt_one_iff_dvd zInt).mp
  exact hz

/-- Actual integral formal parameters attached to any affine point reducing
to infinity, including their exact relation and reduction modulo 37. -/
theorem exists_integral_formal_parameters
    (A B : ℤ_[37]) [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hred :
      finiteReducePoint A B
        (.some x y hpoint) = none) :
    ∃ t r : ℤ_[37],
      (t : ℚ_[37]) = -x / y ∧
      (r : ℚ_[37]) = x⁻¹ ∧
      PadicInt.toZMod t = 0 ∧
      PadicInt.toZMod r = 0 ∧
      (r : ℚ_[37]) =
        (t : ℚ_[37]) ^ 2 *
          (1 + (A : ℚ_[37]) * (r : ℚ_[37]) +
            (B : ℚ_[37]) * (r : ℚ_[37]) ^ 2) := by
  have hxNorm := norm_x_gt_one_of_reduce_none A B hpoint hred
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, norm_zero] at hxNorm
    norm_num at hxNorm
  have htNorm := norm_parameter_lt_one A B hpoint hxNorm
  have hrNorm := norm_reciprocal_x_lt_one hxNorm
  have hEq := local_curve_equation A B hpoint
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0, zero_pow (by norm_num)] at hEq
    have hinnerZero :
        x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37]) = 0 :=
      (mul_eq_zero.mp hEq.symm).resolve_left hx
    have hinnerNorm := norm_inner_eq_norm_x_sq A B hxNorm
    rw [hinnerZero, norm_zero] at hinnerNorm
    have hx0 : 0 < ‖x‖ := lt_trans (by norm_num) hxNorm
    nlinarith
  let t : ℤ_[37] := ⟨-x / y, htNorm.le⟩
  let r : ℤ_[37] := ⟨x⁻¹, hrNorm.le⟩
  refine ⟨t, r, rfl, rfl, ?_, ?_, ?_⟩
  · exact toZMod_eq_zero_of_norm_lt_one (-x / y) htNorm
  · exact toZMod_eq_zero_of_norm_lt_one x⁻¹ hrNorm
  · exact reciprocal_eq_parameter_sq_mul A B hpoint hx hy

/-- Plus-prime specialization of the actual formal-parameter theorem. -/
theorem exists_plus_integral_formal_parameters
    {x y : ℚ_[37]}
    (hpoint :
      (localPadicCurve plusA plusB).toAffine.Nonsingular x y)
    (hred :
      finiteReducePoint plusA plusB
        (.some x y hpoint) = none) :
    ∃ t r : ℤ_[37],
      (t : ℚ_[37]) = -x / y ∧
      (r : ℚ_[37]) = x⁻¹ ∧
      PadicInt.toZMod t = 0 ∧
      PadicInt.toZMod r = 0 ∧
      (r : ℚ_[37]) =
        (t : ℚ_[37]) ^ 2 *
          (1 + (plusA : ℚ_[37]) * (r : ℚ_[37]) +
            (plusB : ℚ_[37]) * (r : ℚ_[37]) ^ 2) :=
  exists_integral_formal_parameters plusA plusB hpoint hred

/-- Minus-prime specialization of the actual formal-parameter theorem. -/
theorem exists_minus_integral_formal_parameters
    {x y : ℚ_[37]}
    (hpoint :
      (localPadicCurve minusA minusB).toAffine.Nonsingular x y)
    (hred :
      finiteReducePoint minusA minusB
        (.some x y hpoint) = none) :
    ∃ t r : ℤ_[37],
      (t : ℚ_[37]) = -x / y ∧
      (r : ℚ_[37]) = x⁻¹ ∧
      PadicInt.toZMod t = 0 ∧
      PadicInt.toZMod r = 0 ∧
      (r : ℚ_[37]) =
        (t : ℚ_[37]) ^ 2 *
          (1 + (minusA : ℚ_[37]) * (r : ℚ_[37]) +
            (minusB : ℚ_[37]) * (r : ℚ_[37]) ^ 2) :=
  exists_integral_formal_parameters minusA minusB hpoint hred

private def translationTailPolynomial
    (sign A B r t : ℚ_[37]) : ℚ_[37] :=
  (B + 4 * A + 12) - 4 * (A + 4) * r +
    sign * 4 * t * ((A + 4) + (B - 4) * r) +
    4 * t ^ 2 * (1 + A * r + B * r ^ 2)

private def translationTail
    (sign A B r t : ℚ_[37]) : ℚ_[37] :=
  (1 + A * r + B * r ^ 2) *
      translationTailPolynomial sign A B r t /
    (1 - 2 * r) ^ 2

private def translationNumeratorLocal
    (sign A B r t : ℚ_[37]) : ℚ_[37] :=
  (1 + A * r + B * r ^ 2) * (1 + sign * 2 * r * t) ^ 2 -
    r * (1 - 2 * r) ^ 2 * (A + 4 + sign * 4 * t) -
    (1 - 2 * r) ^ 2

private def integralTranslationTailPolynomial
    (sign A B r t : ℤ_[37]) : ℤ_[37] :=
  (B + 4 * A + 12) - 4 * (A + 4) * r +
    sign * 4 * t * ((A + 4) + (B - 4) * r) +
    4 * t ^ 2 * (1 + A * r + B * r ^ 2)

private theorem norm_translationTail_le_one
    (sign A B r t : ℤ_[37])
    (hr : ‖(r : ℚ_[37])‖ < 1) :
    ‖translationTail (sign : ℚ_[37]) (A : ℚ_[37])
        (B : ℚ_[37]) (r : ℚ_[37]) (t : ℚ_[37])‖ ≤ 1 := by
  let C : ℤ_[37] := 1 + A * r + B * r ^ 2
  let H : ℤ_[37] := integralTranslationTailPolynomial sign A B r t
  have hTwo : ‖(2 : ℚ_[37])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have hTwoR : ‖(2 : ℚ_[37]) * (r : ℚ_[37])‖ < 1 := by
    rw [norm_mul, hTwo, one_mul]
    exact hr
  have hDen :
      ‖(1 : ℚ_[37]) - 2 * (r : ℚ_[37])‖ = 1 := by
    calc
      ‖(1 : ℚ_[37]) - 2 * (r : ℚ_[37])‖ =
          ‖(1 : ℚ_[37]) + -(2 * (r : ℚ_[37]))‖ := by ring
      _ =
          max ‖(1 : ℚ_[37])‖ ‖-(2 * (r : ℚ_[37]))‖ :=
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
          (by
            rw [norm_one, norm_neg]
            exact ne_of_gt hTwoR)
      _ = 1 := by
        rw [norm_one, norm_neg, max_eq_left hTwoR.le]
  have hNumerator :
      ‖((C * H : ℤ_[37]) : ℚ_[37])‖ ≤ 1 :=
    (C * H).property
  change
    ‖((C : ℤ_[37]) : ℚ_[37]) *
        ((H : ℤ_[37]) : ℚ_[37]) /
      ((1 : ℚ_[37]) - 2 * (r : ℚ_[37])) ^ 2‖ ≤ 1
  rw [norm_div, norm_pow, hDen]
  norm_num
  change
    ‖((C : ℤ_[37]) : ℚ_[37]) * ((H : ℤ_[37]) : ℚ_[37])‖ ≤ 1
    at hNumerator
  rw [norm_mul] at hNumerator
  exact hNumerator

private theorem translationNumeratorLocal_factor
    (sign A B r t : ℚ_[37])
    (hsign : sign ^ 2 = 1) :
    translationNumeratorLocal sign A B r t =
      r ^ 2 * translationTailPolynomial sign A B r t := by
  simp only [translationNumeratorLocal, translationTailPolynomial]
  linear_combination
    4 * r ^ 2 * t ^ 2 * (1 + r * (A + B * r)) * hsign

private theorem secant_slope_eq_formal
    (x y sign : ℚ_[37]) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxTwo : x ≠ 2) :
    (sign * 2 - y) / (2 - x) =
      -(1 + sign * 2 * x⁻¹ * (-x / y)) /
        ((-x / y) * (1 - 2 * x⁻¹)) := by
  field_simp [hx, hy, hxTwo]
  ring

private theorem formal_translated_x_identity
    (sign A B r t : ℚ_[37])
    (hr : r = t ^ 2 * (1 + A * r + B * r ^ 2))
    (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hden : 1 - 2 * r ≠ 0)
    (hsign : sign ^ 2 = 1) :
    (-(1 + sign * 2 * r * t) / (t * (1 - 2 * r))) ^ 2 -
          A - 2 - r⁻¹ =
      2 + sign * 4 * t +
        t ^ 2 * translationTail sign A B r t := by
  have hfactor :=
    translationNumeratorLocal_factor sign A B r t hsign
  let C : ℚ_[37] := 1 + A * r + B * r ^ 2
  let q : ℚ_[37] := 1 + sign * 2 * r * t
  let d : ℚ_[37] := 1 - 2 * r
  have hd0 : d ≠ 0 := by simpa [d] using hden
  have hsquare :
      (-q / (t * d)) ^ 2 =
        C * q ^ 2 / (r * d ^ 2) := by
    dsimp [C, q, d]
    field_simp [hr0, ht0, hden]
    linear_combination (1 + sign * 2 * r * t) ^ 2 * hr
  have hremainder :
      (-q / (t * d)) ^ 2 - A - 2 - r⁻¹ -
            (2 + sign * 4 * t) =
        translationNumeratorLocal sign A B r t /
          (r * d ^ 2) := by
    rw [hsquare]
    change
      C * q ^ 2 / (r * d ^ 2) - A - 2 - r⁻¹ -
          (2 + sign * 4 * t) =
        (C * q ^ 2 - r * d ^ 2 * (A + 4 + sign * 4 * t) -
          d ^ 2) / (r * d ^ 2)
    field_simp [hr0, hd0]
    ring
  have htail :
      translationNumeratorLocal sign A B r t /
          (r * d ^ 2) =
        t ^ 2 * translationTail sign A B r t := by
    rw [hfactor]
    change
      r ^ 2 * translationTailPolynomial sign A B r t /
          (r * d ^ 2) =
        t ^ 2 *
          ((1 + A * r + B * r ^ 2) *
            translationTailPolynomial sign A B r t / d ^ 2)
    field_simp [hr0, hd0]
    linear_combination
      translationTailPolynomial sign A B r t * hr
  change
    (-q / (t * d)) ^ 2 - A - 2 - r⁻¹ =
      2 + sign * 4 * t + t ^ 2 * translationTail sign A B r t
  rw [show
    (-q / (t * d)) ^ 2 - A - 2 - r⁻¹ =
      ((-q / (t * d)) ^ 2 - A - 2 - r⁻¹ -
        (2 + sign * 4 * t)) + (2 + sign * 4 * t) by ring,
    hremainder, htail]
  ring

/-- The exact secant formula at `(2, 2 * sign)` has linear term
`4 * sign * t` on every actual point in the infinity disk.  The remainder
is `t²` times an actual 37-adic integer; no formal-group interface is assumed.
-/
theorem exists_integral_first_order_translation
    (sign A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (hsign : (sign : ℚ_[37]) ^ 2 = 1)
    {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hred :
      finiteReducePoint A B
        (.some x y hpoint) = none) :
    ∃ t r tail : ℤ_[37],
      (t : ℚ_[37]) = -x / y ∧
      (r : ℚ_[37]) = x⁻¹ ∧
      PadicInt.toZMod t = 0 ∧
      PadicInt.toZMod r = 0 ∧
      (r : ℚ_[37]) =
        (t : ℚ_[37]) ^ 2 *
          (1 + (A : ℚ_[37]) * (r : ℚ_[37]) +
            (B : ℚ_[37]) * (r : ℚ_[37]) ^ 2) ∧
      (((sign : ℚ_[37]) * 2 - y) / (2 - x)) ^ 2 -
            (A : ℚ_[37]) - 2 - x =
        2 + (sign : ℚ_[37]) * 4 * (t : ℚ_[37]) +
          (t : ℚ_[37]) ^ 2 * (tail : ℚ_[37]) := by
  have hxNorm := norm_x_gt_one_of_reduce_none A B hpoint hred
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, norm_zero] at hxNorm
    norm_num at hxNorm
  obtain ⟨t, r, ht, hrx, htRes, hrRes, hformal⟩ :=
    exists_integral_formal_parameters A B hpoint hred
  have hr0 : (r : ℚ_[37]) ≠ 0 := by
    rw [hrx]
    exact inv_ne_zero hx
  have hy : y ≠ 0 := by
    intro hy0
    have ht0 : (t : ℚ_[37]) = 0 := by
      rw [ht, hy0]
      simp
    have hrZero : (r : ℚ_[37]) = 0 := by
      rw [hformal, ht0]
      norm_num
    exact hr0 hrZero
  have ht0 : (t : ℚ_[37]) ≠ 0 := by
    rw [ht]
    exact div_ne_zero (neg_ne_zero.mpr hx) hy
  have hxTwo : x ≠ 2 := by
    intro hx2
    subst x
    have hTwo : ‖(2 : ℚ_[37])‖ = 1 :=
      Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
    rw [hTwo] at hxNorm
    exact (lt_irrefl 1) hxNorm
  have hrNorm : ‖(r : ℚ_[37])‖ < 1 := by
    rw [hrx]
    exact norm_reciprocal_x_lt_one hxNorm
  have hTwo : ‖(2 : ℚ_[37])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have hTwoR : ‖(2 : ℚ_[37]) * (r : ℚ_[37])‖ < 1 := by
    rw [norm_mul, hTwo, one_mul]
    exact hrNorm
  have hden : (1 : ℚ_[37]) - 2 * (r : ℚ_[37]) ≠ 0 := by
    intro hzero
    have hone : (1 : ℚ_[37]) = 2 * (r : ℚ_[37]) :=
      sub_eq_zero.mp hzero
    have hnorm := congrArg norm hone
    rw [norm_one] at hnorm
    nlinarith
  have htailNorm :=
    norm_translationTail_le_one sign A B r t hrNorm
  let tail : ℤ_[37] :=
    ⟨translationTail (sign : ℚ_[37]) (A : ℚ_[37])
      (B : ℚ_[37]) (r : ℚ_[37]) (t : ℚ_[37]), htailNorm⟩
  have hxFromR : x = ((r : ℚ_[37]))⁻¹ := by
    rw [hrx, inv_inv]
  have hidentity :=
    formal_translated_x_identity
      (sign : ℚ_[37]) (A : ℚ_[37]) (B : ℚ_[37])
      (r : ℚ_[37]) (t : ℚ_[37])
      hformal hr0 ht0 hden hsign
  refine ⟨t, r, tail, ht, hrx, htRes, hrRes, hformal, ?_⟩
  calc
    (((sign : ℚ_[37]) * 2 - y) / (2 - x)) ^ 2 -
          (A : ℚ_[37]) - 2 - x =
        (-(1 + (sign : ℚ_[37]) * 2 * (r : ℚ_[37]) *
              (t : ℚ_[37])) /
          ((t : ℚ_[37]) * (1 - 2 * (r : ℚ_[37])))) ^ 2 -
            (A : ℚ_[37]) - 2 - ((r : ℚ_[37]))⁻¹ := by
      rw [secant_slope_eq_formal x y (sign : ℚ_[37]) hx hy hxTwo,
        ← ht, ← hrx, hxFromR]
    _ =
        2 + (sign : ℚ_[37]) * 4 * (t : ℚ_[37]) +
          (t : ℚ_[37]) ^ 2 *
            translationTail (sign : ℚ_[37]) (A : ℚ_[37])
              (B : ℚ_[37]) (r : ℚ_[37]) (t : ℚ_[37]) :=
      hidentity
    _ =
        2 + (sign : ℚ_[37]) * 4 * (t : ℚ_[37]) +
          (t : ℚ_[37]) ^ 2 * (tail : ℚ_[37]) :=
      rfl

/-- First-order translation by the actual point `P=(2,2)`. -/
theorem exists_integral_translation_at_P
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hred :
      finiteReducePoint A B
        (.some x y hpoint) = none) :
    ∃ t r tail : ℤ_[37],
      (t : ℚ_[37]) = -x / y ∧
      (r : ℚ_[37]) = x⁻¹ ∧
      PadicInt.toZMod t = 0 ∧
      PadicInt.toZMod r = 0 ∧
      (r : ℚ_[37]) =
        (t : ℚ_[37]) ^ 2 *
          (1 + (A : ℚ_[37]) * (r : ℚ_[37]) +
            (B : ℚ_[37]) * (r : ℚ_[37]) ^ 2) ∧
      ((2 - y) / (2 - x)) ^ 2 - (A : ℚ_[37]) - 2 - x =
        2 + 4 * (t : ℚ_[37]) +
          (t : ℚ_[37]) ^ 2 * (tail : ℚ_[37]) := by
  simpa using
    exists_integral_first_order_translation (1 : ℤ_[37]) A B
      (by norm_num) hpoint hred

/-- First-order translation by the actual point `-P=(2,-2)`. -/
theorem exists_integral_translation_at_negP
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hred :
      finiteReducePoint A B
        (.some x y hpoint) = none) :
    ∃ t r tail : ℤ_[37],
      (t : ℚ_[37]) = -x / y ∧
      (r : ℚ_[37]) = x⁻¹ ∧
      PadicInt.toZMod t = 0 ∧
      PadicInt.toZMod r = 0 ∧
      (r : ℚ_[37]) =
        (t : ℚ_[37]) ^ 2 *
          (1 + (A : ℚ_[37]) * (r : ℚ_[37]) +
            (B : ℚ_[37]) * (r : ℚ_[37]) ^ 2) ∧
      ((-2 - y) / (2 - x)) ^ 2 - (A : ℚ_[37]) - 2 - x =
        2 - 4 * (t : ℚ_[37]) +
          (t : ℚ_[37]) ^ 2 * (tail : ℚ_[37]) := by
  obtain ⟨t, r, tail, ht, hr, htRes, hrRes, hformal, htranslate⟩ :=
    exists_integral_first_order_translation (-1 : ℤ_[37]) A B
      (by norm_num) hpoint hred
  refine ⟨t, r, tail, ht, hr, htRes, hrRes, hformal, ?_⟩
  norm_num at htranslate
  simpa [sub_eq_add_neg] using htranslate

end

end GaussianFormalLocal
end Cuboid2
