import Cuboid2.Factorization
import Cuboid2.LinearQuartic.KnownPoints
import Cuboid2.LinearQuartic.RootMap

/-!
# Elementary completion of the linear--quartic branch

This file isolates the sole arithmetic-geometric input as
`LinearQuarticRationalPointClassification`.  Assuming that exact
classification, all inverse images of the six known points are checked here
by rational identities:

* the root-to-curve map is affine, so it cannot be the point at infinity;
* `t = -1` forces `s = -1`;
* `t = 0` and `t = 1` are genuine poles of `U(t)`.

Thus no positive `s ≠ 1` can give a rational root of the normalized quintic.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- The reciprocal value `2` has the unique nonzero rational lift `s=1`.
This is the exceptional lift attached to the point at infinity. -/
theorem linearQuartic_reciprocal_eq_two
    {s : ℚ} (hs : s ≠ 0)
    (hrec : linearQuarticReciprocal s = 2) :
    s = 1 := by
  by_contra hs1
  exact linearQuartic_reciprocal_ne_two hs hs1 hrec

/-- The reciprocal value `-2` has the unique nonzero rational lift `s=-1`. -/
theorem linearQuartic_reciprocal_eq_neg_two
    {s : ℚ} (hs : s ≠ 0)
    (hrec : linearQuarticReciprocal s = -2) :
    s = -1 := by
  simp [linearQuarticReciprocal] at hrec
  field_simp [hs] at hrec
  nlinarith [sq_nonneg (s + 1)]

/--
Besides producing a curve point, the root-to-curve map retains the exact
cross-multiplied identity `U(t)=s+s⁻¹`.
-/
theorem normalizedRootToLinearQuartic_U_cross
    {s r : ℚ} (hs : 0 < s) (hs1 : s ≠ 1)
    (hr : IsRoot (normalizedQuintic s) r) :
    linearQuarticUNumerator (normalizedRootToLinearQuartic hs hs1 hr).t =
      linearQuarticReciprocal s *
        linearQuarticUDenominator
          (normalizedRootToLinearQuartic hs hs1 hr).t := by
  let y : ℚ := r / s
  let U : ℚ := linearQuarticReciprocal s
  let V : ℚ := linearQuarticReciprocal y
  have hs0 : s ≠ 0 := ne_of_gt hs
  have heq : linearQuarticRootEquation s y = 0 := by
    exact linearQuarticRootEquation_eq_zero_of_isRoot hs0 hr
  have hy : y ≠ 0 :=
    linearQuarticRootEquation_right_ne_zero hs0 heq
  have hU : U ≠ 2 := by
    exact linearQuartic_reciprocal_ne_two hs0 hs1
  have hQ : linearQuarticReciprocalQuotient U V = 0 := by
    exact linearQuartic_reciprocalQuotient_eq_zero hs0 hy heq
  have hinverse := linearQuartic_inverseSlope_U (U := U) (V := V) hU
  have hproduct :
      (U - 2) ^ 4 *
          (linearQuarticUNumerator (linearQuarticSlope U V) -
            U * linearQuarticUDenominator (linearQuarticSlope U V)) = 0 := by
    simpa [hQ] using hinverse
  have hdifference :
      linearQuarticUNumerator (linearQuarticSlope U V) -
          U * linearQuarticUDenominator (linearQuarticSlope U V) = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left
      (pow_ne_zero 4 (sub_ne_zero.mpr hU))
  have hcross :
      linearQuarticUNumerator (linearQuarticSlope U V) =
        U * linearQuarticUDenominator (linearQuarticSlope U V) :=
    sub_eq_zero.mp hdifference
  rw [normalizedRootToLinearQuartic_t]
  simpa [U, V, y] using hcross

/-- At `t=-1`, the exact cross-multiplied quotient equation forces `s=-1`. -/
theorem linearQuartic_U_lift_at_neg_one
    {s : ℚ} (hs : s ≠ 0)
    (hcross :
      linearQuarticUNumerator (-1) =
        linearQuarticReciprocal s * linearQuarticUDenominator (-1)) :
    s = -1 := by
  have hrec : linearQuarticReciprocal s = -2 := by
    norm_num [linearQuarticUNumerator, linearQuarticUDenominator] at hcross ⊢
    linarith
  exact linearQuartic_reciprocal_eq_neg_two hs hrec

/-- `t=0` is a genuine pole of `U(t)`, so it has no finite quotient lift. -/
theorem linearQuartic_no_U_lift_at_zero
    {U : ℚ}
    (hcross :
      linearQuarticUNumerator 0 =
        U * linearQuarticUDenominator 0) :
    False := by
  norm_num [linearQuarticUNumerator, linearQuarticUDenominator] at hcross

/-- `t=1` is a genuine pole of `U(t)`, so it has no finite quotient lift. -/
theorem linearQuartic_no_U_lift_at_one
    {U : ℚ}
    (hcross :
      linearQuarticUNumerator 1 =
        U * linearQuarticUDenominator 1) :
    False := by
  norm_num [linearQuarticUNumerator, linearQuarticUDenominator] at hcross

/--
The six-point classification leaves only the three affine abscissas
`-1`, `0`, and `1`.
-/
theorem linearQuartic_affine_abscissa_of_classification
    (hclass : LinearQuarticRationalPointClassification)
    (point : LinearQuarticAffinePoint) :
    point.t = -1 ∨ point.t = 0 ∨ point.t = 1 := by
  have hmem := hclass (.affine point)
  rw [mem_knownLinearQuarticRationalPoints_iff] at hmem
  rcases hmem with hinfinity | hneg | hzeroPlus | hzeroMinus | honePlus | honeMinus
  · change LinearQuarticRationalPoint.affine point =
      LinearQuarticRationalPoint.infinity at hinfinity
    cases hinfinity
  · change LinearQuarticRationalPoint.affine point =
      LinearQuarticRationalPoint.affine linearQuarticNegOne at hneg
    injection hneg with hpoint
    exact Or.inl (by
      simpa [linearQuarticNegOne] using
        congrArg (fun p : LinearQuarticAffinePoint => p.t) hpoint)
  · change LinearQuarticRationalPoint.affine point =
      LinearQuarticRationalPoint.affine linearQuarticZeroPlus at hzeroPlus
    injection hzeroPlus with hpoint
    exact Or.inr (Or.inl (by
      simpa [linearQuarticZeroPlus] using
        congrArg (fun p : LinearQuarticAffinePoint => p.t) hpoint))
  · change LinearQuarticRationalPoint.affine point =
      LinearQuarticRationalPoint.affine linearQuarticZeroMinus at hzeroMinus
    injection hzeroMinus with hpoint
    exact Or.inr (Or.inl (by
      simpa [linearQuarticZeroMinus] using
        congrArg (fun p : LinearQuarticAffinePoint => p.t) hpoint))
  · change LinearQuarticRationalPoint.affine point =
      LinearQuarticRationalPoint.affine linearQuarticOnePlus at honePlus
    injection honePlus with hpoint
    exact Or.inr (Or.inr (by
      simpa [linearQuarticOnePlus] using
        congrArg (fun p : LinearQuarticAffinePoint => p.t) hpoint))
  · change LinearQuarticRationalPoint.affine point =
      LinearQuarticRationalPoint.affine linearQuarticOneMinus at honeMinus
    injection honeMinus with hpoint
    exact Or.inr (Or.inr (by
      simpa [linearQuarticOneMinus] using
        congrArg (fun p : LinearQuarticAffinePoint => p.t) hpoint))

/--
Once the exact six-point classification is available, the linear-factor case
is impossible for every admissible parameter.
-/
theorem linearQuarticCase_impossible_of_point_classification
    (hclass : LinearQuarticRationalPointClassification)
    {s : ℚ} (hs : 0 < s) (hs1 : s ≠ 1) :
    ¬ LinearQuarticCase s := by
  rintro ⟨r, hr⟩
  let point : LinearQuarticAffinePoint :=
    normalizedRootToLinearQuartic hs hs1 hr
  have hcross :
      linearQuarticUNumerator point.t =
        linearQuarticReciprocal s * linearQuarticUDenominator point.t := by
    simpa [point] using
      normalizedRootToLinearQuartic_U_cross hs hs1 hr
  rcases linearQuartic_affine_abscissa_of_classification hclass point with
    ht | ht | ht
  · rw [ht] at hcross
    have hsneg := linearQuartic_U_lift_at_neg_one (ne_of_gt hs) hcross
    linarith
  · rw [ht] at hcross
    exact linearQuartic_no_U_lift_at_zero hcross
  · rw [ht] at hcross
    exact linearQuartic_no_U_lift_at_one hcross

end

end Cuboid2
