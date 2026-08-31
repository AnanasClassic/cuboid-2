import Cuboid2.LinearQuartic.Basic
import Cuboid2.Polynomial

/-!
# Exact root-to-curve algebra for the linear--quartic branch

A rational root `r` of `normalizedQuintic s` is first scaled to `y = r / s`.
The reciprocal coordinates

`U = s + s⁻¹`, `V = y + y⁻¹`

lie on the exact quotient polynomial below.  The inverse slope
`t = (V + 2) / (U - 2)` and a square identity for `V(t)` then produce a
rational point on the genus-two curve from `Basic.lean`.

All identities are checked here as rational polynomial identities.  No
resultant, factorization, or external computer-algebra conclusion is used as
a proof premise.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- The normalized rational-root equation `P_s(sy) / s³`. -/
def linearQuarticRootEquation (s y : ℚ) : ℚ :=
  s ^ 2 * y ^ 5 +
    (-2 * s ^ 3 - s ^ 2 + 6 * s) * y ^ 4 +
    (s ^ 4 - 14 * s ^ 3 + 4 * s ^ 2 + 10 * s + 1) * y ^ 3 +
    (-s ^ 4 - 10 * s ^ 3 - 4 * s ^ 2 + 14 * s - 1) * y ^ 2 +
    (-6 * s ^ 3 + s ^ 2 + 2 * s) * y -
    s ^ 2

/-- Evaluating the normalized quintic at `s*y` gives the exact scaled root
equation used by the reciprocal quotient. -/
theorem eval_normalizedQuintic_mul_eq_rootEquation (s y : ℚ) :
    eval (s * y) (normalizedQuintic s) =
      s ^ 3 * linearQuarticRootEquation s y := by
  simp [normalizedQuintic, normalizedQuinticLower, linearQuarticRootEquation]
  ring

/-- A rational root of `P_s` yields a zero of the scaled root equation. -/
theorem linearQuarticRootEquation_eq_zero_of_isRoot
    {s r : ℚ} (hs : s ≠ 0) (hr : IsRoot (normalizedQuintic s) r) :
    linearQuarticRootEquation s (r / s) = 0 := by
  have hscale : s * (r / s) = r := by field_simp
  have hid := eval_normalizedQuintic_mul_eq_rootEquation s (r / s)
  rw [hscale, IsRoot.def.mp hr] at hid
  exact (mul_eq_zero.mp hid.symm).resolve_left (pow_ne_zero 3 hs)

/-- The scaled root in the reciprocal coordinate is nonzero. -/
theorem linearQuarticRootEquation_right_ne_zero
    {s y : ℚ} (hs : s ≠ 0)
    (heq : linearQuarticRootEquation s y = 0) :
    y ≠ 0 := by
  intro hy
  subst y
  simp [linearQuarticRootEquation] at heq
  exact hs heq

/-- The root equation at `y=-1` is a nonzero scalar times the excluded
fourth power `(s-1)^4`. -/
theorem linearQuarticRootEquation_neg_one (s : ℚ) :
    linearQuarticRootEquation s (-1) = -2 * (s - 1) ^ 4 := by
  simp [linearQuarticRootEquation]
  ring

/-- Reciprocal coordinate `x + x⁻¹`. -/
def linearQuarticReciprocal (x : ℚ) : ℚ :=
  x + x⁻¹

/-- The exact reciprocal quotient of the normalized rational-root equation. -/
def linearQuarticReciprocalQuotient (U V : ℚ) : ℚ :=
  U ^ 4 * V - 2 * U ^ 4 +
    4 * U ^ 3 * V ^ 2 - 8 * U ^ 3 * V -
    10 * U ^ 2 * V ^ 3 - 108 * U ^ 2 * V ^ 2 -
    192 * U ^ 2 * V - 128 * U ^ 2 +
    4 * U * V ^ 4 - 8 * U * V ^ 3 +
    V ^ 5 - 2 * V ^ 4 + 64 * V ^ 3 +
    384 * V ^ 2 + 768 * V + 512

/-- The second factor produced when the reciprocal quotient is pulled back
to `(s,y)`.  The first factor is `linearQuarticRootEquation s y`. -/
def linearQuarticRootEquationMate (s y : ℚ) : ℚ :=
  s ^ 2 * y ^ 5 +
    (6 * s ^ 3 - s ^ 2 - 2 * s) * y ^ 4 +
    (s ^ 4 + 10 * s ^ 3 + 4 * s ^ 2 - 14 * s + 1) * y ^ 3 +
    (-s ^ 4 + 14 * s ^ 3 - 4 * s ^ 2 - 10 * s - 1) * y ^ 2 +
    (2 * s ^ 3 + s ^ 2 - 6 * s) * y -
    s ^ 2

/--
Substituting both reciprocal coordinates into the quotient gives the product
of the two reciprocal root equations.  This is the multiplication-back form
of the double resultant identity.
-/
theorem linearQuartic_reciprocalQuotient_identity
    {s y : ℚ} (hs : s ≠ 0) (hy : y ≠ 0) :
    s ^ 4 * y ^ 5 *
        linearQuarticReciprocalQuotient
          (linearQuarticReciprocal s) (linearQuarticReciprocal y) =
      linearQuarticRootEquation s y * linearQuarticRootEquationMate s y := by
  simp [linearQuarticReciprocalQuotient, linearQuarticReciprocal,
    linearQuarticRootEquation, linearQuarticRootEquationMate]
  field_simp [hs, hy]
  ring

/-- A scaled root therefore lies on the reciprocal quotient. -/
theorem linearQuartic_reciprocalQuotient_eq_zero
    {s y : ℚ} (hs : s ≠ 0) (hy : y ≠ 0)
    (heq : linearQuarticRootEquation s y = 0) :
    linearQuarticReciprocalQuotient
        (linearQuarticReciprocal s) (linearQuarticReciprocal y) = 0 := by
  have hid := linearQuartic_reciprocalQuotient_identity hs hy
  rw [heq] at hid
  simp only [zero_mul] at hid
  exact (mul_eq_zero.mp hid).resolve_left
    (mul_ne_zero (pow_ne_zero 4 hs) (pow_ne_zero 5 hy))

/-- The basic reciprocal square identity. -/
theorem linearQuartic_reciprocal_sq_sub_four
    {x : ℚ} (hx : x ≠ 0) :
    linearQuarticReciprocal x ^ 2 - 4 = (x - x⁻¹) ^ 2 := by
  simp [linearQuarticReciprocal]
  field_simp [hx]
  ring

/-- The denominator of the inverse slope is exactly the square character
associated to `s-1`. -/
theorem linearQuartic_reciprocal_sub_two
    {x : ℚ} (hx : x ≠ 0) :
    linearQuarticReciprocal x - 2 = (x - 1) ^ 2 / x := by
  simp [linearQuarticReciprocal]
  field_simp [hx]
  ring

/-- The numerator of the inverse slope is the corresponding square character
at `y=-1`. -/
theorem linearQuartic_reciprocal_add_two
    {x : ℚ} (hx : x ≠ 0) :
    linearQuarticReciprocal x + 2 = (x + 1) ^ 2 / x := by
  simp [linearQuarticReciprocal]
  field_simp [hx]
  ring

/-- For nonzero `x`, the reciprocal coordinate equals `2` only at `x=1`. -/
theorem linearQuartic_reciprocal_ne_two
    {x : ℚ} (hx : x ≠ 0) (hx1 : x ≠ 1) :
    linearQuarticReciprocal x ≠ 2 := by
  intro hrec
  have hsq : (x - 1) ^ 2 = 0 := by
    calc
      (x - 1) ^ 2 = x * (linearQuarticReciprocal x - 2) := by
        rw [linearQuartic_reciprocal_sub_two hx]
        field_simp [hx]
      _ = 0 := by rw [hrec]; ring
  have hxsub : x - 1 = 0 :=
    (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hsq
  exact hx1 (sub_eq_zero.mp hxsub)

/-- The inverse slope on the reciprocal quotient. -/
def linearQuarticSlope (U V : ℚ) : ℚ :=
  (V + 2) / (U - 2)

/-- Cross-multiplied defining equation of the inverse slope. -/
theorem linearQuarticSlope_cross
    {U V : ℚ} (hU : U ≠ 2) :
    (U - 2) * linearQuarticSlope U V = V + 2 := by
  unfold linearQuarticSlope
  field_simp [sub_ne_zero.mpr hU]

/-- The inverse slope written directly in the original reciprocal variables. -/
theorem linearQuarticSlope_reciprocal
    {s y : ℚ} (hs : s ≠ 0) (hy : y ≠ 0) (hs1 : s ≠ 1) :
    linearQuarticSlope
        (linearQuarticReciprocal s) (linearQuarticReciprocal y) =
      s * (y + 1) ^ 2 / (y * (s - 1) ^ 2) := by
  unfold linearQuarticSlope
  rw [linearQuartic_reciprocal_add_two hy,
    linearQuartic_reciprocal_sub_two hs]
  field_simp [hs, hy, sub_ne_zero.mpr hs1,
    pow_ne_zero 2 (sub_ne_zero.mpr hs1)]

/-- Numerator of the rational function `U(t)`. -/
def linearQuarticUNumerator (t : ℚ) : ℚ :=
  2 * (t ^ 5 + 6 * t ^ 4 + 30 * t ^ 3 + 16 * t ^ 2 + 9 * t + 2)

/-- Denominator of the rational function `U(t)`. -/
def linearQuarticUDenominator (t : ℚ) : ℚ :=
  t * (t - 1) ^ 2 * (t ^ 2 + 6 * t + 1)

/-- Numerator of the rational function `V(t)`. -/
def linearQuarticVNumerator (t : ℚ) : ℚ :=
  2 * (t ^ 4 + 36 * t ^ 3 + 22 * t ^ 2 + 4 * t + 1)

/-- Denominator of the rational function `V(t)`. -/
def linearQuarticVDenominator (t : ℚ) : ℚ :=
  (t - 1) ^ 2 * (t ^ 2 + 6 * t + 1)

/-- The inverse slope recovers `U(t)=U` in cross-multiplied form. -/
theorem linearQuartic_inverseSlope_U
    {U V : ℚ} (hU : U ≠ 2) :
    (U - 2) ^ 4 *
        (linearQuarticUNumerator (linearQuarticSlope U V) -
          U * linearQuarticUDenominator (linearQuarticSlope U V)) =
      -linearQuarticReciprocalQuotient U V := by
  simp [linearQuarticSlope, linearQuarticUNumerator,
    linearQuarticUDenominator, linearQuarticReciprocalQuotient]
  field_simp [sub_ne_zero.mpr hU]
  ring

/-- The inverse slope recovers `V(t)=V` in cross-multiplied form. -/
theorem linearQuartic_inverseSlope_V
    {U V : ℚ} (hU : U ≠ 2) :
    (U - 2) ^ 4 *
        (linearQuarticVNumerator (linearQuarticSlope U V) -
          V * linearQuarticVDenominator (linearQuarticSlope U V)) =
      -linearQuarticReciprocalQuotient U V := by
  simp [linearQuarticSlope, linearQuarticVNumerator,
    linearQuarticVDenominator, linearQuarticReciprocalQuotient]
  field_simp [sub_ne_zero.mpr hU]
  ring

/-- The `V(t)` square identity in denominator-free form. -/
theorem linearQuartic_V_square_identity (t : ℚ) :
    linearQuarticVNumerator t ^ 2 -
        4 * linearQuarticVDenominator t ^ 2 =
      256 * t ^ 2 * linearQuarticCurveRhs t := by
  simp [linearQuarticVNumerator, linearQuarticVDenominator,
    linearQuarticCurveRhs]
  ring

/-- The remaining quadratic denominator in the parametrization has no
rational zero; its completed square would make `8` a rational square. -/
theorem linearQuartic_remainingDenominator_ne_zero (t : ℚ) :
    t ^ 2 + 6 * t + 1 ≠ 0 := by
  intro hzero
  have hsquare : IsSquare (8 : ℚ) := by
    refine ⟨t + 3, ?_⟩
    nlinarith
  have : ¬ IsSquare (8 : ℚ) := by norm_num
  exact this hsquare

/-- The ordinate obtained from a reciprocal value `y`, a slope `t`, and the
cross-multiplied `V(t)=y+y⁻¹` identity lies on the genus-two curve. -/
theorem linearQuartic_curve_identity_of_V
    {y t : ℚ} (hy : y ≠ 0) (ht : t ≠ 0)
    (hV :
      linearQuarticVNumerator t =
        linearQuarticReciprocal y * linearQuarticVDenominator t) :
    (((y - y⁻¹) * linearQuarticVDenominator t) / (16 * t)) ^ 2 =
      linearQuarticCurveRhs t := by
  have hrec := linearQuartic_reciprocal_sq_sub_four hy
  have hsquare := linearQuartic_V_square_identity t
  have hnum :
      (y - y⁻¹) ^ 2 * linearQuarticVDenominator t ^ 2 =
        linearQuarticVNumerator t ^ 2 -
          4 * linearQuarticVDenominator t ^ 2 := by
    rw [← hrec, hV]
    ring
  rw [hsquare] at hnum
  calc
    (((y - y⁻¹) * linearQuarticVDenominator t) / (16 * t)) ^ 2 =
        ((y - y⁻¹) ^ 2 * linearQuarticVDenominator t ^ 2) /
          (256 * t ^ 2) := by ring
    _ = (256 * t ^ 2 * linearQuarticCurveRhs t) / (256 * t ^ 2) := by
      rw [hnum]
    _ = linearQuarticCurveRhs t := by field_simp [ht]

/-- The inverse slope attached to an admissible scaled root is nonzero. -/
theorem linearQuartic_rootSlope_ne_zero
    {s y : ℚ} (hs : s ≠ 0) (hs1 : s ≠ 1)
    (hy : y ≠ 0) (heq : linearQuarticRootEquation s y = 0) :
    linearQuarticSlope
        (linearQuarticReciprocal s) (linearQuarticReciprocal y) ≠ 0 := by
  let U := linearQuarticReciprocal s
  let V := linearQuarticReciprocal y
  have hU : U ≠ 2 := by
    exact linearQuartic_reciprocal_ne_two hs hs1
  intro ht
  have hslope := linearQuarticSlope_cross (U := U) (V := V) hU
  rw [ht] at hslope
  have hVplus : V + 2 = 0 := by simpa using hslope.symm
  have hyplus : (y + 1) ^ 2 = 0 := by
    calc
      (y + 1) ^ 2 = y * (linearQuarticReciprocal y + 2) := by
        rw [linearQuartic_reciprocal_add_two hy]
        field_simp [hy]
      _ = 0 := by simpa [V] using congrArg (fun z : ℚ => y * z) hVplus
  have hyneg : y = -1 := by
    have : y + 1 = 0 :=
      (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hyplus
    linarith
  have hsPower : (s - 1) ^ 4 = 0 := by
    rw [hyneg, linearQuarticRootEquation_neg_one] at heq
    exact (mul_eq_zero.mp heq).resolve_left (by norm_num)
  have hsEq : s = 1 := by
    have : s - 1 = 0 :=
      (pow_eq_zero_iff (by norm_num : 4 ≠ 0)).mp hsPower
    linarith
  exact hs1 hsEq

/--
The exact forward map from an admissible rational root of `P_s` to an affine
rational point on the genus-two curve.
-/
def normalizedRootToLinearQuartic
    {s r : ℚ} (hs : 0 < s) (hs1 : s ≠ 1)
    (hr : IsRoot (normalizedQuintic s) r) :
    LinearQuarticAffinePoint := by
  let y : ℚ := r / s
  let U : ℚ := linearQuarticReciprocal s
  let V : ℚ := linearQuarticReciprocal y
  let t : ℚ := linearQuarticSlope U V
  have hs0 : s ≠ 0 := ne_of_gt hs
  have heq : linearQuarticRootEquation s y = 0 := by
    exact linearQuarticRootEquation_eq_zero_of_isRoot hs0 hr
  have hy : y ≠ 0 :=
    linearQuarticRootEquation_right_ne_zero hs0 heq
  have hU : U ≠ 2 := by
    exact linearQuartic_reciprocal_ne_two hs0 hs1
  have hQ : linearQuarticReciprocalQuotient U V = 0 := by
    exact linearQuartic_reciprocalQuotient_eq_zero hs0 hy heq
  have hV :
      linearQuarticVNumerator t =
        V * linearQuarticVDenominator t := by
    have hinv := linearQuartic_inverseSlope_V (U := U) (V := V) hU
    rw [hQ] at hinv
    have hdiff :
        linearQuarticVNumerator t -
            V * linearQuarticVDenominator t = 0 :=
      (mul_eq_zero.mp hinv).resolve_left
        (pow_ne_zero 4 (sub_ne_zero.mpr hU))
    exact sub_eq_zero.mp hdiff
  have ht : t ≠ 0 := by
    exact linearQuartic_rootSlope_ne_zero hs0 hs1 hy heq
  exact
    { t := t
      w := ((y - y⁻¹) * linearQuarticVDenominator t) / (16 * t)
      onCurve := by
        exact linearQuartic_curve_identity_of_V hy ht (by simpa [V] using hV) }

@[simp] theorem normalizedRootToLinearQuartic_t
    {s r : ℚ} (hs : 0 < s) (hs1 : s ≠ 1)
    (hr : IsRoot (normalizedQuintic s) r) :
    (normalizedRootToLinearQuartic hs hs1 hr).t =
      linearQuarticSlope
        (linearQuarticReciprocal s)
        (linearQuarticReciprocal (r / s)) := by
  rfl

end

end Cuboid2
