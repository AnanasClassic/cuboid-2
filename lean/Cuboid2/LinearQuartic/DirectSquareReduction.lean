import Cuboid2.LinearQuartic.ClassificationBridge

/-!
# Direct square-character reduction for cuboid parameters

For the public cuboid parameter `s = (p / q)²`, a rational-root argument
would additionally show that a rational root of the normalized quintic is a
signed square.  This file records the exact low-degree consequence of those
two square characters.

The quotient function `U(t)` satisfies

`N_U + 2 D_U = 4 (t + 1)⁵`.

Consequently, if `s` is a nonzero square and `U(t) = s + s⁻¹`, then

`t (t + 1) (t² + 6t + 1)`

is a square.  If `t` is respectively a square or the negative of a square,
this lands on one of two explicit genus-two covers.  All statements below
are polynomial identities or elementary field manipulations; no
rational-point classification is asserted here.
-/

namespace Cuboid2

noncomputable section

/-- The quadratic factor appearing in the denominator of the quotient
function `U(t)`. -/
def linearQuarticDirectH (t : ℚ) : ℚ :=
  t ^ 2 + 6 * t + 1

/-- The numerator of `U(t) + 2` factors as a fifth power. -/
theorem linearQuartic_U_plus_two_factor (t : ℚ) :
    linearQuarticUNumerator t + 2 * linearQuarticUDenominator t =
      4 * (t + 1) ^ 5 := by
  simp [linearQuarticUNumerator, linearQuarticUDenominator]
  ring

/-- The numerator of `U(t) - 2` is four times the quartic factor of the
linear--quartic genus-two curve. -/
theorem linearQuartic_U_minus_two_factor (t : ℚ) :
    linearQuarticUNumerator t - 2 * linearQuarticUDenominator t =
      4 * (t ^ 4 + 20 * t ^ 3 + 6 * t ^ 2 + 4 * t + 1) := by
  simp [linearQuarticUNumerator, linearQuarticUDenominator]
  ring

/--
If the parameter is a nonzero rational square and the cross-multiplied
quotient equation holds, then
`t (t + 1) (t² + 6t + 1)` is a rational square.
-/
theorem linearQuartic_squareParameter_character
    {s z t : ℚ} (hz : z ≠ 0) (hs : s = z ^ 2) (ht1 : t ≠ 1)
    (hcross :
      linearQuarticUNumerator t =
        linearQuarticReciprocal s * linearQuarticUDenominator t) :
    IsSquare (t * (t + 1) * linearQuarticDirectH t) := by
  have hspos : 0 < s := by
    rw [hs]
    positivity
  have hsplus : s + 1 ≠ 0 := by linarith
  have hscale : (s + 1) / z ≠ 0 := div_ne_zero hsplus hz
  have hrec :
      linearQuarticReciprocal s + 2 = ((s + 1) / z) ^ 2 := by
    simp [linearQuarticReciprocal, hs]
    field_simp [hz]
    ring
  have hfactor := linearQuartic_U_plus_two_factor t
  have hproduct :
      ((s + 1) / z) ^ 2 *
          (t * (t - 1) ^ 2 * linearQuarticDirectH t) =
        4 * (t + 1) ^ 5 := by
    calc
      ((s + 1) / z) ^ 2 *
          (t * (t - 1) ^ 2 * linearQuarticDirectH t) =
          (linearQuarticReciprocal s + 2) *
            linearQuarticUDenominator t := by
              rw [hrec]
              simp [linearQuarticUDenominator, linearQuarticDirectH]
      _ = linearQuarticUNumerator t +
          2 * linearQuarticUDenominator t := by rw [hcross]; ring
      _ = 4 * (t + 1) ^ 5 := hfactor
  have hproduct' :
      (s + 1) ^ 2 *
          (t * (t - 1) ^ 2 * linearQuarticDirectH t) =
        4 * z ^ 2 * (t + 1) ^ 5 := by
    calc
      (s + 1) ^ 2 *
          (t * (t - 1) ^ 2 * linearQuarticDirectH t) =
        z ^ 2 *
          (((s + 1) / z) ^ 2 *
            (t * (t - 1) ^ 2 * linearQuarticDirectH t)) := by
              field_simp [hz]
      _ = z ^ 2 * (4 * (t + 1) ^ 5) := by rw [hproduct]
      _ = 4 * z ^ 2 * (t + 1) ^ 5 := by ring
  refine
    ⟨2 * z * (t + 1) ^ 3 / ((s + 1) * (t - 1)), ?_⟩
  have hden : (s + 1) * (t - 1) ≠ 0 :=
    mul_ne_zero hsplus (sub_ne_zero.mpr ht1)
  field_simp [hden]
  calc
    t * (t + 1) * linearQuarticDirectH t *
        (s + 1) ^ 2 * (t - 1) ^ 2 =
      (t + 1) *
        ((s + 1) ^ 2 *
          (t * (t - 1) ^ 2 * linearQuarticDirectH t)) := by
            ring
    _ = (t + 1) * (4 * z ^ 2 * (t + 1) ^ 5) := by rw [hproduct']
    _ = (t + 1) ^ 6 * 2 ^ 2 * z ^ 2 := by ring

/-- On the square branch `t = u²`, the direct character is the explicit
even sextic `u⁶ + 7u⁴ + 7u² + 1`. -/
theorem linearQuartic_positiveSlope_genusTwo
    {t u : ℚ} (ht0 : t ≠ 0) (ht : t = u ^ 2)
    (hcharacter :
      IsSquare (t * (t + 1) * linearQuarticDirectH t)) :
    IsSquare ((u ^ 2 + 1) * (u ^ 4 + 6 * u ^ 2 + 1)) := by
  have hu : u ≠ 0 := by
    intro hu
    apply ht0
    simp [ht, hu]
  rcases hcharacter with ⟨k, hk⟩
  refine ⟨k / u, ?_⟩
  rw [ht] at hk
  simp [linearQuarticDirectH] at hk
  field_simp [hu]
  nlinarith [hk]

/-- On the negative-square branch `t = -u²`, the direct character is the
twisted sextic `u⁶ - 7u⁴ + 7u² - 1`. -/
theorem linearQuartic_negativeSlope_genusTwo
    {t u : ℚ} (ht0 : t ≠ 0) (ht : t = -(u ^ 2))
    (hcharacter :
      IsSquare (t * (t + 1) * linearQuarticDirectH t)) :
    IsSquare ((u ^ 2 - 1) * (u ^ 4 - 6 * u ^ 2 + 1)) := by
  have hu : u ≠ 0 := by
    intro hu
    apply ht0
    simp [ht, hu]
  rcases hcharacter with ⟨k, hk⟩
  refine ⟨k / u, ?_⟩
  rw [ht] at hk
  simp [linearQuarticDirectH] at hk
  field_simp [hu]
  nlinarith [hk]

/-- Expanded form of the positive signed-square cover. -/
theorem linearQuartic_positiveSlope_sextic_identity (u : ℚ) :
    (u ^ 2 + 1) * (u ^ 4 + 6 * u ^ 2 + 1) =
      u ^ 6 + 7 * u ^ 4 + 7 * u ^ 2 + 1 := by
  ring

/-- Expanded form of the negative signed-square cover. -/
theorem linearQuartic_negativeSlope_sextic_identity (u : ℚ) :
    (u ^ 2 - 1) * (u ^ 4 - 6 * u ^ 2 + 1) =
      u ^ 6 - 7 * u ^ 4 + 7 * u ^ 2 - 1 := by
  ring

end

end Cuboid2
