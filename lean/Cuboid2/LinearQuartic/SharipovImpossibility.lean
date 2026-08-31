import Cuboid2.LinearQuartic.SignedSquareCovers

/-!
# Completion of the Sharipov linear--quartic branch

For the square parameter `s=(p/q)²`, every rational root has signed-square
class.  The inverse-slope map preserves that class.  Its positive branch is
excluded by the elementary Fermat cover, while its negative branch is
excluded by the joint direct/curve cover modulo three.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- If both the parameter and a normalized-quintic root have square class,
the abscissa produced by the root-to-curve map has the root's signed-square
class. -/
theorem normalizedRootToLinearQuartic_signedSquare_t
    {s r z u : ℚ} {ε : PhysicalSign}
    (hs : 0 < s) (hs1 : s ≠ 1)
    (hr : IsRoot (normalizedQuintic s) r)
    (hz : z ≠ 0) (hsz : s = z ^ 2)
    (hrsq : r = ε.value * u ^ 2) :
    ∃ v : ℚ,
      (normalizedRootToLinearQuartic hs hs1 hr).t =
        ε.value * v ^ 2 := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have heq :
      linearQuarticRootEquation s (r / s) = 0 :=
    linearQuarticRootEquation_eq_zero_of_isRoot hs0 hr
  have hy0 : r / s ≠ 0 :=
    linearQuarticRootEquation_right_ne_zero hs0 heq
  have hu0 : u ≠ 0 := by
    intro hzero
    apply hy0
    rw [hrsq, hzero]
    simp
  rw [normalizedRootToLinearQuartic_t,
    linearQuarticSlope_reciprocal hs0 hy0 hs1]
  refine
    ⟨z ^ 2 * (r / s + 1) / (u * (s - 1)), ?_⟩
  cases ε <;>
    simp only [PhysicalSign.value_positive, PhysicalSign.value_negative] at hrsq ⊢ <;>
    rw [hsz, hrsq] <;>
    field_simp [hz, hu0]

/-- The linear-factor case is impossible at every admissible Sharipov
parameter. -/
theorem linear_quartic_impossible_sharipov
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hcop : p.Coprime q) (hne : p ≠ q) :
    ¬ LinearQuarticCase (sharipovParameter p q) := by
  rintro ⟨r, hr⟩
  let s : ℚ := sharipovParameter p q
  let z : ℚ := (p : ℚ) / (q : ℚ)
  have hs : 0 < s := sharipovParameter_pos hp hq
  have hs1 : s ≠ 1 := sharipovParameter_ne_one hp hq hne
  have hz : z ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast Nat.ne_of_gt hp
    · exact_mod_cast Nat.ne_of_gt hq
  have hsz : s = z ^ 2 := rfl
  obtain ⟨ε, u, hrsq⟩ :=
    normalizedQuintic_root_signedSquare_sharipov hp hq hcop hr
  let point : LinearQuarticAffinePoint :=
    normalizedRootToLinearQuartic hs hs1 hr
  have hcross :
      linearQuarticUNumerator point.t =
        linearQuarticReciprocal s *
          linearQuarticUDenominator point.t := by
    simpa [point] using
      normalizedRootToLinearQuartic_U_cross hs hs1 hr
  have ht0 : point.t ≠ 0 := by
    intro ht
    rw [ht] at hcross
    exact linearQuartic_no_U_lift_at_zero hcross
  have ht1 : point.t ≠ 1 := by
    intro ht
    rw [ht] at hcross
    exact linearQuartic_no_U_lift_at_one hcross
  have hcharacter :
      IsSquare
        (point.t * (point.t + 1) *
          linearQuarticDirectH point.t) :=
    linearQuartic_squareParameter_character hz hsz ht1 hcross
  obtain ⟨v, htSigned⟩ :=
    normalizedRootToLinearQuartic_signedSquare_t
      hs hs1 hr hz hsz hrsq
  cases ε with
  | positive =>
      have ht : point.t = v ^ 2 := by
        simpa only [PhysicalSign.value_positive, one_mul] using htSigned
      have hcover :=
        linearQuartic_positiveSlope_genusTwo ht0 ht hcharacter
      rcases positiveSlope_cover_classification hcover with hv0 | hv1
      · exact ht0 (by simp [ht, hv0])
      · exact ht1 (by simpa [ht] using hv1)
  | negative =>
      have ht : point.t = -(v ^ 2) := by
        simpa only [PhysicalSign.value_negative, neg_one_mul] using htSigned
      have hdirect :=
        linearQuartic_negativeSlope_genusTwo ht0 ht hcharacter
      have hcurve :
          IsSquare
            ((1 - v ^ 2) *
              (v ^ 8 - 20 * v ^ 6 + 6 * v ^ 4 -
                4 * v ^ 2 + 1)) := by
        refine ⟨point.w, ?_⟩
        calc
          (1 - v ^ 2) *
                (v ^ 8 - 20 * v ^ 6 + 6 * v ^ 4 -
                  4 * v ^ 2 + 1) =
              linearQuarticCurveRhs (-(v ^ 2)) := by
                simp [linearQuarticCurveRhs]
                ring
          _ = linearQuarticCurveRhs point.t := by rw [ht]
          _ = point.w ^ 2 := point.onCurve.symm
          _ = point.w * point.w := by ring
      have hv1 :=
        negativeSlope_cover_pair_classification hdirect hcurve
      have htneg : point.t = -1 := by
        rw [ht, hv1]
      rw [htneg] at hcross
      have hsneg :=
        linearQuartic_U_lift_at_neg_one (ne_of_gt hs) hcross
      linarith

end

end Cuboid2
