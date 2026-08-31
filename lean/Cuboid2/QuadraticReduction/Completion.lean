import Cuboid2.QuadraticReduction.Characters
import Cuboid2.QuadraticReduction.ValuationDescent
import Cuboid2.DPlus.GlobalBridge

/-!
# Final regular-locus reduction for the quadratic--cubic case

This module keeps the octic witness produced by the common-character
valuation descent.  Retaining that witness is essential: the affine
square-abscissa classification on `D+` contains three points, whereas the
octic cover has only the four lifts above `a = 1`.
-/

namespace Cuboid2

noncomputable section

/--
The common-character relation reaches the positive octic cover, and the
elliptic slope is exactly twice the square of its octic coordinate.
-/
theorem e1_hk_to_octic
    {k h z : ℚ} (hk : k ≠ 0) (hh : h ≠ 0)
    (hz : z ^ 2 = 2 * k * h)
    (hrel : e1HKRelation k h = 0) :
    ∃ Q : OcticPoint, k = 2 * Q.u ^ 2 := by
  rcases e1_hk_signed_squareclasses hk hh hz hrel with
    ⟨ε, u, v, hu, hv, hkSquare, hhSquare⟩
  cases ε with
  | positive =>
      have hkPos : k = 2 * u ^ 2 := by
        simpa [PhysicalSign.value] using hkSquare
      have hhPos : h = v ^ 2 := by
        simpa [PhysicalSign.value] using hhSquare
      let r : ℚ := v ^ 2 - 2 * u ^ 4 - 1
      have hr : r ^ 2 = octicRhs u := by
        unfold e1HKRelation at hrel
        rw [hkPos, hhPos] at hrel
        simp only [octicRhs]
        dsimp [r]
        nlinarith
      exact ⟨⟨u, r, hr⟩, hkPos⟩
  | negative =>
      have hkNeg : k = -2 * u ^ 2 := by
        simpa [PhysicalSign.value] using hkSquare
      have hhNeg : h = -v ^ 2 := by
        simpa [PhysicalSign.value] using hhSquare
      exfalso
      apply e1_negative_squareclass_impossible (u ^ 2) v
      simpa [hkNeg, hhNeg] using hrel

/--
On the regular part of the translated elliptic quotient, the nonzero common
square character is incompatible with the checked square-abscissa
classification on `D+`.
-/
theorem regular_e1_common_character_impossible
    (hclass : DPlusSquareAbscissaClassified)
    (P : E1AffinePoint)
    (hX : P.X ≠ 0)
    (hD0 : e1D0 P.X P.Y ≠ 0)
    (hX3 : P.X ≠ 3)
    (hL : e1L P.X P.Y ≠ 0)
    (hg : e1G P.X P.Y ≠ 0)
    (hsquare :
      IsSquare (1 - e1U P.X P.Y * e1V P.X P.Y))
    (hne : 1 - e1U P.X P.Y * e1V P.X P.Y ≠ 0) :
    False := by
  rcases e1_two_k_h_isSquare P hX hD0 hX3 hL hg hsquare with
    ⟨z, hz⟩
  let k : ℚ := (P.Y + 2) / P.X
  let h : ℚ := P.X + 1
  have hcharacter := e1_common_character P hD0 hX3
  have hM := e1_M_eq_L_mul_k P hX
  have hk : k ≠ 0 := by
    intro hk0
    apply hne
    rw [hcharacter]
    unfold e1F
    rw [hM]
    dsimp [k, h] at hk0 ⊢
    rw [hk0]
    ring
  have hh : h ≠ 0 := by
    intro hh0
    apply hne
    rw [hcharacter]
    unfold e1F
    dsimp [h] at hh0 ⊢
    rw [hh0]
    ring
  have hz' : z ^ 2 = 2 * k * h := by
    simpa [k, h, pow_two] using hz.symm
  have hrel : e1HKRelation k h = 0 := by
    simpa [k, h] using e1_hk_relation P hX
  rcases e1_hk_to_octic hk hh hz' hrel with ⟨Q, hkQ⟩
  have hQclass :=
    octic_classified_of_dplus_classified hclass Q
  have hu : Q.u = 1 ∨ Q.u = -1 := by
    rcases hQclass with hpp | hpm | hmp | hmm
    · exact Or.inl hpp.1
    · exact Or.inl hpm.1
    · exact Or.inr hmp.1
    · exact Or.inr hmm.1
  have hk2 : k = 2 := by
    rcases hu with hu | hu <;> rw [hkQ, hu] <;> norm_num
  have hhCases : h = 2 ∨ h = 4 := by
    unfold e1HKRelation at hrel
    rw [hk2] at hrel
    have hfactor : (h - 2) * (h - 4) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with h2 | h4
    · exact Or.inl (sub_eq_zero.mp h2)
    · exact Or.inr (sub_eq_zero.mp h4)
  rcases hhCases with hh2 | hh4
  · have hPX : P.X = 1 := by
      dsimp [h] at hh2
      linarith
    have hPY : P.Y = 0 := by
      dsimp [k] at hk2
      rw [hPX] at hk2
      norm_num at hk2 ⊢
      linarith
    apply hD0
    rw [hPX, hPY]
    norm_num [e1D0]
  · apply hX3
    dsimp [h] at hh4
    linarith

end

end Cuboid2
