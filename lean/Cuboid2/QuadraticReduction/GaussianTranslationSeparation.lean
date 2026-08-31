import Cuboid2.QuadraticReduction.GaussianFormalKernelDisk

/-!
# Separation of the two split-37 translation traces

The actual translation formulas at `P = (2,2)` and `-P = (2,-2)` have the
shape

`2 + sign * 4 * t + t² * tail`.

When two parameters lie in the maximal ideal, have the same positive norm
`r`, and their difference still has norm `r`, the linear parts of their
translation traces differ by an element of norm exactly `r`.  The difference
of the two quadratic tails has norm at most `r² < r`, so the traces cannot be
equal.
-/

namespace Cuboid2
namespace GaussianTranslationSeparation

noncomputable section

open GaussianFormalKernelDisk

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

private theorem norm_four_padic :
    ‖(4 : ℚ_[37])‖ = 1 :=
  Padic.norm_natCast_eq_one_iff.mpr (by norm_num)

/-- Generic split-37 separation lemma.  The coefficient `sign` may be any
37-adic unit; the applications below use `+1` and `-1`. -/
theorem firstOrderTranslation_eq_impossible
    (sign t₁ t₂ tail₁ tail₂ : ℤ_[37])
    (r : ℝ)
    (hsign : ‖(sign : ℚ_[37])‖ = 1)
    (ht₁Red : PadicInt.toZMod t₁ = 0)
    (ht₂Red : PadicInt.toZMod t₂ = 0)
    (ht₁Norm : ‖(t₁ : ℚ_[37])‖ = r)
    (ht₂Norm : ‖(t₂ : ℚ_[37])‖ = r)
    (hsep :
      ‖(t₁ : ℚ_[37]) - (t₂ : ℚ_[37])‖ = r)
    (hr : 0 < r)
    (heq :
      2 + (sign : ℚ_[37]) * 4 * (t₁ : ℚ_[37]) +
          (t₁ : ℚ_[37]) ^ 2 * (tail₁ : ℚ_[37]) =
        2 + (sign : ℚ_[37]) * 4 * (t₂ : ℚ_[37]) +
          (t₂ : ℚ_[37]) ^ 2 * (tail₂ : ℚ_[37])) :
    False := by
  have ht₁Lt : ‖(t₁ : ℚ_[37])‖ < 1 :=
    norm_coe_lt_one_of_toZMod_eq_zero t₁ ht₁Red
  have ht₂Lt : ‖(t₂ : ℚ_[37])‖ < 1 :=
    norm_coe_lt_one_of_toZMod_eq_zero t₂ ht₂Red
  have hrLt : r < 1 := by
    simpa only [ht₁Norm] using ht₁Lt
  have hrSqLt : r ^ 2 < r := by
    nlinarith
  have htail₁ : ‖(tail₁ : ℚ_[37])‖ ≤ 1 :=
    tail₁.property
  have htail₂ : ‖(tail₂ : ℚ_[37])‖ ≤ 1 :=
    tail₂.property
  have hquad₁ :
      ‖(t₁ : ℚ_[37]) ^ 2 * (tail₁ : ℚ_[37])‖ ≤ r ^ 2 := by
    rw [norm_mul, norm_pow, ht₁Norm]
    nlinarith [norm_nonneg (tail₁ : ℚ_[37])]
  have hquad₂ :
      ‖(t₂ : ℚ_[37]) ^ 2 * (tail₂ : ℚ_[37])‖ ≤ r ^ 2 := by
    rw [norm_mul, norm_pow, ht₂Norm]
    nlinarith [norm_nonneg (tail₂ : ℚ_[37])]
  have hquad :
      ‖(t₁ : ℚ_[37]) ^ 2 * (tail₁ : ℚ_[37]) -
          (t₂ : ℚ_[37]) ^ 2 * (tail₂ : ℚ_[37])‖ ≤
        r ^ 2 := by
    rw [sub_eq_add_neg]
    exact
      (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le hquad₁ (by simpa only [norm_neg] using hquad₂))
  have hlinear :
      ‖(sign : ℚ_[37]) * 4 *
          ((t₁ : ℚ_[37]) - (t₂ : ℚ_[37]))‖ = r := by
    rw [norm_mul, norm_mul, hsign, norm_four_padic, hsep]
    norm_num
  have hbalance :
      (sign : ℚ_[37]) * 4 *
          ((t₁ : ℚ_[37]) - (t₂ : ℚ_[37])) =
        -((t₁ : ℚ_[37]) ^ 2 * (tail₁ : ℚ_[37]) -
          (t₂ : ℚ_[37]) ^ 2 * (tail₂ : ℚ_[37])) := by
    linear_combination heq
  have hnormBalance := congrArg norm hbalance
  rw [hlinear, norm_neg] at hnormBalance
  have hquadLt :
      ‖(t₁ : ℚ_[37]) ^ 2 * (tail₁ : ℚ_[37]) -
          (t₂ : ℚ_[37]) ^ 2 * (tail₂ : ℚ_[37])‖ < r :=
    hquad.trans_lt hrSqLt
  linarith

/-- Inequality form of `firstOrderTranslation_eq_impossible`. -/
theorem firstOrderTranslations_ne
    (sign t₁ t₂ tail₁ tail₂ : ℤ_[37])
    (r : ℝ)
    (hsign : ‖(sign : ℚ_[37])‖ = 1)
    (ht₁Red : PadicInt.toZMod t₁ = 0)
    (ht₂Red : PadicInt.toZMod t₂ = 0)
    (ht₁Norm : ‖(t₁ : ℚ_[37])‖ = r)
    (ht₂Norm : ‖(t₂ : ℚ_[37])‖ = r)
    (hsep :
      ‖(t₁ : ℚ_[37]) - (t₂ : ℚ_[37])‖ = r)
    (hr : 0 < r) :
    2 + (sign : ℚ_[37]) * 4 * (t₁ : ℚ_[37]) +
          (t₁ : ℚ_[37]) ^ 2 * (tail₁ : ℚ_[37]) ≠
      2 + (sign : ℚ_[37]) * 4 * (t₂ : ℚ_[37]) +
        (t₂ : ℚ_[37]) ^ 2 * (tail₂ : ℚ_[37]) :=
  fun heq =>
    firstOrderTranslation_eq_impossible
      sign t₁ t₂ tail₁ tail₂ r hsign ht₁Red ht₂Red
      ht₁Norm ht₂Norm hsep hr heq

/-- Wrapper matching the final translated expressions returned by
`GaussianFormalLocal.exists_integral_translation_at_P`. -/
theorem plusFirstOrderTranslations_ne
    (t₁ t₂ tail₁ tail₂ : ℤ_[37])
    (r : ℝ)
    (ht₁Red : PadicInt.toZMod t₁ = 0)
    (ht₂Red : PadicInt.toZMod t₂ = 0)
    (ht₁Norm : ‖(t₁ : ℚ_[37])‖ = r)
    (ht₂Norm : ‖(t₂ : ℚ_[37])‖ = r)
    (hsep :
      ‖(t₁ : ℚ_[37]) - (t₂ : ℚ_[37])‖ = r)
    (hr : 0 < r) :
    2 + 4 * (t₁ : ℚ_[37]) +
          (t₁ : ℚ_[37]) ^ 2 * (tail₁ : ℚ_[37]) ≠
      2 + 4 * (t₂ : ℚ_[37]) +
        (t₂ : ℚ_[37]) ^ 2 * (tail₂ : ℚ_[37]) := by
  have h :=
    firstOrderTranslations_ne
      (1 : ℤ_[37]) t₁ t₂ tail₁ tail₂ r
      (by norm_num) ht₁Red ht₂Red ht₁Norm ht₂Norm hsep hr
  simpa using h

/-- Wrapper matching the final translated expressions returned by
`GaussianFormalLocal.exists_integral_translation_at_negP`. -/
theorem minusFirstOrderTranslations_ne
    (t₁ t₂ tail₁ tail₂ : ℤ_[37])
    (r : ℝ)
    (ht₁Red : PadicInt.toZMod t₁ = 0)
    (ht₂Red : PadicInt.toZMod t₂ = 0)
    (ht₁Norm : ‖(t₁ : ℚ_[37])‖ = r)
    (ht₂Norm : ‖(t₂ : ℚ_[37])‖ = r)
    (hsep :
      ‖(t₁ : ℚ_[37]) - (t₂ : ℚ_[37])‖ = r)
    (hr : 0 < r) :
    2 - 4 * (t₁ : ℚ_[37]) +
          (t₁ : ℚ_[37]) ^ 2 * (tail₁ : ℚ_[37]) ≠
      2 - 4 * (t₂ : ℚ_[37]) +
        (t₂ : ℚ_[37]) ^ 2 * (tail₂ : ℚ_[37]) := by
  have h :=
    firstOrderTranslations_ne
      (-1 : ℤ_[37]) t₁ t₂ tail₁ tail₂ r
      (by norm_num) ht₁Red ht₂Red ht₁Norm ht₂Norm hsep hr
  have hneg :
      (((-1 : ℤ_[37]) : ℚ_[37])) = (-1 : ℚ_[37]) := by
    rw [PadicInt.coe_neg, PadicInt.coe_one]
  rw [hneg] at h
  convert h using 1 <;> ring

end

end GaussianTranslationSeparation
end Cuboid2
