import Cuboid2.QuadraticReduction.Reciprocal

/-!
# Square characters on the reciprocal quotient

For a compact solution the two quotient inputs are literal rational squares,
`S = z²` and `K = k²`.  This file turns the identities in `Reciprocal` into
explicit `IsSquare` witnesses.  Denominator fibres are kept as hypotheses and
are handled by the separate exceptional-fibre audit.
-/

namespace Cuboid2

noncomputable section

/-- A rational square plus one cannot vanish. -/
theorem rat_sq_add_one_ne_zero (x : ℚ) : x ^ 2 + 1 ≠ 0 := by
  nlinarith [sq_nonneg x]

/-- The product character is a square on either physical branch. -/
theorem reciprocal_product_isSquare
    {z k : ℚ} (hk : k ^ 2 - 1 ≠ 0) :
    IsSquare
      (reciprocalU (z ^ 2) (k ^ 2) *
        reciprocalV (z ^ 2) (k ^ 2)) := by
  have hzPlus : z ^ 2 + 1 ≠ 0 := rat_sq_add_one_ne_zero z
  have hkPlus : k ^ 2 + 1 ≠ 0 := rat_sq_add_one_ne_zero k
  rw [reciprocal_UV hzPlus hk hkPlus]
  refine ⟨(z ^ 2 - 1) / (z ^ 2 + 1), ?_⟩
  field_simp [hzPlus] <;> ring

/-- The common second character is a square because `S=z²`. -/
theorem reciprocal_one_sub_product_isSquare
    {z k : ℚ} (hk : k ^ 2 - 1 ≠ 0) :
    IsSquare
      (1 -
        reciprocalU (z ^ 2) (k ^ 2) *
          reciprocalV (z ^ 2) (k ^ 2)) := by
  have hzPlus : z ^ 2 + 1 ≠ 0 := rat_sq_add_one_ne_zero z
  have hkPlus : k ^ 2 + 1 ≠ 0 := rat_sq_add_one_ne_zero k
  rw [reciprocal_one_sub_UV hzPlus hk hkPlus]
  refine ⟨2 * z / (z ^ 2 + 1), ?_⟩
  field_simp [hzPlus] <;> ring

/-- On the positive physical branch the third character is also a square. -/
theorem reciprocal_positive_third_isSquare
    {z k : ℚ} (hz : z ^ 2 - 1 ≠ 0) (hk : k ^ 2 - 1 ≠ 0) :
    IsSquare
      (1 -
        reciprocalV (z ^ 2) (k ^ 2) /
          reciprocalU (z ^ 2) (k ^ 2)) := by
  have hzPlus : z ^ 2 + 1 ≠ 0 := rat_sq_add_one_ne_zero z
  have hkPlus : k ^ 2 + 1 ≠ 0 := rat_sq_add_one_ne_zero k
  rw [reciprocal_one_sub_V_div_U hzPlus hz hkPlus hk]
  refine ⟨2 * k / (k ^ 2 + 1), ?_⟩
  field_simp [hkPlus] <;> ring

/-- On the negative physical branch the third character is minus a square. -/
theorem reciprocal_negative_third_eq_neg_square
    {z k : ℚ} (hz : z ^ 2 - 1 ≠ 0) (hk : k ^ 2 - 1 ≠ 0) :
    1 -
        reciprocalU (z ^ 2) (k ^ 2) /
          reciprocalV (z ^ 2) (k ^ 2) =
      -(2 * k / (k ^ 2 - 1)) ^ 2 := by
  have hzPlus : z ^ 2 + 1 ≠ 0 := rat_sq_add_one_ne_zero z
  have hkPlus : k ^ 2 + 1 ≠ 0 := rat_sq_add_one_ne_zero k
  rw [reciprocal_one_sub_U_div_V hzPlus hz hkPlus hk]
  field_simp [hk] <;> ring

end

end Cuboid2
