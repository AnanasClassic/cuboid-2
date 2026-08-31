import Cuboid2.QuadraticReduction.CompactModel

/-!
# Simultaneous reciprocal quotient

These are the exact Cayley/fixed-field identities used for both physical
signs.  All denominator hypotheses are explicit; no generic-open-set argument
is used implicitly.
-/

namespace Cuboid2

noncomputable section

/-- Cayley coordinate for `S=z^2`. -/
def reciprocalCayleyX (S : ℚ) : ℚ := (S - 1) / (S + 1)

/-- Cayley coordinate for `K=k^2`. -/
def reciprocalCayleyY (K : ℚ) : ℚ := (K - 1) / (K + 1)

/-- First fixed-field generator `U=x/y`. -/
def reciprocalU (S K : ℚ) : ℚ :=
  ((S - 1) * (K + 1)) / ((S + 1) * (K - 1))

/-- Second fixed-field generator `V=xy`. -/
def reciprocalV (S K : ℚ) : ℚ :=
  ((S - 1) * (K - 1)) / ((S + 1) * (K + 1))

/-- The product character is independent of the physical sign. -/
theorem reciprocal_UV
    {S K : ℚ} (hS : S + 1 ≠ 0) (hKm : K - 1 ≠ 0) (hKp : K + 1 ≠ 0) :
    reciprocalU S K * reciprocalV S K = (S - 1) ^ 2 / (S + 1) ^ 2 := by
  unfold reciprocalU reciprocalV
  field_simp [hS, hKm, hKp] <;> ring

/-- Exact common character, including its factor `4`. -/
theorem reciprocal_one_sub_UV
    {S K : ℚ} (hS : S + 1 ≠ 0) (hKm : K - 1 ≠ 0) (hKp : K + 1 ≠ 0) :
    1 - reciprocalU S K * reciprocalV S K = 4 * S / (S + 1) ^ 2 := by
  rw [reciprocal_UV hS hKm hKp]
  field_simp [hS]
  ring

/-- The ratio `V/U` is a square on the positive physical branch. -/
theorem reciprocal_V_div_U
    {S K : ℚ}
    (hSp : S + 1 ≠ 0) (hSm : S - 1 ≠ 0)
    (hKp : K + 1 ≠ 0) (hKm : K - 1 ≠ 0) :
    reciprocalV S K / reciprocalU S K = (K - 1) ^ 2 / (K + 1) ^ 2 := by
  unfold reciprocalU reciprocalV
  field_simp [hSp, hSm, hKp, hKm] <;> ring

/-- Positive-branch third character. -/
theorem reciprocal_one_sub_V_div_U
    {S K : ℚ}
    (hSp : S + 1 ≠ 0) (hSm : S - 1 ≠ 0)
    (hKp : K + 1 ≠ 0) (hKm : K - 1 ≠ 0) :
    1 - reciprocalV S K / reciprocalU S K = 4 * K / (K + 1) ^ 2 := by
  rw [reciprocal_V_div_U hSp hSm hKp hKm]
  field_simp [hKp]
  ring

/-- Negative-branch third character, with its essential minus sign. -/
theorem reciprocal_one_sub_U_div_V
    {S K : ℚ}
    (hSp : S + 1 ≠ 0) (hSm : S - 1 ≠ 0)
    (hKp : K + 1 ≠ 0) (hKm : K - 1 ≠ 0) :
    1 - reciprocalU S K / reciprocalV S K = -4 * K / (K - 1) ^ 2 := by
  unfold reciprocalU reciprocalV
  field_simp [hSp, hSm, hKp, hKm] <;> ring

/-- Reciprocal inversion becomes sign change in the first Cayley coordinate. -/
theorem reciprocalCayleyX_inv
    {S : ℚ} (hS0 : S ≠ 0) (hSp : S + 1 ≠ 0) :
    reciprocalCayleyX (1 / S) = -reciprocalCayleyX S := by
  have hOneSp : 1 + S ≠ 0 := by simpa [add_comm] using hSp
  unfold reciprocalCayleyX
  field_simp [hS0, hSp, hOneSp] <;> ring

/-- Reciprocal inversion becomes sign change in the second Cayley coordinate. -/
theorem reciprocalCayleyY_inv
    {K : ℚ} (hK0 : K ≠ 0) (hKp : K + 1 ≠ 0) :
    reciprocalCayleyY (1 / K) = -reciprocalCayleyY K := by
  have hOneKp : 1 + K ≠ 0 := by simpa [add_comm] using hKp
  unfold reciprocalCayleyY
  field_simp [hK0, hKp, hOneKp] <;> ring

/-- The simultaneous involution fixes `U`. -/
theorem reciprocalU_inv
    {S K : ℚ}
    (hS0 : S ≠ 0) (hK0 : K ≠ 0)
    (hSp : S + 1 ≠ 0) (hSm : S - 1 ≠ 0)
    (hKp : K + 1 ≠ 0) (hKm : K - 1 ≠ 0) :
    reciprocalU (1 / S) (1 / K) = reciprocalU S K := by
  have hOneSp : 1 + S ≠ 0 := by simpa [add_comm] using hSp
  have hOneKm : 1 - K ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hKm))
  have hden : 1 + S - S * K - K ≠ 0 := by
    rw [show 1 + S - S * K - K = (1 + S) * (1 - K) by ring]
    exact mul_ne_zero hOneSp hOneKm
  unfold reciprocalU
  field_simp [hS0, hK0, hSp, hSm, hKp, hKm, hOneSp, hOneKm, hden] <;> ring

/-- The simultaneous involution fixes `V`. -/
theorem reciprocalV_inv
    {S K : ℚ}
    (hS0 : S ≠ 0) (hK0 : K ≠ 0)
    (hSp : S + 1 ≠ 0) (hSm : S - 1 ≠ 0)
    (hKp : K + 1 ≠ 0) (hKm : K - 1 ≠ 0) :
    reciprocalV (1 / S) (1 / K) = reciprocalV S K := by
  have hOneSp : 1 + S ≠ 0 := by simpa [add_comm] using hSp
  have hOneKp : 1 + K ≠ 0 := by simpa [add_comm] using hKp
  have hden : 1 + S + S * K + K ≠ 0 := by
    rw [show 1 + S + S * K + K = (1 + S) * (1 + K) by ring]
    exact mul_ne_zero hOneSp hOneKp
  unfold reciprocalV
  field_simp [hS0, hK0, hSp, hSm, hKp, hKm, hOneSp, hOneKp, hden] <;> ring

end

end Cuboid2
