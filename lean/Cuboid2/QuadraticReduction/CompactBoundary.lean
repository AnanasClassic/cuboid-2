import Cuboid2.QuadraticReduction.QuotientTransport
import Cuboid2.QuadraticReduction.Characters

/-!
# Compact-chart boundary elimination

The reciprocal Cayley chart uses `S = z²` and `K = k²`, and therefore
requires the factors `S + 1`, `K - 1`, and `K + 1` to be nonzero.  This
module discharges those conditions directly from the two compact projection
equations.  In the negative physical branch, the only additional factor is
the reciprocal quartic; its absence on positive rational `S` is proved by
reducing a putative root to a rational square root of `5`.
-/

namespace Cuboid2

noncomputable section

/--
The reciprocal exceptional quartic has no positive rational root.

After division by `S²`, a root would give
`(S + 1/S - 16)² = 320`, hence a rational square root of `5`.
-/
theorem reciprocalExceptionalQuartic_ne_zero_of_pos
    {S : ℚ} (hS : 0 < S) :
    reciprocalExceptionalQuartic S ≠ 0 := by
  intro hquartic
  have hS0 : S ≠ 0 := ne_of_gt hS
  have hsquare :
      (S + 1 / S - 16) ^ 2 = 320 := by
    unfold reciprocalExceptionalQuartic at hquartic
    field_simp [hS0]
    nlinarith [hquartic]
  have hroot :
      ((S + 1 / S - 16) / 8) ^ 2 = 5 := by
    nlinarith [hsquare]
  have hfive : IsSquare (5 : ℚ) := by
    refine ⟨(S + 1 / S - 16) / 8, ?_⟩
    simpa [pow_two] using hroot.symm
  norm_num at hfive

/--
On the positive compact projection, the fibre `K = 1` forces `S = ±1`.
Both values are excluded on the regular square-parameter chart.
-/
theorem compactProjectionPositive_K_ne_one
    {S K : ℚ}
    (hQ : compactProjectionPositive S K = 0)
    (hSm : S - 1 ≠ 0) (hSp : S + 1 ≠ 0) :
    K - 1 ≠ 0 := by
  intro hK
  have hK1 : K = 1 := sub_eq_zero.mp hK
  rw [hK1, compactProjectionPositive_K_one] at hQ
  have hfactor :
      (64 : ℚ) * (S - 1) ^ 6 * (S + 1) ^ 2 ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 6 hSm))
      (pow_ne_zero 2 hSp)
  exact hfactor hQ

/--
On the negative compact projection, the fibre `K = 1` is the union of
`S = 1` and the reciprocal exceptional quartic.  Neither meets the positive
regular square-parameter chart.
-/
theorem compactProjectionNegative_K_ne_one
    {S K : ℚ}
    (hQ : compactProjectionNegative S K = 0)
    (hS : 0 < S) (hSm : S - 1 ≠ 0) :
    K - 1 ≠ 0 := by
  intro hK
  have hK1 : K = 1 := sub_eq_zero.mp hK
  rw [hK1, compactProjectionNegative_K_one] at hQ
  have hquartic :
      reciprocalExceptionalQuartic S ≠ 0 :=
    reciprocalExceptionalQuartic_ne_zero_of_pos hS
  have hfactor :
      (16 : ℚ) * (S - 1) ^ 4 *
          reciprocalExceptionalQuartic S ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 4 hSm))
      hquartic
  exact hfactor hQ

/-- The two compact projections, with the physical sign kept explicit. -/
def compactProjection : PhysicalSign → ℚ → ℚ → ℚ
  | .positive => compactProjectionPositive
  | .negative => compactProjectionNegative

/-- Both pairs of compact equations imply their sign-specific projection. -/
theorem compactProjection_of_compact_equations
    {ε : PhysicalSign} {z k y : ℚ}
    (h1 : compactF1 ε z k y = 0)
    (h0 : compactF0 ε z k y = 0) :
    compactProjection ε (z ^ 2) (k ^ 2) = 0 := by
  cases ε with
  | positive =>
      exact compactProjectionPositive_of_compact_equations h1 h0
  | negative =>
      exact compactProjectionNegative_of_compact_equations h1 h0

/--
Every compact solution with nonzero parameters and `z² ≠ 1` lies in the
full reciprocal Cayley chart.  The six conclusions are the nonzero square
parameters and the four factors used by the quotient transport.
-/
theorem compact_square_chart_denominators
    {ε : PhysicalSign} {z k y : ℚ}
    (hz : z ≠ 0) (hk : k ≠ 0)
    (hSm : z ^ 2 - 1 ≠ 0)
    (h1 : compactF1 ε z k y = 0)
    (h0 : compactF0 ε z k y = 0) :
    z ^ 2 ≠ 0 ∧ k ^ 2 ≠ 0 ∧
      z ^ 2 + 1 ≠ 0 ∧ z ^ 2 - 1 ≠ 0 ∧
      k ^ 2 + 1 ≠ 0 ∧ k ^ 2 - 1 ≠ 0 := by
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hk2 : k ^ 2 ≠ 0 := pow_ne_zero 2 hk
  have hzPlus : z ^ 2 + 1 ≠ 0 := rat_sq_add_one_ne_zero z
  have hkPlus : k ^ 2 + 1 ≠ 0 := rat_sq_add_one_ne_zero k
  have hQ := compactProjection_of_compact_equations h1 h0
  have hKminus : k ^ 2 - 1 ≠ 0 := by
    cases ε with
    | positive =>
        exact compactProjectionPositive_K_ne_one hQ hSm hzPlus
    | negative =>
        exact compactProjectionNegative_K_ne_one hQ
          (sq_pos_of_ne_zero hz) hSm
  exact ⟨hz2, hk2, hzPlus, hSm, hkPlus, hKminus⟩

/--
The sign-specific reciprocal coordinates of a compact solution lie on
`C8`, with no residual denominator hypotheses.
-/
theorem compact_equations_to_reciprocalQuotientC8
    {ε : PhysicalSign} {z k y : ℚ}
    (hz : z ≠ 0) (hk : k ≠ 0)
    (hSm : z ^ 2 - 1 ≠ 0)
    (h1 : compactF1 ε z k y = 0)
    (h0 : compactF0 ε z k y = 0) :
    match ε with
    | .positive =>
        reciprocalQuotientC8
          (reciprocalU (z ^ 2) (k ^ 2))
          (reciprocalV (z ^ 2) (k ^ 2)) = 0
    | .negative =>
        reciprocalQuotientC8
          (reciprocalV (z ^ 2) (k ^ 2))
          (reciprocalU (z ^ 2) (k ^ 2)) = 0 := by
  obtain ⟨_, _, hzPlus, _, hkPlus, hkMinus⟩ :=
    compact_square_chart_denominators hz hk hSm h1 h0
  have hQ := compactProjection_of_compact_equations h1 h0
  cases ε with
  | positive =>
      exact reciprocalQuotientC8_of_compactProjectionPositive
        hzPlus hkMinus hkPlus hQ
  | negative =>
      exact reciprocalQuotientC8_of_compactProjectionNegative
        hzPlus hkMinus hkPlus hQ

/--
The product character of a nonzero compact square parameter is not the
removed value `1`.
-/
theorem reciprocal_product_ne_one_of_z_ne_zero
    {z k : ℚ} (hz : z ≠ 0) (hk : k ^ 2 - 1 ≠ 0) :
    reciprocalU (z ^ 2) (k ^ 2) *
        reciprocalV (z ^ 2) (k ^ 2) ≠ 1 := by
  have hzPlus : z ^ 2 + 1 ≠ 0 := rat_sq_add_one_ne_zero z
  have hkPlus : k ^ 2 + 1 ≠ 0 := rat_sq_add_one_ne_zero k
  rw [reciprocal_UV hzPlus hk hkPlus]
  intro h
  field_simp [hzPlus] at h
  nlinarith [sq_pos_of_ne_zero hz]

/--
The common character of a nonzero compact square parameter is itself
nonzero.
-/
theorem reciprocal_one_sub_product_ne_zero_of_z_ne_zero
    {z k : ℚ} (hz : z ≠ 0) (hk : k ^ 2 - 1 ≠ 0) :
    1 -
        reciprocalU (z ^ 2) (k ^ 2) *
          reciprocalV (z ^ 2) (k ^ 2) ≠ 0 := by
  have hzPlus : z ^ 2 + 1 ≠ 0 := rat_sq_add_one_ne_zero z
  have hkPlus : k ^ 2 + 1 ≠ 0 := rat_sq_add_one_ne_zero k
  rw [reciprocal_one_sub_UV hzPlus hk hkPlus]
  exact div_ne_zero
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz))
    (pow_ne_zero 2 hzPlus)

/-- First reciprocal coordinate in the sign-specific physical ordering. -/
def compactReciprocalU (ε : PhysicalSign) (z k : ℚ) : ℚ :=
  match ε with
  | .positive => reciprocalU (z ^ 2) (k ^ 2)
  | .negative => reciprocalV (z ^ 2) (k ^ 2)

/-- Second reciprocal coordinate in the sign-specific physical ordering. -/
def compactReciprocalV (ε : PhysicalSign) (z k : ℚ) : ℚ :=
  match ε with
  | .positive => reciprocalV (z ^ 2) (k ^ 2)
  | .negative => reciprocalU (z ^ 2) (k ^ 2)

/--
All four common-character facts used after quotient transport.  They are
unchanged when the two reciprocal coordinates are swapped.
-/
theorem compact_common_character_facts
    {ε : PhysicalSign} {z k y : ℚ}
    (hz : z ≠ 0) (hk : k ≠ 0)
    (hSm : z ^ 2 - 1 ≠ 0)
    (h1 : compactF1 ε z k y = 0)
    (h0 : compactF0 ε z k y = 0) :
    IsSquare (compactReciprocalU ε z k * compactReciprocalV ε z k) ∧
      compactReciprocalU ε z k * compactReciprocalV ε z k ≠ 1 ∧
      IsSquare
        (1 - compactReciprocalU ε z k * compactReciprocalV ε z k) ∧
      1 - compactReciprocalU ε z k * compactReciprocalV ε z k ≠ 0 := by
  obtain ⟨_, _, _, _, _, hkMinus⟩ :=
    compact_square_chart_denominators hz hk hSm h1 h0
  have hsquare := reciprocal_product_isSquare (z := z) hkMinus
  have hone :=
    reciprocal_product_ne_one_of_z_ne_zero (z := z) hz hkMinus
  have hcharacter :=
    reciprocal_one_sub_product_isSquare (z := z) hkMinus
  have hcharacterZero :=
    reciprocal_one_sub_product_ne_zero_of_z_ne_zero (z := z) hz hkMinus
  cases ε with
  | positive =>
      simpa [compactReciprocalU, compactReciprocalV] using
        And.intro hsquare
          (And.intro hone (And.intro hcharacter hcharacterZero))
  | negative =>
      simpa [compactReciprocalU, compactReciprocalV, mul_comm] using
        And.intro hsquare
          (And.intro hone (And.intro hcharacter hcharacterZero))

end

end Cuboid2
