import Cuboid2.DPlus.FiniteGroup
import Cuboid2.DPlus.GlobalMumfordCertificate
import Mathlib.NumberTheory.PythagoreanTriples

/-!
# Fixed-curve global certificate rows for `D+`

This module deliberately stops before the missing Schaefer--Stoll/Jacobian
bridge.  It checks the finite mask arithmetic, the rational two-torsion
candidate, the integral `3`-saturation consequence, and an elementary
Pythagorean reformulation of the octic cover.  None of these rows is stated
as a premise equivalent to a rank theorem or a rational-point
classification.
-/

namespace Cuboid2

noncomputable section

/-! ## The four final two-descent masks -/

/-- Final masks in the pinned thirteen-bit squareclass basis. -/
def dplusSelmerSurvivorMasks : Finset (Fin 8192) :=
  {0, 96, 276, 372}

/-- Named final masks: identity, `D`, `D+T`, and `T`. -/
def dplusIdentityMask : Fin 8192 := 0
def dplusDMask : Fin 8192 := 96
def dplusDPlusTMask : Fin 8192 := 276
def dplusTMask : Fin 8192 := 372

/-- The exact local survivor set has four distinct rows. -/
theorem card_dplusSelmerSurvivorMasks :
    dplusSelmerSurvivorMasks.card = 4 := by
  decide

/-- The named rows exhaust the pinned finite survivor set. -/
theorem dplusSelmerSurvivorMasks_eq_named :
    dplusSelmerSurvivorMasks =
      {dplusIdentityMask, dplusDMask, dplusDPlusTMask, dplusTMask} :=
  rfl

/-- In the binary mask algebra the row for `D+T` is the xor of the rows for
`D` and `T`. -/
theorem dplusD_xor_T_mask :
    dplusDMask.val ^^^ dplusTMask.val = dplusDPlusTMask.val := by
  decide

/--
The exact good-reduction orders at `3` and `7` have gcd two.  This is the
numerical torsion bound consumed by a genuine good-reduction injection
theorem.
-/
theorem dplus_good_reduction_order_gcd :
    Nat.gcd 22 42 = 2 := by
  decide

/-- The displayed two-torsion row is nonzero and has exact order two in the
complete finite model at `7`. -/
theorem dplus_finite_torsion_row_order :
    dplusTorsionIndexF7 ≠ 0 ∧
      addOrderOf dplusTorsionIndexF7 = 2 := by
  constructor
  · decide
  · exact addOrderOf_dplusTorsionIndexF7

/-- The finite `p=7` certificate gives the exact order of the `D` row. -/
theorem dplus_finite_generator_row_order :
    addOrderOf dplusGeneratorIndexF7 = 21 :=
  addOrderOf_dplusGeneratorIndexF7

/--
The complete fixed finite group proves the integral `3`-saturation step for
every putative global generator relation with odd multiplier.
-/
theorem dplus_three_saturated_odd_relation
    {generator : DPlusJacobianIndexF7} {m : ℕ}
    (hrel : dplusGeneratorIndexF7 = m • generator)
    (hm : Odd m) :
    ¬ 3 ∣ m :=
  dplusIndex_odd_multiplier_not_divisible_by_three hrel hm

/-! ## Elementary audit of the proposed Pythagorean shortcut -/

/--
The octic equation is the Pythagorean identity

`r² = (2u⁴ - 1)² + (2(u² - 1))²`.
-/
theorem octic_pythagorean_identity (u : ℚ) :
    octicRhs u =
      (2 * u ^ 4 - 1) ^ 2 + (2 * (u ^ 2 - 1)) ^ 2 := by
  simp [octicRhs]
  ring

/-- Every octic point therefore gives a rational Pythagorean triple. -/
theorem OcticPoint.pythagoreanTriple (P : OcticPoint) :
    (2 * P.u ^ 4 - 1) ^ 2 +
        (2 * (P.u ^ 2 - 1)) ^ 2 =
      P.r ^ 2 := by
  rw [← octic_pythagorean_identity, P.onCurve]

/--
The circle parameter `t = 2(u²-1)/(r+2u⁴-1)` produces the exact conic
relation.  This exposes why the shortcut does not lower the arithmetic
complexity: eliminating `u²` from this relation recovers the same
square-pullback problem.
-/
theorem octic_circle_parameter_relation
    (P : OcticPoint)
    (hden : P.r + (2 * P.u ^ 4 - 1) ≠ 0) :
    let t := 2 * (P.u ^ 2 - 1) /
      (P.r + (2 * P.u ^ 4 - 1))
    (P.u ^ 2 - 1) * (1 - t ^ 2) =
      t * (2 * P.u ^ 4 - 1) := by
  dsimp
  have hpyth :
      (2 * P.u ^ 4 - 1) ^ 2 +
          (2 * (P.u ^ 2 - 1)) ^ 2 =
        P.r ^ 2 :=
    P.pythagoreanTriple
  apply (mul_left_cancel₀ (pow_ne_zero 2 hden))
  field_simp [hden]
  ring_nf at hpyth ⊢
  nlinarith

/--
After treating `y=u²`, the discriminant of the conic parameter equation is
the reciprocal quartic displayed below.  It is an exact algebraic identity,
not a claim that the resulting genus-one square pullback is classified.
-/
theorem octic_circle_discriminant_identity (t : ℚ) :
    (1 - t ^ 2) ^ 2 - 8 * t * (1 - t ^ 2 - t) =
      t ^ 4 + 8 * t ^ 3 + 6 * t ^ 2 - 8 * t + 1 := by
  ring

end

end Cuboid2
