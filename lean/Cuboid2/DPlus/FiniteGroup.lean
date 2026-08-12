import Cuboid2.Genus2.FiniteMumford
import Cuboid2.DPlus.Saturation
import Mathlib.GroupTheory.OrderOfElement

/-!
# The finite `D+` Jacobian at `7`

The external certificate writes every reduced Mumford representative in the
coordinates

`n * [(1,1)-∞] + e * [(0,0)-∞]`, with `n ∈ Z/21Z` and `e ∈ Z/2Z`.

This file records that table as explicit data.  Ordinary kernel reduction
checks that every row satisfies the exact Mumford divisibility condition and
that the 42 rows enumerate all such representatives without repetition.
Thus the coordinate type has the right finite carrier, while retaining the
cyclic orders used by the saturation argument.
-/

namespace Cuboid2

noncomputable section

local instance dplusFiniteGroupFactPrime7 : Fact (Nat.Prime 7) :=
  ⟨by norm_num⟩

/-- Coordinates for the finite Jacobian certificate at `7`. -/
abbrev DPlusJacobianIndexF7 := ZMod 21 × ZMod 2

/--
The 42 reduced representatives, ordered as `(0,0),(0,1),(1,0),(1,1),…`.
The `v` coordinate uses the original model `R²=4a⁵-8a²+5a`.
-/
def dplusMumfordTableF7 : List (FiniteMumford (ZMod 7)) :=
  [ .infinity,
    .degreeOne 0 0,
    .degreeOne 6 1,
    .degreeTwo 6 0 1 0,
    .degreeTwo 5 1 1 0,
    .degreeTwo 2 3 6 0,
    .degreeTwo 2 1 5 0,
    .degreeTwo 5 3 2 0,
    .degreeTwo 4 2 0 6,
    .degreeTwo 6 5 1 6,
    .degreeOne 5 6,
    .degreeTwo 5 0 3 0,
    .degreeTwo 4 2 5 3,
    .degreeTwo 2 5 5 3,
    .degreeTwo 0 2 0 4,
    .degreeTwo 6 5 2 4,
    .degreeTwo 6 4 1 1,
    .degreeTwo 0 6 4 2,
    .degreeTwo 1 0 2 0,
    .degreeOne 1 5,
    .degreeTwo 3 4 4 5,
    .degreeTwo 0 6 5 3,
    .degreeTwo 3 4 3 2,
    .degreeTwo 0 6 2 4,
    .degreeTwo 1 0 5 0,
    .degreeOne 1 2,
    .degreeTwo 6 4 6 6,
    .degreeTwo 0 6 3 5,
    .degreeTwo 0 2 0 3,
    .degreeTwo 6 5 5 3,
    .degreeTwo 4 2 2 4,
    .degreeTwo 2 5 2 4,
    .degreeOne 5 1,
    .degreeTwo 5 0 4 0,
    .degreeTwo 4 2 0 1,
    .degreeTwo 6 5 6 1,
    .degreeTwo 2 1 2 0,
    .degreeTwo 5 3 5 0,
    .degreeTwo 5 1 6 0,
    .degreeTwo 2 3 1 0,
    .degreeOne 6 6,
    .degreeTwo 6 0 6 0 ]

@[simp] theorem dplusMumfordTableF7_length :
    dplusMumfordTableF7.length = 42 := rfl

/-- The table row belonging to a pair of cyclic coordinates. -/
def dplusRepresentativeRawF7
    (i : DPlusJacobianIndexF7) : FiniteMumford (ZMod 7) :=
  dplusMumfordTableF7[
    2 * i.1.val + i.2.val
  ]'(by
    rw [dplusMumfordTableF7_length]
    have h₁ := i.1.val_lt
    have h₂ := i.2.val_lt
    omega)

/-- Every displayed table row is a valid reduced Mumford representative. -/
theorem dplusRepresentativeRawF7_valid
    (i : DPlusJacobianIndexF7) :
    (dplusRepresentativeRawF7 i).ValidOn dplusPolynomialF7 := by
  set_option maxRecDepth 100000 in
    decide +revert

/-- The table row, bundled with its kernel-checked curve condition. -/
def dplusRepresentativeF7
    (i : DPlusJacobianIndexF7) : DPlusMumfordF7 :=
  ⟨dplusRepresentativeRawF7 i, dplusRepresentativeRawF7_valid i⟩

/--
The 42 coordinate rows and the 42 exact reduced Mumford representatives are
in bijection.  This simultaneously checks absence of duplicate rows and
exhaustiveness of the table.
-/
theorem dplusRepresentativeF7_bijective :
    Function.Bijective dplusRepresentativeF7 := by
  set_option maxRecDepth 100000 in
    decide +revert

/-- Exact equivalence between the cyclic certificate coordinates and the
kernel-enumerated reduced representatives. -/
def dplusRepresentativeEquivF7 :
    DPlusJacobianIndexF7 ≃ DPlusMumfordF7 :=
  Equiv.ofBijective dplusRepresentativeF7
    dplusRepresentativeF7_bijective

/-- In the pinned coordinates, the reduction of `D=[(1,1)-∞]`. -/
def dplusGeneratorIndexF7 : DPlusJacobianIndexF7 := (1, 0)

/-- In the pinned coordinates, the reduction of `T=[(0,0)-∞]`. -/
def dplusTorsionIndexF7 : DPlusJacobianIndexF7 := (0, 1)

@[simp] theorem dplusGeneratorIndexF7_rep :
    (dplusRepresentativeF7 dplusGeneratorIndexF7).1 =
      .degreeOne 6 1 := by
  decide

@[simp] theorem dplusTorsionIndexF7_rep :
    (dplusRepresentativeF7 dplusTorsionIndexF7).1 =
      .degreeOne 0 0 := by
  decide

/-- The coordinate model has exactly 42 elements. -/
theorem card_dplusJacobianIndexF7 :
    Fintype.card DPlusJacobianIndexF7 = 42 := by
  decide

/-- The displayed generator coordinate has exact additive order 21. -/
theorem addOrderOf_dplusGeneratorIndexF7 :
    addOrderOf dplusGeneratorIndexF7 = 21 := by
  rw [addOrderOf_eq_iff (by norm_num : 0 < 21)]
  constructor
  · decide
  · intro m hm hm0 hzero
    have hfirst :
        (m : ZMod 21) = 0 := by
      simpa [dplusGeneratorIndexF7] using
        congrArg Prod.fst hzero
    have hdvd : 21 ∣ m :=
      (ZMod.natCast_eq_zero_iff m 21).mp hfirst
    omega

/-- The displayed Weierstrass coordinate has exact additive order 2. -/
theorem addOrderOf_dplusTorsionIndexF7 :
    addOrderOf dplusTorsionIndexF7 = 2 := by
  rw [addOrderOf_eq_iff (by norm_num : 0 < 2)]
  constructor
  · decide
  · intro m hm hm0 hzero
    have hsecond :
        (m : ZMod 2) = 0 := by
      simpa [dplusTorsionIndexF7] using
        congrArg Prod.snd hzero
    have hdvd : 2 ∣ m :=
      (ZMod.natCast_eq_zero_iff m 2).mp hsecond
    omega

/--
The abstract saturation lemma is now instantiated by the finite certificate:
an odd multiplier of the displayed `D` coordinate cannot be divisible by
three.
-/
theorem dplusIndex_odd_multiplier_not_divisible_by_three
    {generator : DPlusJacobianIndexF7} {m : ℕ}
    (hrel : dplusGeneratorIndexF7 = m • generator)
    (hm : Odd m) :
    ¬ 3 ∣ m := by
  exact odd_multiplier_not_divisible_by_three
    card_dplusJacobianIndexF7
    addOrderOf_dplusGeneratorIndexF7
    hrel hm

end

end Cuboid2
