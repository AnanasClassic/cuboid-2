import Cuboid2.DPlus.LocalSeries
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Finite and valuation rows for the direct `p=3` certificate

This file checks the projective residue information and the universal
integer inequalities used to control all omitted primitive coefficients.
-/

namespace Cuboid2

noncomputable section

local instance dplusLocalFactPrime3 : Fact (Nat.Prime 3) :=
  ⟨by norm_num⟩

/-- A finite affine point on the `D+` model. -/
structure DPlusFiniteAffinePoint (K : Type*) [CommRing K] where
  a : K
  R : K
deriving DecidableEq, Fintype

namespace DPlusFiniteAffinePoint

variable {K : Type*} [CommRing K]

/-- The exact finite curve equation. -/
def Valid (P : DPlusFiniteAffinePoint K) : Prop :=
  P.R ^ 2 = 4 * P.a ^ 5 - 8 * P.a ^ 2 + 5 * P.a

instance [DecidableEq K] (P : DPlusFiniteAffinePoint K) :
    Decidable P.Valid := by
  unfold Valid
  infer_instance

end DPlusFiniteAffinePoint

/-- All five affine points on `D+(F₃)`. -/
def dplusAffinePointsF3 : List (DPlusFiniteAffinePoint (ZMod 3)) :=
  [ ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨2, 2⟩ ]

/-- Exact enumeration of the affine reduction. -/
theorem dplusF3_valid_iff_mem
    (P : DPlusFiniteAffinePoint (ZMod 3)) :
    P.Valid ↔ P ∈ dplusAffinePointsF3 := by
  decide +revert

/-- A square abscissa leaves precisely the three affine disks used by the
direct certificate. -/
theorem dplusF3_valid_square_abscissa
    (P : DPlusFiniteAffinePoint (ZMod 3))
    (hP : P.Valid) (hsquare : ∃ u : ZMod 3, P.a = u ^ 2) :
    P = ⟨0, 0⟩ ∨ P = ⟨1, 1⟩ ∨ P = ⟨1, 2⟩ := by
  revert P
  decide

/-- The two remaining affine disks have nonsquare abscissa. -/
theorem dplusF3_nonsquare_extra_disks :
    ¬(∃ u : ZMod 3, (2 : ZMod 3) = u ^ 2) := by
  decide

/--
Universal coefficient estimate at `3`: division by the primitive degree
cannot consume the two powers of `3` supplied by a term of degree at least
two.
-/
theorem padicValNat_three_add_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    padicValNat 3 n + 2 ≤ n := by
  by_cases hsmall : n ≤ 3
  · have hnCases : n = 2 ∨ n = 3 := by omega
    rcases hnCases with rfl | rfl
    · rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬3 ∣ 2)]
    · rw [padicValNat_self]
  · have h3n : 3 < n := by omega
    have h := padicValNat_add_le_self (p := 3) h3n
    omega

/-- Subtraction form of the infinity-tail estimate
`n-1-v₃(n) ≥ 1`. -/
theorem one_le_degree_sub_one_sub_padicValNat_three
    {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ n - 1 - padicValNat 3 n := by
  have h := padicValNat_three_add_two_le hn
  omega

/-- First tail estimate in the two disks above `a=1`. -/
theorem one_le_twice_degree_sub_two_sub_padicValNat_three
    {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ 2 * n - 2 - padicValNat 3 n := by
  have h := padicValNat_three_add_two_le hn
  omega

/-- Second tail estimate in the two disks above `a=1`. -/
theorem one_le_twice_degree_sub_three_sub_padicValNat_three
    {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ 2 * n - 3 - padicValNat 3 n := by
  have h := padicValNat_three_add_two_le hn
  omega

end

end Cuboid2
