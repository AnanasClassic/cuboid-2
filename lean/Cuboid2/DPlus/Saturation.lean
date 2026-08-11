import Cuboid2.DPlus.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# The elementary `p=7` saturation step

Once Lean has checked `#J(F_7)=42` and `ord(D mod 7)=21`, the remaining
argument is finite group arithmetic.  This file proves that argument without
assuming that the rational divisor `D` is primitive.
-/

namespace Cuboid2

noncomputable section

/-- The numerical core of the `3`-saturation argument. -/
theorem saturation_arithmetic
    {n m : ℕ}
    (hn : n ∣ 42)
    (horder : n / Nat.gcd n m = 21)
    (hm : Odd m) :
    ¬ 3 ∣ m := by
  have hnle : n ≤ 42 := Nat.le_of_dvd (by norm_num) hn
  have hquotle : n / Nat.gcd n m ≤ n := Nat.div_le_self n (Nat.gcd n m)
  have hnlow : 21 ≤ n := by omega
  have hncases : n = 21 ∨ n = 42 := by
    interval_cases n <;> norm_num at hn ⊢
  rcases hncases with rfl | rfl
  · have hgcd : Nat.gcd 21 m = 1 := by
      have hle : Nat.gcd 21 m ≤ 21 :=
        Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 21 m)
      interval_cases h : Nat.gcd 21 m <;> norm_num [h] at horder ⊢
    intro h3
    have h3gcd : 3 ∣ Nat.gcd 21 m :=
      Nat.dvd_gcd (by norm_num) h3
    rw [hgcd] at h3gcd
    norm_num at h3gcd
  · have hgcd : Nat.gcd 42 m = 2 := by
      have hle : Nat.gcd 42 m ≤ 42 :=
        Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 42 m)
      interval_cases h : Nat.gcd 42 m <;> norm_num [h] at horder ⊢
    have h2 : 2 ∣ m := by
      rw [← hgcd]
      exact Nat.gcd_dvd_right 42 m
    obtain ⟨r, hr⟩ := hm
    obtain ⟨s, hs⟩ := h2
    omega

/--
Abstract finite-group form used by the `D+` proof.  The only curve-specific
inputs are the checked cardinality and checked order of `D mod 7`.
-/
theorem odd_multiplier_not_divisible_by_three
    {G : Type*} [AddCommGroup G] [Fintype G]
    {D generator : G} {m : ℕ}
    (hcard : Fintype.card G = 42)
    (hD : addOrderOf D = 21)
    (hrel : D = m • generator)
    (hm : Odd m) :
    ¬ 3 ∣ m := by
  apply saturation_arithmetic (n := addOrderOf generator) (m := m)
  · rw [← hcard]
    exact addOrderOf_dvd_card
  · calc
      addOrderOf generator / Nat.gcd (addOrderOf generator) m =
          addOrderOf (m • generator) := by
            symm
            exact addOrderOf_nsmul generator
      _ = addOrderOf D := by rw [hrel]
      _ = 21 := hD
  · exact hm

end

end Cuboid2
