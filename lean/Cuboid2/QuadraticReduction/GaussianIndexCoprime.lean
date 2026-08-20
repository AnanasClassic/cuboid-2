import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

/-!
# Coprimality consequences for the visible-point index

These lemmas collect the elementary integer arithmetic needed after the
visible point has been saturated at `2`, `3`, `7`, and `37`.
-/

namespace Cuboid2
namespace GaussianIndexCoprime

private theorem irreducible_int_of_nat_prime
    {p : ℕ} (hp : Nat.Prime p) :
    Irreducible (p : ℤ) := by
  rw [irreducible_iff_prime, Int.prime_iff_natAbs_prime]
  simpa using hp

/-- An odd integer not divisible by `3` or `7` is coprime to
`84 = 2² · 3 · 7`. -/
theorem isCoprime_84_of_odd_of_not_dvd_three_of_not_dvd_seven
    {m : ℤ}
    (hodd : Odd m)
    (hthree : ¬ (3 : ℤ) ∣ m)
    (hseven : ¬ (7 : ℤ) ∣ m) :
    IsCoprime m (84 : ℤ) := by
  have hm2 : IsCoprime m (2 : ℤ) :=
    Int.isCoprime_two_right.mpr hodd
  have hm4 : IsCoprime m ((2 : ℤ) ^ 2) :=
    hm2.pow_right
  have hm3 : IsCoprime m (3 : ℤ) :=
    ((irreducible_int_of_nat_prime (by norm_num : Nat.Prime 3))
      |>.coprime_iff_not_dvd.mpr hthree).symm
  have hm7 : IsCoprime m (7 : ℤ) :=
    ((irreducible_int_of_nat_prime (by norm_num : Nat.Prime 7))
      |>.coprime_iff_not_dvd.mpr hseven).symm
  simpa only [show ((2 : ℤ) ^ 2 * 3) * 7 = 84 by norm_num] using
    (hm4.mul_right hm3).mul_right hm7

/-- Nondivisibility by the prime `37` is exactly enough for coprimality with
`37`. -/
theorem isCoprime_37_of_not_dvd
    {m : ℤ}
    (h37 : ¬ (37 : ℤ) ∣ m) :
    IsCoprime m (37 : ℤ) :=
  ((irreducible_int_of_nat_prime (by norm_num : Nat.Prime 37))
    |>.coprime_iff_not_dvd.mpr h37).symm

/-- Combined coprimality package produced by the four saturation
conditions. -/
theorem isCoprime_84_and_37_of_saturation
    {m : ℤ}
    (hodd : Odd m)
    (hthree : ¬ (3 : ℤ) ∣ m)
    (hseven : ¬ (7 : ℤ) ∣ m)
    (h37 : ¬ (37 : ℤ) ∣ m) :
    IsCoprime m (84 : ℤ) ∧ IsCoprime m (37 : ℤ) :=
  ⟨isCoprime_84_of_odd_of_not_dvd_three_of_not_dvd_seven
      hodd hthree hseven,
    isCoprime_37_of_not_dvd h37⟩

end GaussianIndexCoprime
end Cuboid2
