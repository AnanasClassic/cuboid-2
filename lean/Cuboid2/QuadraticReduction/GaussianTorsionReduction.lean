import Cuboid2.QuadraticReduction.GaussianFinite

/-!
# Arithmetic boundary for Gaussian torsion reduction

`GaussianFinite` exhaustively computes the orders of the two split special
fibres at `13` and `29`.  This file records the exact elementary number-theory
consequences of those closed computations.

There is deliberately no claim here that a characteristic-zero point reduces
to either finite group.  Such a claim requires a point-reduction homomorphism
and a proof that its kernel has no prime-to-residue-characteristic torsion;
neither result is currently supplied by Mathlib's elliptic-curve reduction API.
-/

namespace Cuboid2
namespace GaussianTorsionReduction

open GaussianFinite

/-! ## Bundled closed certificates -/

/-- The two closed `E₀` point-count certificates, kept together for downstream
use by an eventual point-reduction bridge. -/
theorem e0CertifiedReductionRows :
    (let plus := e0Coefficients 13 5
      let minus := e0Coefficients 13 8
      (finitePoints 13 plus.1 plus.2).length = 12 ∧
        (finitePoints 13 minus.1 minus.2).length = 18) ∧
    (let plus := e0Coefficients 29 12
      let minus := e0Coefficients 29 17
      (finitePoints 29 plus.1 plus.2).length = 28 ∧
        (finitePoints 29 minus.1 minus.2).length = 38) :=
  ⟨e0TorsionRows13, e0TorsionRows29⟩

/-- The two closed `E₁` point-count certificates, kept together for downstream
use by an eventual point-reduction bridge. -/
theorem e1CertifiedReductionRows :
    (let plus := e1Coefficients 13 5
      let minus := e1Coefficients 13 8
      (finitePoints 13 plus.1 plus.2).length = 16 ∧
        (finitePoints 13 minus.1 minus.2).length = 10) ∧
    (let plus := e1Coefficients 29 12
      let minus := e1Coefficients 29 17
      (finitePoints 29 plus.1 plus.2).length = 32 ∧
        (finitePoints 29 minus.1 minus.2).length = 22) :=
  ⟨e1TorsionRows13, e1TorsionRows29⟩

/-- The gcds of the certified `E₀` split-fibre orders. -/
theorem e0CertifiedOrderGcds :
    Nat.gcd 12 18 = 6 ∧ Nat.gcd 28 38 = 2 := by
  norm_num

/-- The gcds of the certified `E₁` split-fibre orders. -/
theorem e1CertifiedOrderGcds :
    Nat.gcd 16 10 = 2 ∧ Nat.gcd 32 22 = 2 := by
  norm_num

private theorem prime_eq_two_of_common_divisor
    {ℓ a b : ℕ} (hℓ : Nat.Prime ℓ) (ha : ℓ ∣ a) (hb : ℓ ∣ b)
    (hgcd : Nat.gcd a b = 2) : ℓ = 2 := by
  have htwo : ℓ ∣ 2 := by
    simpa [hgcd] using Nat.dvd_gcd ha hb
  exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp htwo

/-! ## Exact arithmetic consumers

The hypotheses below are only divisibility statements.  An eventual geometric
bridge must prove them from actual reduction maps; these theorems do not assume
or manufacture such maps.
-/

/-- Any prime satisfying the divisibilities forced by prime-to-`13` and
prime-to-`29` reduction into both split `E₀` fibres is `2`.

The exceptional case `ℓ = 29` is disposed of at `13`; every other prime is
disposed of by the two order-`28` and order-`38` fibres at `29`.
-/
theorem e0_prime_eq_two_of_reduction_order_divisibility
    {ℓ : ℕ} (hℓ : Nat.Prime ℓ)
    (h13 : ℓ ≠ 13 → ℓ ∣ 12 ∧ ℓ ∣ 18)
    (h29 : ℓ ≠ 29 → ℓ ∣ 28 ∧ ℓ ∣ 38) :
    ℓ = 2 := by
  by_cases h : ℓ = 29
  · subst ℓ
    have hdiv : 29 ∣ 12 := (h13 (by norm_num)).1
    norm_num at hdiv
  · obtain ⟨h28, h38⟩ := h29 h
    exact prime_eq_two_of_common_divisor hℓ h28 h38 (by norm_num)

/-- Any prime satisfying the divisibilities forced by prime-to-`13` and
prime-to-`29` reduction into both split `E₁` fibres is `2`.

The exceptional case `ℓ = 13` is disposed of at `29`; every other prime is
disposed of by the two order-`16` and order-`10` fibres at `13`.
-/
theorem e1_prime_eq_two_of_reduction_order_divisibility
    {ℓ : ℕ} (hℓ : Nat.Prime ℓ)
    (h13 : ℓ ≠ 13 → ℓ ∣ 16 ∧ ℓ ∣ 10)
    (h29 : ℓ ≠ 29 → ℓ ∣ 32 ∧ ℓ ∣ 22) :
    ℓ = 2 := by
  by_cases h : ℓ = 13
  · subst ℓ
    obtain ⟨h32, h22⟩ := h29 (by norm_num)
    exact prime_eq_two_of_common_divisor (by norm_num) h32 h22 (by norm_num)
  · obtain ⟨h16, h10⟩ := h13 h
    exact prime_eq_two_of_common_divisor hℓ h16 h10 (by norm_num)

/-- No odd prime can satisfy all prime-to-residue-characteristic divisibility
constraints for the certified `E₀` fibres. -/
theorem e0_no_odd_prime_of_reduction_order_divisibility
    {ℓ : ℕ} (hℓ : Nat.Prime ℓ) (hodd : Odd ℓ)
    (h13 : ℓ ≠ 13 → ℓ ∣ 12 ∧ ℓ ∣ 18)
    (h29 : ℓ ≠ 29 → ℓ ∣ 28 ∧ ℓ ∣ 38) :
    False := by
  have htwo := e0_prime_eq_two_of_reduction_order_divisibility hℓ h13 h29
  subst ℓ
  exact Nat.not_even_iff_odd.mpr hodd (by norm_num)

/-- No odd prime can satisfy all prime-to-residue-characteristic divisibility
constraints for the certified `E₁` fibres. -/
theorem e1_no_odd_prime_of_reduction_order_divisibility
    {ℓ : ℕ} (hℓ : Nat.Prime ℓ) (hodd : Odd ℓ)
    (h13 : ℓ ≠ 13 → ℓ ∣ 16 ∧ ℓ ∣ 10)
    (h29 : ℓ ≠ 29 → ℓ ∣ 32 ∧ ℓ ∣ 22) :
    False := by
  have htwo := e1_prime_eq_two_of_reduction_order_divisibility hℓ h13 h29
  subst ℓ
  exact Nat.not_even_iff_odd.mpr hodd (by norm_num)

/-- An odd natural number is `1` when every one of its prime divisors obeys
the certified prime-to-characteristic `E₀` order constraints.

This packages the elementary passage from prime divisors to an odd-order
component.  Its divisibility hypotheses remain the exact output required from
the missing geometric reduction bridge.
-/
theorem e0_odd_order_eq_one_of_reduction_order_divisibility
    {n : ℕ} (hodd : Odd n)
    (h13 : ∀ ℓ, Nat.Prime ℓ → ℓ ∣ n → ℓ ≠ 13 → ℓ ∣ 12 ∧ ℓ ∣ 18)
    (h29 : ∀ ℓ, Nat.Prime ℓ → ℓ ∣ n → ℓ ≠ 29 → ℓ ∣ 28 ∧ ℓ ∣ 38) :
    n = 1 := by
  by_contra hn
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd hn
  have htwo : ℓ = 2 :=
    e0_prime_eq_two_of_reduction_order_divisibility hℓ
      (h13 ℓ hℓ hℓn) (h29 ℓ hℓ hℓn)
  subst ℓ
  exact hodd.not_two_dvd_nat hℓn

/-- An odd natural number is `1` when every one of its prime divisors obeys
the certified prime-to-characteristic `E₁` order constraints.

As above, this is an arithmetic consumer, not a point-reduction theorem.
-/
theorem e1_odd_order_eq_one_of_reduction_order_divisibility
    {n : ℕ} (hodd : Odd n)
    (h13 : ∀ ℓ, Nat.Prime ℓ → ℓ ∣ n → ℓ ≠ 13 → ℓ ∣ 16 ∧ ℓ ∣ 10)
    (h29 : ∀ ℓ, Nat.Prime ℓ → ℓ ∣ n → ℓ ≠ 29 → ℓ ∣ 32 ∧ ℓ ∣ 22) :
    n = 1 := by
  by_contra hn
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd hn
  have htwo : ℓ = 2 :=
    e1_prime_eq_two_of_reduction_order_divisibility hℓ
      (h13 ℓ hℓ hℓn) (h29 ℓ hℓ hℓn)
  subst ℓ
  exact hodd.not_two_dvd_nat hℓn

end GaussianTorsionReduction
end Cuboid2
