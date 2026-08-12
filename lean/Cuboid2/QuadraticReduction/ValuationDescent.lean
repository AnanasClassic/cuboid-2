import Cuboid2.QuadraticReduction.Characters
import Cuboid2.QuadraticReduction.C012
import Cuboid2.QuadraticReduction.SquareclassDescent
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Common-character valuation descent

This module checks the full elementary valuation argument behind C040.  From
`z² = 2kh` and the exact elliptic `h,k` relation it proves:

* `v_r(k)` is even at every odd prime;
* `v_2(k)` is odd;
* consequently `k = 2 ε u²` and `h = ε v²` for one physical sign `ε`.

The `2`-adic unit cases are excluded by explicit `ZMod 8` and `ZMod 32`
discriminant certificates.  Global square-class reconstruction uses the
factorizations of the reduced rational numerator and denominator.
-/

namespace Cuboid2

private theorem quadratic_constant_ne_zero (k : ℚ) :
    k ^ 2 + 4 * k - 4 ≠ 0 := by
  intro h
  have hs : (k + 2) ^ 2 = 8 := by nlinarith
  have : IsSquare (8 : ℚ) :=
    ⟨k + 2, by simpa [pow_two] using hs.symm⟩
  exact (by norm_num [Rat.isSquare_iff] : ¬ IsSquare (8 : ℚ)) this

private theorem valuation_three_terms_no_unique_min
    {p : ℕ} [Fact p.Prime] {a b c : ℚ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hsum : a + b + c = 0) :
    ¬(padicValRat p a < padicValRat p b ∧
      padicValRat p a < padicValRat p c) := by
  rintro ⟨hab, hac⟩
  have hbc : b + c = -a := by linarith
  have hbc0 : b + c ≠ 0 := by rw [hbc]; exact neg_ne_zero.mpr ha
  have hv := padicValRat.lt_add_of_lt hbc0 hab hac
  rw [hbc, padicValRat.neg] at hv
  exact (lt_irrefl _) hv

private theorem odd_prime_val_two_eq_zero
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    padicValRat p (2 : ℚ) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  simp [padicValRat, padicValInt, hp.ne_one,
    Nat.dvd_prime Nat.prime_two, hp2]

private theorem odd_prime_val_four_eq_zero
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    padicValRat p (4 : ℚ) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [show (4 : ℚ) = 2 * 2 by norm_num,
    padicValRat.mul (by norm_num) (by norm_num),
    odd_prime_val_two_eq_zero hp hp2]
  norm_num

private theorem odd_prime_k_coefficients_positive
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {k : ℚ} (hk : k ≠ 0) (halpha : 0 < padicValRat p k) :
    padicValRat p (k ^ 2 + 2) = 0 ∧
      padicValRat p (k ^ 2 + 4 * k - 4) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hv2 := odd_prime_val_two_eq_zero hp hp2
  have hv4 := odd_prime_val_four_eq_zero hp hp2
  have hk2 : k ^ 2 ≠ 0 := pow_ne_zero 2 hk
  have hk2v : padicValRat p (k ^ 2) = 2 * padicValRat p k := by simp
  have hk2p2 : k ^ 2 + 2 ≠ 0 := by nlinarith [sq_nonneg k]
  have hfirst : padicValRat p (2 + k ^ 2) = 0 := by
    rw [padicValRat.add_eq_of_lt
      (by simpa [add_comm] using hk2p2) (by norm_num) hk2]
    · exact hv2
    · rw [hv2, hk2v]
      omega
  constructor
  · simpa [add_comm] using hfirst
  · have h4k : 4 * k ≠ 0 := mul_ne_zero (by norm_num) hk
    have h4kv : padicValRat p (4 * k) = padicValRat p k := by
      rw [padicValRat.mul (by norm_num) hk, hv4]
      omega
    have hinner0 : k ^ 2 + 4 * k ≠ 0 := by
      intro hzero
      have : k = -4 := by
        apply (mul_left_cancel₀ hk)
        nlinarith
      rw [this, padicValRat.neg, hv4] at halpha
      omega
    have hinnerLower :
        0 < padicValRat p (k ^ 2 + 4 * k) := by
      have hmin := padicValRat.min_le_padicValRat_add (p := p) hinner0
      rw [hk2v, h4kv] at hmin
      omega
    have hconst0 : k ^ 2 + 4 * k + -4 ≠ 0 := by
      convert quadratic_constant_ne_zero k using 1 <;> ring
    have hvneg4 : padicValRat p (-4 : ℚ) = 0 := by
      rw [padicValRat.neg, hv4]
    have hval := padicValRat.add_eq_of_lt (p := p)
      (q := (-4 : ℚ)) (r := k ^ 2 + 4 * k)
      (by simpa [add_comm] using hconst0)
      (by norm_num) hinner0 (by omega)
    calc
      padicValRat p (k ^ 2 + 4 * k - 4) =
          padicValRat p (-4 + (k ^ 2 + 4 * k)) := by congr 1 <;> ring
      _ = padicValRat p (-4) := hval
      _ = 0 := hvneg4

private theorem odd_prime_k_coefficients_negative
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {k : ℚ} (hk : k ≠ 0) (halpha : padicValRat p k < 0) :
    padicValRat p (k ^ 2 + 2) = 2 * padicValRat p k ∧
      padicValRat p (k ^ 2 + 4 * k - 4) = 2 * padicValRat p k := by
  letI : Fact p.Prime := ⟨hp⟩
  have hv2 := odd_prime_val_two_eq_zero hp hp2
  have hv4 := odd_prime_val_four_eq_zero hp hp2
  have hk2 : k ^ 2 ≠ 0 := pow_ne_zero 2 hk
  have hk2v : padicValRat p (k ^ 2) = 2 * padicValRat p k := by simp
  have hk2p2 : k ^ 2 + 2 ≠ 0 := by nlinarith [sq_nonneg k]
  constructor
  · rw [padicValRat.add_eq_of_lt hk2p2 hk2 (by norm_num)]
    · exact hk2v
    · rw [hk2v, hv2]
      omega
  · have h4k : 4 * k ≠ 0 := mul_ne_zero (by norm_num) hk
    have h4kv : padicValRat p (4 * k) = padicValRat p k := by
      rw [padicValRat.mul (by norm_num) hk, hv4]
      omega
    have hinner0 : 4 * k + -4 ≠ 0 := by
      intro hzero
      have : k = 1 := by linarith
      rw [this, padicValRat.one] at halpha
      omega
    have hinnerVal : padicValRat p (4 * k + -4) = padicValRat p k := by
      have hvneg4 : padicValRat p (-4 : ℚ) = 0 := by
        rw [padicValRat.neg, hv4]
      rw [padicValRat.add_eq_of_lt hinner0 h4k (by norm_num)]
      · exact h4kv
      · rw [h4kv, hvneg4]
        exact halpha
    have hconst0 : k ^ 2 + (4 * k + -4) ≠ 0 := by
      convert quadratic_constant_ne_zero k using 1 <;> ring
    have hval := padicValRat.add_eq_of_lt (p := p) hconst0 hk2 hinner0
      (by rw [hk2v, hinnerVal]; omega)
    calc
      padicValRat p (k ^ 2 + 4 * k - 4) =
          padicValRat p (k ^ 2 + (4 * k + -4)) := by congr 1 <;> ring
      _ = padicValRat p (k ^ 2) := hval
      _ = 2 * padicValRat p k := hk2v

theorem odd_prime_k_valuation_even
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {k h z : ℚ} (hk : k ≠ 0) (hh : h ≠ 0)
    (hz : z ^ 2 = 2 * k * h)
    (hrel : e1HKRelation k h = 0) :
    Even (padicValRat p k) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0] at hz
    have hzero : 2 * k * h = 0 := by simpa using hz.symm
    exact (mul_ne_zero (mul_ne_zero (by norm_num) hk) hh) hzero
  let α := padicValRat p k
  let β := padicValRat p h
  let γ := padicValRat p z
  have hv2 := odd_prime_val_two_eq_zero hp hp2
  have hzval : 2 * γ = α + β := by
    have hv := congrArg (padicValRat p) hz
    simp only [padicValRat.pow] at hv
    rw [padicValRat.mul (mul_ne_zero (by norm_num) hk) hh,
      padicValRat.mul (by norm_num) hk, hv2] at hv
    dsimp [α, β, γ]
    omega
  by_cases hapos : 0 < α
  · have hcoeff := odd_prime_k_coefficients_positive hp hp2 hk hapos
    have hsum :
        h ^ 2 + (-(k ^ 2 + 2) * h) + (k ^ 2 + 4 * k - 4) = 0 := by
      unfold e1HKRelation at hrel
      linear_combination hrel
    have hA0 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
    have hcoef0 : k ^ 2 + 2 ≠ 0 := by nlinarith [sq_nonneg k]
    have hB0 : -(k ^ 2 + 2) * h ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr hcoef0) hh
    have hC0 := quadratic_constant_ne_zero k
    have hvA : padicValRat p (h ^ 2) = 2 * β := by simp [β]
    have hvB : padicValRat p (-(k ^ 2 + 2) * h) = β := by
      rw [padicValRat.mul (neg_ne_zero.mpr hcoef0) hh,
        padicValRat.neg, hcoeff.1]
      simp [β]
    have hvC : padicValRat p (k ^ 2 + 4 * k - 4) = 0 := hcoeff.2
    have hbzero : β = 0 := by
      by_contra hb
      by_cases hbpos : 0 < β
      · have hu := valuation_three_terms_no_unique_min (p := p) hC0 hA0 hB0
          (by linarith [hsum])
        rw [hvC, hvA, hvB] at hu
        exact hu ⟨by omega, by omega⟩
      · have hbneg : β < 0 := by omega
        have hu := valuation_three_terms_no_unique_min (p := p) hA0 hB0 hC0 hsum
        rw [hvA, hvB, hvC] at hu
        exact hu ⟨by omega, by omega⟩
    refine ⟨γ, ?_⟩
    rw [hbzero] at hzval
    omega
  · by_cases haneg : α < 0
    · have hcoeff := odd_prime_k_coefficients_negative hp hp2 hk haneg
      have hsum :
          h ^ 2 + (-(k ^ 2 + 2) * h) + (k ^ 2 + 4 * k - 4) = 0 := by
        unfold e1HKRelation at hrel
        linear_combination hrel
      have hA0 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
      have hcoef0 : k ^ 2 + 2 ≠ 0 := by nlinarith [sq_nonneg k]
      have hB0 : -(k ^ 2 + 2) * h ≠ 0 :=
        mul_ne_zero (neg_ne_zero.mpr hcoef0) hh
      have hC0 := quadratic_constant_ne_zero k
      have hvA : padicValRat p (h ^ 2) = 2 * β := by simp [β]
      have hvB :
          padicValRat p (-(k ^ 2 + 2) * h) = 2 * α + β := by
        rw [padicValRat.mul (neg_ne_zero.mpr hcoef0) hh,
          padicValRat.neg, hcoeff.1]
      have hvC : padicValRat p (k ^ 2 + 4 * k - 4) = 2 * α := hcoeff.2
      have hbeta : β = 0 ∨ β = 2 * α := by
        by_contra hcases
        push Not at hcases
        have hnum :
            (2 * β < 2 * α + β ∧ 2 * β < 2 * α) ∨
            (2 * α + β < 2 * β ∧ 2 * α + β < 2 * α) ∨
            (2 * α < 2 * β ∧ 2 * α < 2 * α + β) := by
          omega
        rcases hnum with hnum | hnum | hnum
        · have hu := valuation_three_terms_no_unique_min (p := p)
            hA0 hB0 hC0 hsum
          rw [hvA, hvB, hvC] at hu
          exact hu hnum
        · have hsum' : (-(k ^ 2 + 2) * h) + h ^ 2 +
              (k ^ 2 + 4 * k - 4) = 0 := by linarith [hsum]
          have hu := valuation_three_terms_no_unique_min (p := p)
            hB0 hA0 hC0 hsum'
          rw [hvA, hvB, hvC] at hu
          exact hu hnum
        · have hsum' : (k ^ 2 + 4 * k - 4) + h ^ 2 +
              (-(k ^ 2 + 2) * h) = 0 := by linarith [hsum]
          have hu := valuation_three_terms_no_unique_min (p := p)
            hC0 hA0 hB0 hsum'
          rw [hvA, hvB, hvC] at hu
          exact hu hnum
      rcases hbeta with hbeta | hbeta
      · refine ⟨γ, ?_⟩
        rw [hbeta] at hzval
        omega
      · refine ⟨γ - α, ?_⟩
        omega
    · have ha0 : α = 0 := by omega
      exact ⟨0, by omega⟩

private theorem two_val_two : padicValRat 2 (2 : ℚ) = 1 := by
  norm_num [padicValRat, padicValInt, padicValNat]

private theorem two_val_four : padicValRat 2 (4 : ℚ) = 2 := by
  rw [show (4 : ℚ) = 2 * 2 by norm_num,
    padicValRat.mul (p := 2) (by norm_num) (by norm_num), two_val_two]
  norm_num

private theorem two_k_coefficients_negative
    {k : ℚ} (hk : k ≠ 0) (halpha : padicValRat 2 k < 0) :
    padicValRat 2 (k ^ 2 + 2) = 2 * padicValRat 2 k ∧
      padicValRat 2 (k ^ 2 + 4 * k - 4) = 2 * padicValRat 2 k := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk2 : k ^ 2 ≠ 0 := pow_ne_zero 2 hk
  have hk2v : padicValRat 2 (k ^ 2) = 2 * padicValRat 2 k := by simp
  have hk2p2 : k ^ 2 + 2 ≠ 0 := by nlinarith [sq_nonneg k]
  constructor
  · rw [padicValRat.add_eq_of_lt hk2p2 hk2 (by norm_num)]
    · exact hk2v
    · rw [hk2v, two_val_two]
      omega
  · have h4k : 4 * k ≠ 0 := mul_ne_zero (by norm_num) hk
    have h4kv : padicValRat 2 (4 * k) = 2 + padicValRat 2 k := by
      rw [padicValRat.mul (by norm_num) hk, two_val_four]
    have hinner0 : 4 * k + -4 ≠ 0 := by
      intro hzero
      have : k = 1 := by linarith
      rw [this, padicValRat.one] at halpha
      omega
    have hinnerLower :
        2 * padicValRat 2 k < padicValRat 2 (4 * k + -4) := by
      have hmin := padicValRat.min_le_padicValRat_add (p := 2) hinner0
      have hvneg4 : padicValRat 2 (-4 : ℚ) = 2 := by
        rw [padicValRat.neg, two_val_four]
      rw [h4kv, hvneg4] at hmin
      omega
    have hconst0 : k ^ 2 + (4 * k + -4) ≠ 0 := by
      convert quadratic_constant_ne_zero k using 1 <;> ring
    have hval := padicValRat.add_eq_of_lt (p := 2) hconst0 hk2 hinner0
      (by rw [hk2v]; exact hinnerLower)
    calc
      padicValRat 2 (k ^ 2 + 4 * k - 4) =
          padicValRat 2 (k ^ 2 + (4 * k + -4)) := by congr 1 <;> ring
      _ = padicValRat 2 (k ^ 2) := hval
      _ = 2 * padicValRat 2 k := hk2v

private theorem two_negative_k_valuation_odd
    {k h z : ℚ} (hk : k ≠ 0) (hh : h ≠ 0)
    (hz : z ^ 2 = 2 * k * h)
    (hrel : e1HKRelation k h = 0)
    (halpha : padicValRat 2 k < 0) :
    Odd (padicValRat 2 k) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0] at hz
    have hzero : 2 * k * h = 0 := by simpa using hz.symm
    exact (mul_ne_zero (mul_ne_zero (by norm_num) hk) hh) hzero
  let α := padicValRat 2 k
  let β := padicValRat 2 h
  let γ := padicValRat 2 z
  have hzval : 2 * γ = 1 + α + β := by
    have hv := congrArg (padicValRat 2) hz
    simp only [padicValRat.pow] at hv
    rw [padicValRat.mul (mul_ne_zero (by norm_num) hk) hh,
      padicValRat.mul (by norm_num) hk, two_val_two] at hv
    dsimp [α, β, γ]
    omega
  have hcoeff := two_k_coefficients_negative hk halpha
  have hsum :
      h ^ 2 + (-(k ^ 2 + 2) * h) + (k ^ 2 + 4 * k - 4) = 0 := by
    unfold e1HKRelation at hrel
    linear_combination hrel
  have hA0 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hcoef0 : k ^ 2 + 2 ≠ 0 := by nlinarith [sq_nonneg k]
  have hB0 : -(k ^ 2 + 2) * h ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hcoef0) hh
  have hC0 := quadratic_constant_ne_zero k
  have hvA : padicValRat 2 (h ^ 2) = 2 * β := by simp [β]
  have hvB :
      padicValRat 2 (-(k ^ 2 + 2) * h) = 2 * α + β := by
    rw [padicValRat.mul (neg_ne_zero.mpr hcoef0) hh,
      padicValRat.neg, hcoeff.1]
  have hvC : padicValRat 2 (k ^ 2 + 4 * k - 4) = 2 * α := hcoeff.2
  have hbeta : β = 0 ∨ β = 2 * α := by
    by_contra hcases
    push Not at hcases
    have hnum :
        (2 * β < 2 * α + β ∧ 2 * β < 2 * α) ∨
        (2 * α + β < 2 * β ∧ 2 * α + β < 2 * α) ∨
        (2 * α < 2 * β ∧ 2 * α < 2 * α + β) := by
      omega
    rcases hnum with hnum | hnum | hnum
    · have hu := valuation_three_terms_no_unique_min (p := 2)
        hA0 hB0 hC0 hsum
      rw [hvA, hvB, hvC] at hu
      exact hu hnum
    · have hsum' : (-(k ^ 2 + 2) * h) + h ^ 2 +
          (k ^ 2 + 4 * k - 4) = 0 := by linarith [hsum]
      have hu := valuation_three_terms_no_unique_min (p := 2)
        hB0 hA0 hC0 hsum'
      rw [hvA, hvB, hvC] at hu
      exact hu hnum
    · have hsum' : (k ^ 2 + 4 * k - 4) + h ^ 2 +
          (-(k ^ 2 + 2) * h) = 0 := by linarith [hsum]
      have hu := valuation_three_terms_no_unique_min (p := 2)
        hC0 hA0 hB0 hsum'
      rw [hvA, hvB, hvC] at hu
      exact hu hnum
  rcases hbeta with hbeta | hbeta
  · refine ⟨γ - 1, ?_⟩
    rw [hbeta] at hzval
    omega
  · refine ⟨2 * α - γ, ?_⟩
    omega

/-- Numerator of `k⁴-16k+20` after multiplication by the fourth power
of a denominator. -/
def hkDiscriminantNumerator (m n : ℤ) : ℤ :=
  m ^ 4 - 16 * m * n ^ 3 + 20 * n ^ 4

private theorem hk_discriminant_num_isSquare
    {k h : ℚ} (hrel : e1HKRelation k h = 0) :
    IsSquare (hkDiscriminantNumerator k.num k.den) := by
  have hn : (k.den : ℚ) ≠ 0 := by exact_mod_cast k.den_ne_zero
  have hdisc :
      (2 * h - (k ^ 2 + 2)) ^ 2 = k ^ 4 - 16 * k + 20 := by
    unfold e1HKRelation at hrel
    nlinarith
  have hdisc' := hdisc
  rw [← k.num_div_den] at hdisc'
  field_simp [hn] at hdisc'
  have hclear :
      (2 * h * (k.den : ℚ) ^ 2 -
          ((k.num : ℚ) ^ 2 + 2 * (k.den : ℚ) ^ 2)) ^ 2 =
        ((hkDiscriminantNumerator k.num k.den : ℤ) : ℚ) := by
    calc
      _ = (k.num : ℚ) * ((k.num : ℚ) ^ 3 - (k.den : ℚ) ^ 3 * 16) +
          (k.den : ℚ) ^ 4 * 20 := hdisc'
      _ = _ := by
        push_cast
        simp [hkDiscriminantNumerator]
        ring
  have hrat :
      IsSquare ((hkDiscriminantNumerator k.num k.den : ℤ) : ℚ) := by
    refine ⟨2 * h * (k.den : ℚ) ^ 2 -
      ((k.num : ℚ) ^ 2 + 2 * (k.den : ℚ) ^ 2), ?_⟩
    simpa [pow_two] using hclear.symm
  exact Rat.isSquare_intCast_iff.mp hrat

private theorem hk_discriminant_odd_odd_not_square (a b : ℤ) :
    ¬ IsSquare (hkDiscriminantNumerator (2 * a + 1) (2 * b + 1)) := by
  rintro ⟨w, hw⟩
  have hw' :
      w ^ 2 = hkDiscriminantNumerator (2 * a + 1) (2 * b + 1) := by
    simpa [pow_two] using hw.symm
  have hmod :
      ((w ^ 2 : ℤ) : ZMod 8) =
        ((hkDiscriminantNumerator (2 * a + 1) (2 * b + 1) : ℤ) : ZMod 8) :=
    congrArg (fun x : ℤ => (x : ZMod 8)) hw'
  have hfinite : ∀ A B : ZMod 8,
      (2 * A + 1) ^ 4 -
          16 * (2 * A + 1) * (2 * B + 1) ^ 3 +
          20 * (2 * B + 1) ^ 4 = 5 := by decide
  have hcast :
      ((hkDiscriminantNumerator (2 * a + 1) (2 * b + 1) : ℤ) : ZMod 8) = 5 := by
    simp [hkDiscriminantNumerator]
    exact hfinite _ _
  have hsquare : ∀ W : ZMod 8, W ^ 2 ≠ 5 := by decide
  apply hsquare (w : ZMod 8)
  rw [hcast] at hmod
  simpa using hmod

private theorem hk_discriminant_four_odd_not_square (a b : ℤ) :
    ¬ IsSquare (hkDiscriminantNumerator (4 * a) (2 * b + 1)) := by
  rintro ⟨w, hw⟩
  have hw' :
      w ^ 2 = hkDiscriminantNumerator (4 * a) (2 * b + 1) := by
    simpa [pow_two] using hw.symm
  have hmod :
      ((w ^ 2 : ℤ) : ZMod 32) =
        ((hkDiscriminantNumerator (4 * a) (2 * b + 1) : ℤ) : ZMod 32) :=
    congrArg (fun x : ℤ => (x : ZMod 32)) hw'
  have hfinite : ∀ A B : ZMod 32,
      (4 * A) ^ 4 - 16 * (4 * A) * (2 * B + 1) ^ 3 +
          20 * (2 * B + 1) ^ 4 = 20 := by decide
  have hcast :
      ((hkDiscriminantNumerator (4 * a) (2 * b + 1) : ℤ) : ZMod 32) = 20 := by
    simp [hkDiscriminantNumerator]
    exact hfinite _ _
  have hsquare : ∀ W : ZMod 32, W ^ 2 ≠ 20 := by decide
  apply hsquare (w : ZMod 32)
  rw [hcast] at hmod
  simpa using hmod

private theorem rat_two_num_or_den_val_zero
    {k : ℚ} (hk : k ≠ 0) :
    padicValInt 2 k.num = 0 ∨ padicValNat 2 k.den = 0 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnum0 : k.num.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hk)
  have hden0 : k.den ≠ 0 := k.den_ne_zero
  by_contra h
  push Not at h
  have hnumDiv : 2 ∣ k.num.natAbs := by
    apply (dvd_iff_padicValNat_ne_zero (p := 2) hnum0).2
    simpa [padicValInt] using h.1
  have hdenDiv : 2 ∣ k.den :=
    (dvd_iff_padicValNat_ne_zero (p := 2) hden0).2 h.2
  exact (Nat.not_coprime_of_dvd_of_dvd (d := 2) (by norm_num)
    hnumDiv hdenDiv) k.reduced

private theorem int_odd_of_two_val_zero
    {m : ℤ} (hm : m ≠ 0) (hval : padicValInt 2 m = 0) :
    Odd m := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Int.natAbs_odd]
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  intro hdiv
  have hne : padicValNat 2 m.natAbs ≠ 0 :=
    (dvd_iff_padicValNat_ne_zero (p := 2)
      (Int.natAbs_ne_zero.mpr hm)).1 hdiv
  exact hne (by simpa [padicValInt] using hval)

private theorem nat_odd_of_two_val_zero
    {n : ℕ} (hn : n ≠ 0) (hval : padicValNat 2 n = 0) :
    Odd n := by
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  intro hdiv
  exact ((dvd_iff_padicValNat_ne_zero (p := 2) hn).1 hdiv) hval

theorem two_k_valuation_odd
    {k h z : ℚ} (hk : k ≠ 0) (hh : h ≠ 0)
    (hz : z ^ 2 = 2 * k * h)
    (hrel : e1HKRelation k h = 0) :
    Odd (padicValRat 2 k) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let α := padicValRat 2 k
  by_cases haneg : α < 0
  · exact two_negative_k_valuation_odd hk hh hz hrel haneg
  have ha_nonneg : 0 ≤ α := by omega
  have honezero := rat_two_num_or_den_val_zero hk
  have hdef :
      α = (padicValInt 2 k.num : ℤ) - (padicValNat 2 k.den : ℤ) := rfl
  have hnum0 : k.num ≠ 0 := Rat.num_ne_zero.mpr hk
  have hden0 : k.den ≠ 0 := k.den_ne_zero
  have hdisc := hk_discriminant_num_isSquare hrel
  by_cases ha0 : α = 0
  · have heq :
        padicValInt 2 k.num = padicValNat 2 k.den := by omega
    have hnumVal : padicValInt 2 k.num = 0 := by
      rcases honezero with h | h
      · exact h
      · omega
    have hdenVal : padicValNat 2 k.den = 0 := by omega
    have hnumOdd := int_odd_of_two_val_zero hnum0 hnumVal
    have hdenOdd := nat_odd_of_two_val_zero hden0 hdenVal
    rcases odd_iff_exists_bit1.mp hnumOdd with ⟨a, ha⟩
    rcases odd_iff_exists_bit1.mp hdenOdd with ⟨b, hb⟩
    have hbInt : (k.den : ℤ) = 2 * (b : ℤ) + 1 := by exact_mod_cast hb
    rw [ha, hbInt] at hdisc
    exact False.elim (hk_discriminant_odd_odd_not_square a b hdisc)
  · by_cases ha1 : α = 1
    · exact ⟨0, by omega⟩
    · have ha2 : 2 ≤ α := by omega
      have hdenVal : padicValNat 2 k.den = 0 := by
        rcases honezero with hnumVal | hdenVal
        · have : padicValInt 2 k.num = 0 := hnumVal
          omega
        · exact hdenVal
      have hnumVal2 : 2 ≤ padicValInt 2 k.num := by omega
      have hnumAbs0 : k.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hnum0
      have hfourNat : 2 ^ 2 ∣ k.num.natAbs := by
        apply (Nat.pow_dvd_iff_le_padicValNat (p := 2)
          (by norm_num) hnumAbs0).2
        simpa [padicValInt] using hnumVal2
      have hfourInt : (4 : ℤ) ∣ k.num := by
        have hcast : ((4 : ℕ) : ℤ) ∣ k.num :=
          Int.ofNat_dvd_left.mpr (by simpa using hfourNat)
        norm_num at hcast ⊢
        exact hcast
      rcases hfourInt with ⟨a, ha⟩
      have hdenOdd := nat_odd_of_two_val_zero hden0 hdenVal
      rcases odd_iff_exists_bit1.mp hdenOdd with ⟨b, hb⟩
      have hbInt : (k.den : ℤ) = 2 * (b : ℤ) + 1 := by exact_mod_cast hb
      rw [ha, hbInt] at hdisc
      exact False.elim (hk_discriminant_four_odd_not_square a b hdisc)

private theorem rat_factorization_sum
    {k : ℚ} (hk : k ≠ 0) (r : ℕ) (hr : r.Prime) :
    (k.num.natAbs * k.den).factorization r =
      k.num.natAbs.factorization r + k.den.factorization r := by
  rw [Nat.factorization_mul
    (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hk)) k.den_ne_zero]
  rfl

private theorem rat_padicVal_eq_factorization_sub
    {k : ℚ} (r : ℕ) (hr : r.Prime) :
    padicValRat r k =
      (k.num.natAbs.factorization r : ℤ) -
        (k.den.factorization r : ℤ) := by
  simp only [padicValRat_def, padicValInt, Nat.factorization_def _ hr]

private theorem rat_num_den_product_two_dvd
    {k : ℚ} (hk : k ≠ 0) (hodd : Odd (padicValRat 2 k)) :
    2 ∣ k.num.natAbs * k.den := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsum := rat_factorization_sum hk 2 Nat.prime_two
  have hval := rat_padicVal_eq_factorization_sub (k := k) 2 Nat.prime_two
  rcases hodd with ⟨j, hj⟩
  have hfactorNe :
      (k.num.natAbs * k.den).factorization 2 ≠ 0 := by
    intro hzero
    rw [hsum] at hzero
    have hnumZero : k.num.natAbs.factorization 2 = 0 := by omega
    have hdenZero : k.den.factorization 2 = 0 := by omega
    rw [hnumZero, hdenZero] at hval
    omega
  exact (dvd_iff_padicValNat_ne_zero (p := 2)
    (mul_ne_zero (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hk))
      k.den_ne_zero)).2 (by
        rw [← Nat.factorization_def _ Nat.prime_two]
        exact hfactorNe)

private theorem nat_sum_odd_of_int_sub_odd
    (a b : ℕ) (h : Odd ((a : ℤ) - (b : ℤ))) :
    Odd (a + b) := by
  have hInt : Odd (((a + b : ℕ) : ℤ)) := by
    rw [show (((a + b : ℕ) : ℤ)) =
      ((a : ℤ) - (b : ℤ)) + 2 * (b : ℤ) by push_cast; ring]
    exact h.add_even (even_two_mul (b : ℤ))
  exact (Int.odd_coe_nat (a + b)).mp hInt

private theorem nat_sum_even_of_int_sub_even
    (a b : ℕ) (h : Even ((a : ℤ) - (b : ℤ))) :
    Even (a + b) := by
  have hInt : Even (((a + b : ℕ) : ℤ)) := by
    rw [show (((a + b : ℕ) : ℤ)) =
      ((a : ℤ) - (b : ℤ)) + 2 * (b : ℤ) by push_cast; ring]
    exact h.add (even_two_mul (b : ℤ))
  exact (Int.even_coe_nat (a + b)).mp hInt

private theorem half_num_den_product_prime_factorization_even
    {k : ℚ} (hk : k ≠ 0)
    (hodd : Odd (padicValRat 2 k))
    (heven : ∀ r : ℕ, r.Prime → r ≠ 2 → Even (padicValRat r k))
    (r : ℕ) (hr : r.Prime) :
    Even (((k.num.natAbs * k.den) / 2).factorization r) := by
  have htwo := rat_num_den_product_two_dvd hk hodd
  rw [Nat.factorization_div htwo]
  simp only [Finsupp.coe_tsub, Pi.sub_apply]
  have hsum := rat_factorization_sum hk r hr
  have hval := rat_padicVal_eq_factorization_sub (k := k) r hr
  by_cases hr2 : r = 2
  · subst r
    have htwoFactor : ((2 : ℕ).factorization 2) = 1 := by
      norm_num [Nat.factorization_def, padicValNat]
    rw [htwoFactor]
    have hsumOdd :
        Odd ((k.num.natAbs * k.den).factorization 2) := by
      rw [hsum]
      apply nat_sum_odd_of_int_sub_odd
      rwa [← hval]
    rcases hsumOdd with ⟨d, hd⟩
    have hpos : 1 ≤ (k.num.natAbs * k.den).factorization 2 := by omega
    refine ⟨d, ?_⟩
    omega
  · have htwoFactor : ((2 : ℕ).factorization r) = 0 := by
      rw [Nat.factorization_def 2 hr]
      apply padicValNat.eq_zero_of_not_dvd
      intro hd
      have hcases := (Nat.dvd_prime Nat.prime_two).mp hd
      rcases hcases with h | h
      · exact hr.ne_one h
      · exact hr2 h
    rw [htwoFactor, Nat.sub_zero]
    rw [hsum]
    apply nat_sum_even_of_int_sub_even
    have hvEven := heven r hr hr2
    rwa [hval] at hvEven

private theorem rat_signed_two_square_of_valuations
    {k : ℚ} (hk : k ≠ 0)
    (hodd : Odd (padicValRat 2 k))
    (heven : ∀ r : ℕ, r.Prime → r ≠ 2 → Even (padicValRat r k)) :
    ∃ ε : PhysicalSign, ∃ u : ℚ,
      u ≠ 0 ∧ k = 2 * ε.value * u ^ 2 := by
  let N := k.num.natAbs * k.den
  have hN0 : N ≠ 0 :=
    mul_ne_zero (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hk))
      k.den_ne_zero
  have htwo : 2 ∣ N := rat_num_den_product_two_dvd hk hodd
  have hhalf0 : N / 2 ≠ 0 :=
    ne_of_gt (Nat.div_pos (Nat.le_of_dvd (by omega) htwo) (by norm_num))
  have hhalfSquare : IsSquare (N / 2) :=
    nat_isSquare_of_even_factorization hhalf0
      (half_num_den_product_prime_factorization_even hk hodd heven)
  rcases hhalfSquare with ⟨d, hd⟩
  have hN : N = 2 * d ^ 2 := by
    calc
      N = 2 * (N / 2) := by omega
      _ = 2 * d ^ 2 := by rw [hd]; simp [pow_two]
  let u : ℚ := d / k.den
  have hd0 : d ≠ 0 := by
    intro hdZero
    rw [hdZero] at hN
    norm_num at hN
    exact hN0 hN
  have hu0 : u ≠ 0 := div_ne_zero (by exact_mod_cast hd0)
    (by exact_mod_cast k.den_ne_zero)
  by_cases hkNonneg : 0 ≤ k
  · refine ⟨PhysicalSign.positive, u, hu0, ?_⟩
    simp only [PhysicalSign.value_positive, mul_one]
    rw [← k.num_div_den]
    dsimp [u]
    have hnumNonneg : 0 ≤ k.num := by
      exact Rat.num_nonneg.mpr hkNonneg
    have hnumAbs : (k.num.natAbs : ℤ) = k.num :=
      Int.natAbs_of_nonneg hnumNonneg
    have hNInt :
        (k.num.natAbs : ℤ) * (k.den : ℤ) = 2 * (d : ℤ) ^ 2 := by
      exact_mod_cast hN
    rw [hnumAbs] at hNInt
    field_simp [k.den_ne_zero]
    exact_mod_cast hNInt
  · have hkNeg : k < 0 := lt_of_not_ge hkNonneg
    refine ⟨PhysicalSign.negative, u, hu0, ?_⟩
    simp only [PhysicalSign.value_negative]
    rw [← k.num_div_den]
    dsimp [u]
    have hnumNeg : k.num < 0 := by
      exact Rat.num_neg.mpr hkNeg
    have hnumAbs : (k.num.natAbs : ℤ) = -k.num := by
      rw [Int.natCast_natAbs, abs_of_neg hnumNeg]
    field_simp [k.den_ne_zero]
    have hNInt : -k.num * (k.den : ℤ) = 2 * (d : ℤ) ^ 2 := by
      have hcast :
          (k.num.natAbs : ℤ) * (k.den : ℤ) = 2 * (d : ℤ) ^ 2 := by
        exact_mod_cast hN
      rwa [hnumAbs] at hcast
    exact_mod_cast (by nlinarith [hNInt] :
      k.num * (k.den : ℤ) = -(2 * (d : ℤ) ^ 2))

/--
The common square equation and the elliptic `h,k` relation force exactly the
two signed square classes used by the direct `D+` reduction.
-/
theorem e1_hk_signed_squareclasses
    {k h z : ℚ} (hk : k ≠ 0) (hh : h ≠ 0)
    (hz : z ^ 2 = 2 * k * h)
    (hrel : e1HKRelation k h = 0) :
    ∃ ε : PhysicalSign, ∃ u v : ℚ,
      u ≠ 0 ∧ v ≠ 0 ∧
      k = 2 * ε.value * u ^ 2 ∧ h = ε.value * v ^ 2 := by
  have hodd := two_k_valuation_odd hk hh hz hrel
  have heven : ∀ r : ℕ, r.Prime → r ≠ 2 → Even (padicValRat r k) :=
    fun r hr hr2 => odd_prime_k_valuation_even hr hr2 hk hh hz hrel
  rcases rat_signed_two_square_of_valuations hk hodd heven with
    ⟨ε, u, hu, hkSquare⟩
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0] at hz
    have hzero : 2 * k * h = 0 := by simpa using hz.symm
    exact (mul_ne_zero (mul_ne_zero (by norm_num) hk) hh) hzero
  let v := z / (2 * u)
  have hv : v ≠ 0 := div_ne_zero hz0 (mul_ne_zero (by norm_num) hu)
  refine ⟨ε, u, v, hu, hv, hkSquare, ?_⟩
  dsimp [v]
  rw [hkSquare] at hz
  cases ε <;>
    simp [PhysicalSign.value] at hz ⊢ <;>
    field_simp [hu] <;>
    nlinarith [hz]

/--
The regular common-character locus reaches `D+` with square abscissa.  The
negative square class is discharged by the elementary modular obstruction;
the positive class supplies the explicit octic point.
-/
theorem e1_hk_to_dplus_square_abscissa
    {k h z : ℚ} (hk : k ≠ 0) (hh : h ≠ 0)
    (hz : z ^ 2 = 2 * k * h)
    (hrel : e1HKRelation k h = 0) :
    ∃ P : DPlusAffinePoint, P.HasSquareAbscissa := by
  rcases e1_hk_signed_squareclasses hk hh hz hrel with
    ⟨ε, u, v, hu, hv, hkSquare, hhSquare⟩
  cases ε with
  | positive =>
      have hkPos : k = 2 * u ^ 2 := by
        simpa [PhysicalSign.value] using hkSquare
      have hhPos : h = v ^ 2 := by
        simpa [PhysicalSign.value] using hhSquare
      let r : ℚ := v ^ 2 - 2 * u ^ 4 - 1
      have hr : r ^ 2 = 4 * u ^ 8 - 8 * u ^ 2 + 5 := by
        unfold e1HKRelation at hrel
        rw [hkPos, hhPos] at hrel
        dsimp [r]
        nlinarith
      exact e1_positive_octic_to_dplus u r hr
  | negative =>
      have hkNeg : k = -2 * u ^ 2 := by
        simpa [PhysicalSign.value] using hkSquare
      have hhNeg : h = -v ^ 2 := by
        simpa [PhysicalSign.value] using hhSquare
      exfalso
      apply e1_negative_squareclass_impossible (u ^ 2) v
      simpa [hkNeg, hhNeg] using hrel

end Cuboid2
