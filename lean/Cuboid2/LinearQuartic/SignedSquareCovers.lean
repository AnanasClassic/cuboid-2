import Cuboid2.LinearQuartic.DirectSquareReduction
import Cuboid2.LinearQuartic.FermatAuxiliary
import Cuboid2.LinearQuartic.SharipovCompletion

/-!
# Signed-square covers for the Sharipov specialization

This file classifies the elementary positive cover

`v² = (u² + 1)(u⁴ + 6u² + 1)`.

Writing `u=m/n` in lowest terms leaves two parity cases.  If `m,n` have
opposite parity, the quartic factor is a square and Fermat's difference
descent applies to

`(m+n)⁴ + (m-n)⁴ = 2v²`.

If both are odd, half of the quartic factor is a square and Mathlib's
`not_fermat_42` applies directly.
-/

namespace Cuboid2

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The quadratic denominator-cleared factor of the positive cover. -/
def positiveCoverA (m n : ℤ) : ℤ :=
  m ^ 2 + n ^ 2

/-- The quartic denominator-cleared factor of the positive cover. -/
def positiveCoverB (m n : ℤ) : ℤ :=
  m ^ 4 + 6 * m ^ 2 * n ^ 2 + n ^ 4

theorem positiveCoverB_eq_A_sq_add (m n : ℤ) :
    positiveCoverB m n =
      positiveCoverA m n ^ 2 + 4 * (m * n) ^ 2 := by
  simp [positiveCoverA, positiveCoverB]
  ring

theorem positiveCover_fourth_identity (m n : ℤ) :
    (m + n) ^ 4 + (m - n) ^ 4 =
      2 * positiveCoverB m n := by
  simp [positiveCoverB]
  ring

/-- The quadratic factor is coprime to the product of the reduced
numerator and denominator. -/
theorem positiveCoverA_coprime_mul
    {m n : ℤ} (hmn : IsCoprime m n) :
    IsCoprime (positiveCoverA m n) (m * n) := by
  simpa [positiveCoverA] using Int.isCoprime_of_sq_sum' hmn

/-- In the opposite-parity case the two positive-cover factors are
coprime. -/
theorem positiveCover_coprime_of_A_odd
    {m n : ℤ} (hmn : IsCoprime m n)
    (hAodd : Odd (positiveCoverA m n)) :
    IsCoprime (positiveCoverA m n) (positiveCoverB m n) := by
  have hA2 : IsCoprime (positiveCoverA m n) (2 : ℤ) :=
    Int.isCoprime_two_right.mpr hAodd
  have hAmn : IsCoprime (positiveCoverA m n) (m * n) :=
    positiveCoverA_coprime_mul hmn
  have hAterm :
      IsCoprime (positiveCoverA m n) (4 * (m * n) ^ 2) := by
    have hA4 : IsCoprime (positiveCoverA m n) (4 : ℤ) := by
      simpa only [show (4 : ℤ) = 2 ^ 2 by norm_num] using hA2.pow_right
    exact hA4.mul_right hAmn.pow_right
  have hadd :=
    hAterm.add_mul_left_right (positiveCoverA m n)
  rw [positiveCoverB_eq_A_sq_add]
  simpa only [show
      4 * (m * n) ^ 2 +
          positiveCoverA m n * positiveCoverA m n =
        positiveCoverA m n ^ 2 + 4 * (m * n) ^ 2 by ring] using hadd

/-- If the reduced numerator and denominator are both odd, dividing both
positive-cover factors by two leaves coprime integers. -/
theorem positiveCover_halves_coprime
    {m n A₀ B₀ : ℤ} (hmn : IsCoprime m n)
    (hm : Odd m) (hn : Odd n)
    (hA : positiveCoverA m n = 2 * A₀)
    (hB : positiveCoverB m n = 2 * B₀) :
    IsCoprime A₀ B₀ := by
  have hAmn : IsCoprime (positiveCoverA m n) (m * n) :=
    positiveCoverA_coprime_mul hmn
  have hA₀mn : IsCoprime A₀ (m * n) := by
    rw [hA] at hAmn
    exact hAmn.of_mul_left_right
  obtain ⟨i, hi⟩ := odd_iff_exists_bit1.mp hm
  obtain ⟨j, hj⟩ := odd_iff_exists_bit1.mp hn
  have hA₀formula :
      A₀ = 2 * (i ^ 2 + i + j ^ 2 + j) + 1 := by
    rw [positiveCoverA, hi, hj] at hA
    nlinarith [hA]
  have hA₀odd : Odd A₀ := by
    exact odd_iff_exists_bit1.mpr
      ⟨i ^ 2 + i + j ^ 2 + j, hA₀formula⟩
  have hA₀two : IsCoprime A₀ (2 : ℤ) :=
    Int.isCoprime_two_right.mpr hA₀odd
  have hA₀base :
      IsCoprime A₀ (2 * (m * n) ^ 2) :=
    hA₀two.mul_right hA₀mn.pow_right
  have hBformula :
      B₀ = 2 * (m * n) ^ 2 + A₀ * (2 * A₀) := by
    have hid := positiveCoverB_eq_A_sq_add m n
    rw [hA, hB] at hid
    nlinarith [hid]
  rw [hBformula]
  exact hA₀base.add_mul_left_right (2 * A₀)

/-- The positive signed-square cover has only the abscissas
`u=0,±1`. -/
theorem positiveSlope_cover_classification
    {u : ℚ}
    (hsquare :
      IsSquare ((u ^ 2 + 1) * (u ^ 4 + 6 * u ^ 2 + 1))) :
    u = 0 ∨ u ^ 2 = 1 := by
  let m : ℤ := u.num
  let n : ℤ := u.den
  have hn0 : n ≠ 0 := by
    dsimp only [n]
    exact_mod_cast u.den_ne_zero
  have hnpos : 0 < n := by
    dsimp only [n]
    exact_mod_cast u.den_pos
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hu : u = (m : ℚ) / (n : ℚ) := by
    exact u.num_div_den.symm
  have hcop : IsCoprime m n := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa [m, n] using u.reduced
  have hidentity :
      (((positiveCoverA m n * positiveCoverB m n : ℤ) : ℚ)) =
        ((u ^ 2 + 1) * (u ^ 4 + 6 * u ^ 2 + 1)) *
          (n : ℚ) ^ 6 := by
    rw [hu]
    simp [positiveCoverA, positiveCoverB]
    field_simp [hnq]
  have hdenSquare : IsSquare ((n : ℚ) ^ 6) := by
    exact ⟨(n : ℚ) ^ 3, by ring⟩
  have hproductRat :
      IsSquare (((positiveCoverA m n * positiveCoverB m n : ℤ) : ℚ)) := by
    rw [hidentity]
    exact hsquare.mul hdenSquare
  have hproductInt :
      IsSquare (positiveCoverA m n * positiveCoverB m n) :=
    Rat.isSquare_intCast_iff.mp hproductRat
  obtain ⟨K, hK⟩ := hproductInt
  have hApos : 0 < positiveCoverA m n := by
    simp only [positiveCoverA]
    nlinarith [sq_nonneg m, sq_pos_of_ne_zero hn0]
  have hBpos : 0 < positiveCoverB m n := by
    rw [positiveCoverB_eq_A_sq_add]
    nlinarith [sq_nonneg (m * n)]
  rcases Int.even_or_odd m with hmEven | hmOdd
  · rcases Int.even_or_odd n with hnEven | hnOdd
    · exfalso
      have htwo : IsCoprime (2 : ℤ) (2 : ℤ) :=
        hcop.mono
          (by
            rcases even_iff_exists_two_mul.mp hmEven with ⟨a, ha⟩
            exact ⟨a, by simpa [ha, mul_comm]⟩)
          (by
            rcases even_iff_exists_two_mul.mp hnEven with ⟨b, hb⟩
            exact ⟨b, by simpa [hb, mul_comm]⟩)
      exact (by norm_num : ¬IsCoprime (2 : ℤ) 2) htwo
    · have hAodd : Odd (positiveCoverA m n) := by
        simpa [positiveCoverA, pow_two] using
          (hmEven.mul_right m).add_odd (hnOdd.mul hnOdd)
      have hABcop :
          IsCoprime (positiveCoverA m n) (positiveCoverB m n) :=
        positiveCover_coprime_of_A_odd hcop hAodd
      obtain ⟨Y, hY⟩ :=
        Int.sq_of_isCoprime hABcop.symm (by
          rw [mul_comm]
          simpa [pow_two] using hK)
      have hBsquare : positiveCoverB m n = Y ^ 2 := by
        rcases hY with hY | hY
        · exact hY
        · exfalso
          rw [hY] at hBpos
          exact (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg Y))) hBpos
      have hfourth :
          (m + n) ^ 4 + (m - n) ^ 4 = 2 * Y ^ 2 := by
        rw [positiveCover_fourth_identity, hBsquare]
      have hsquares :=
        fourth_add_fourth_eq_two_square hfourth
      have hmnzero : m * n = 0 := by
        nlinarith [hsquares]
      have hmzero : m = 0 :=
        (mul_eq_zero.mp hmnzero).resolve_right hn0
      exact Or.inl (by
        rw [hu, hmzero]
        simp)
  · rcases Int.even_or_odd n with hnEven | hnOdd
    · have hAodd : Odd (positiveCoverA m n) := by
        simpa [positiveCoverA, pow_two] using
          (hmOdd.mul hmOdd).add_even (hnEven.mul_right n)
      have hABcop :
          IsCoprime (positiveCoverA m n) (positiveCoverB m n) :=
        positiveCover_coprime_of_A_odd hcop hAodd
      obtain ⟨Y, hY⟩ :=
        Int.sq_of_isCoprime hABcop.symm (by
          rw [mul_comm]
          simpa [pow_two] using hK)
      have hBsquare : positiveCoverB m n = Y ^ 2 := by
        rcases hY with hY | hY
        · exact hY
        · exfalso
          rw [hY] at hBpos
          exact (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg Y))) hBpos
      have hfourth :
          (m + n) ^ 4 + (m - n) ^ 4 = 2 * Y ^ 2 := by
        rw [positiveCover_fourth_identity, hBsquare]
      have hsquares :=
        fourth_add_fourth_eq_two_square hfourth
      have hmnzero : m * n = 0 := by
        nlinarith [hsquares]
      have hmzero : m = 0 :=
        (mul_eq_zero.mp hmnzero).resolve_right hn0
      exact Or.inl (by
        rw [hu, hmzero]
        simp)
    · have hAeven : Even (positiveCoverA m n) := by
        simpa [positiveCoverA, pow_two] using
          (hmOdd.mul hmOdd).add_odd (hnOdd.mul hnOdd)
      have hBeven : Even (positiveCoverB m n) := by
        have hends : Even (m ^ 4 + n ^ 4) :=
          hmOdd.pow.add_odd hnOdd.pow
        have hmiddle : Even (6 * m ^ 2 * n ^ 2) := by
          refine ⟨3 * m ^ 2 * n ^ 2, ?_⟩
          ring
        simpa only [positiveCoverB, show
            m ^ 4 + 6 * m ^ 2 * n ^ 2 + n ^ 4 =
              (m ^ 4 + n ^ 4) + 6 * m ^ 2 * n ^ 2 by ring] using
          hends.add hmiddle
      obtain ⟨A₀, hA₀⟩ := even_iff_exists_two_mul.mp hAeven
      obtain ⟨B₀, hB₀⟩ := even_iff_exists_two_mul.mp hBeven
      have hhalves : IsCoprime A₀ B₀ :=
        positiveCover_halves_coprime hcop hmOdd hnOdd hA₀ hB₀
      have hKfour :
          4 * (A₀ * B₀) = K ^ 2 := by
        rw [hA₀, hB₀] at hK
        nlinarith [hK]
      have hKeven : 2 ∣ K := by
        apply @Int.Prime.dvd_pow' _ 2 _ Nat.prime_two
        rw [← hKfour]
        exact ⟨2 * (A₀ * B₀), by ring⟩
      obtain ⟨K₀, hK₀⟩ := hKeven
      have hhalfProduct : A₀ * B₀ = K₀ ^ 2 := by
        rw [hK₀] at hKfour
        nlinarith [hKfour]
      have hB₀pos : 0 < B₀ := by
        rw [hB₀] at hBpos
        nlinarith
      obtain ⟨Y, hY⟩ :=
        Int.sq_of_isCoprime hhalves.symm (by
          rw [mul_comm]
          exact hhalfProduct)
      have hB₀square : B₀ = Y ^ 2 := by
        rcases hY with hY | hY
        · exact hY
        · exfalso
          rw [hY] at hB₀pos
          exact (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg Y))) hB₀pos
      have hBsquare : positiveCoverB m n = 2 * Y ^ 2 := by
        rw [hB₀, hB₀square]
      have hfourth :
          (m + n) ^ 4 + (m - n) ^ 4 = (2 * Y) ^ 2 := by
        rw [positiveCover_fourth_identity, hBsquare]
        ring
      by_cases hplus : m + n = 0
      · exact Or.inr (by
          have hm : m = -n := by linarith
          rw [hu, hm]
          push_cast
          field_simp [hnq])
      by_cases hminus : m - n = 0
      · exact Or.inr (by
          have hm : m = n := sub_eq_zero.mp hminus
          rw [hu, hm]
          field_simp [hnq])
      exact False.elim (not_fermat_42 hplus hminus hfourth)

/-- The common quadratic factor in the denominator-cleared negative cover. -/
def negativeCoverDelta {R : Type*} [CommRing R] (m n : R) : R :=
  m ^ 2 - n ^ 2

/-- The quartic factor in the denominator-cleared negative cover. -/
def negativeCoverD {R : Type*} [CommRing R] (m n : R) : R :=
  m ^ 4 - 6 * m ^ 2 * n ^ 2 + n ^ 4

/-- The octic factor obtained from the original genus-two curve at
`t = -u²`. -/
def negativeCurveG {R : Type*} [CommRing R] (m n : R) : R :=
  m ^ 8 - 20 * m ^ 6 * n ^ 2 + 6 * m ^ 4 * n ^ 4 -
    4 * m ^ 2 * n ^ 6 + n ^ 8

/-- The two square equations modulo three force the common quadratic
factor to vanish. -/
theorem negativeCovers_mod_three_delta
    (m n K L : ZMod 3)
    (hprimitive : ¬(m = 0 ∧ n = 0))
    (hK :
      negativeCoverDelta m n * negativeCoverD m n = K ^ 2)
    (hL :
      negativeCoverDelta m n * (-negativeCurveG m n) = L ^ 2) :
    negativeCoverDelta m n = 0 := by
  revert m n K L
  decide

/-- After removing the exact common power of three, the two square
equations have incompatible nonzero residues modulo three. -/
theorem negativeCovers_mod_three_unit_impossible
    (m n e K L : ZMod 3)
    (hm : m ≠ 0) (hn : n ≠ 0) (he : e ≠ 0)
    (hK : e * negativeCoverD m n = K ^ 2)
    (hL : e * (-negativeCurveG m n) = L ^ 2) :
    False := by
  revert m n e K L
  decide

/-- If both reduced coordinates are nonzero modulo three, the two
remaining homogeneous factors are units modulo three. -/
theorem negativeCover_factors_mod_three_ne_zero
    (m n : ZMod 3) (hm : m ≠ 0) (hn : n ≠ 0) :
    negativeCoverD m n ≠ 0 ∧ negativeCurveG m n ≠ 0 := by
  revert m n
  decide

/-- The direct negative cover and the original genus-two curve cannot
simultaneously be squares, except at `u²=1`. -/
theorem negativeSlope_cover_pair_classification
    {u : ℚ}
    (hdirect :
      IsSquare ((u ^ 2 - 1) * (u ^ 4 - 6 * u ^ 2 + 1)))
    (hcurve :
      IsSquare
        ((1 - u ^ 2) *
          (u ^ 8 - 20 * u ^ 6 + 6 * u ^ 4 -
            4 * u ^ 2 + 1))) :
    u ^ 2 = 1 := by
  let m : ℤ := u.num
  let n : ℤ := u.den
  let δ : ℤ := negativeCoverDelta m n
  let D : ℤ := negativeCoverD m n
  let G : ℤ := negativeCurveG m n
  have hn0 : n ≠ 0 := by
    dsimp only [n]
    exact_mod_cast u.den_ne_zero
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hu : u = (m : ℚ) / (n : ℚ) := u.num_div_den.symm
  have hcop : IsCoprime m n := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa [m, n] using u.reduced
  have hdirectIdentity :
      ((δ * D : ℤ) : ℚ) =
        ((u ^ 2 - 1) * (u ^ 4 - 6 * u ^ 2 + 1)) *
          (n : ℚ) ^ 6 := by
    rw [hu]
    simp [δ, D, negativeCoverDelta, negativeCoverD]
    field_simp [hnq]
  have hcurveIdentity :
      ((δ * (-G) : ℤ) : ℚ) =
        ((1 - u ^ 2) *
          (u ^ 8 - 20 * u ^ 6 + 6 * u ^ 4 -
            4 * u ^ 2 + 1)) * (n : ℚ) ^ 10 := by
    rw [hu]
    simp [δ, G, negativeCoverDelta, negativeCurveG]
    field_simp [hnq]
    ring
  have hdirectInt : IsSquare (δ * D) := by
    apply Rat.isSquare_intCast_iff.mp
    rw [hdirectIdentity]
    exact hdirect.mul ⟨(n : ℚ) ^ 3, by ring⟩
  have hcurveInt : IsSquare (δ * (-G)) := by
    apply Rat.isSquare_intCast_iff.mp
    rw [hcurveIdentity]
    exact hcurve.mul ⟨(n : ℚ) ^ 5, by ring⟩
  obtain ⟨K, hK⟩ := hdirectInt
  obtain ⟨L, hL⟩ := hcurveInt
  by_cases hδ0 : δ = 0
  · have hmnsq : m ^ 2 = n ^ 2 := by
      apply sub_eq_zero.mp
      simpa [δ, negativeCoverDelta] using hδ0
    rw [hu]
    field_simp [hnq]
    exact_mod_cast hmnsq
  have hprimitive :
      ¬(((m : ZMod 3) = 0) ∧ ((n : ZMod 3) = 0)) := by
    rintro ⟨hm3, hn3⟩
    have hmdiv : (3 : ℤ) ∣ m :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd m 3).mp hm3
    have hndiv : (3 : ℤ) ∣ n :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd n 3).mp hn3
    have h33 : IsCoprime (3 : ℤ) (3 : ℤ) :=
      hcop.mono hmdiv hndiv
    norm_num at h33
  have hK3 :
      negativeCoverDelta (m : ZMod 3) n *
          negativeCoverD (m : ZMod 3) n = (K : ZMod 3) ^ 2 := by
    simpa [δ, D, negativeCoverDelta, negativeCoverD, pow_two] using
      congrArg (fun z : ℤ => (z : ZMod 3)) hK
  have hL3 :
      negativeCoverDelta (m : ZMod 3) n *
          (-negativeCurveG (m : ZMod 3) n) = (L : ZMod 3) ^ 2 := by
    simpa [δ, G, negativeCoverDelta, negativeCurveG, pow_two] using
      congrArg (fun z : ℤ => (z : ZMod 3)) hL
  have hδ3 :
      negativeCoverDelta (m : ZMod 3) n = 0 :=
    negativeCovers_mod_three_delta
      (m : ZMod 3) n K L hprimitive hK3 hL3
  have h3δ : (3 : ℤ) ∣ δ := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd δ 3).mp
    simpa [δ, negativeCoverDelta] using hδ3
  have hm3 : (m : ZMod 3) ≠ 0 := by
    intro hmzero
    have hmdiv : (3 : ℤ) ∣ m :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd m 3).mp hmzero
    have hm2div : (3 : ℤ) ∣ m ^ 2 := by
      simpa only [pow_two] using dvd_mul_of_dvd_left hmdiv m
    have hn2div : (3 : ℤ) ∣ n ^ 2 := by
      have := dvd_sub hm2div h3δ
      simpa [δ, negativeCoverDelta] using this
    have hndiv : (3 : ℤ) ∣ n :=
      Int.Prime.dvd_pow' Nat.prime_three hn2div
    exact (by
      have h33 : IsCoprime (3 : ℤ) (3 : ℤ) :=
        hcop.mono hmdiv hndiv
      norm_num at h33)
  have hn3 : (n : ZMod 3) ≠ 0 := by
    intro hnzero
    have hndiv : (3 : ℤ) ∣ n :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd n 3).mp hnzero
    have hn2div : (3 : ℤ) ∣ n ^ 2 := by
      simpa only [pow_two] using dvd_mul_of_dvd_left hndiv n
    have hm2div : (3 : ℤ) ∣ m ^ 2 := by
      have := dvd_add h3δ hn2div
      simpa [δ, negativeCoverDelta] using this
    have hmdiv : (3 : ℤ) ∣ m :=
      Int.Prime.dvd_pow' Nat.prime_three hm2div
    exact (by
      have h33 : IsCoprime (3 : ℤ) (3 : ℤ) :=
        hcop.mono hmdiv hndiv
      norm_num at h33)
  have hfactor3 :=
    negativeCover_factors_mod_three_ne_zero
      (m : ZMod 3) n hm3 hn3
  have h3D : ¬(3 : ℤ) ∣ D := by
    intro hdiv
    apply hfactor3.1
    have hcast :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd D 3).mpr hdiv
    simpa [D, negativeCoverD] using hcast
  have h3G : ¬(3 : ℤ) ∣ G := by
    intro hdiv
    apply hfactor3.2
    have hcast :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd G 3).mpr hdiv
    simpa [G, negativeCurveG] using hcast
  have hD0 : D ≠ 0 := fun hzero => h3D (hzero ▸ dvd_zero 3)
  have hG0 : G ≠ 0 := fun hzero => h3G (hzero ▸ dvd_zero 3)
  have hnegG0 : -G ≠ 0 := neg_ne_zero.mpr hG0
  have h3negG : ¬(3 : ℤ) ∣ -G := by
    simpa only [dvd_neg] using h3G
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDval : padicValInt 3 D = 0 :=
    padicValInt.eq_zero_of_not_dvd h3D
  have hnegGval : padicValInt 3 (-G) = 0 :=
    padicValInt.eq_zero_of_not_dvd h3negG
  have hK0 : K ≠ 0 := by
    intro hzero
    have : δ * D = 0 := by simpa [hzero] using hK
    exact (mul_ne_zero hδ0 hD0) this
  have hL0 : L ≠ 0 := by
    intro hzero
    have : δ * (-G) = 0 := by simpa [hzero] using hL
    exact (mul_ne_zero hδ0 hnegG0) this
  let k : ℕ := padicValInt 3 δ
  let j : ℕ := padicValInt 3 K
  have hkj : k = 2 * j := by
    have hval := congrArg (padicValInt 3) hK
    rw [padicValInt.mul hδ0 hD0,
      padicValInt.mul hK0 hK0, hDval] at hval
    dsimp only [k, j]
    omega
  have hLval : padicValInt 3 L = j := by
    have hval := congrArg (padicValInt 3) hL
    rw [padicValInt.mul hδ0 hnegG0,
      padicValInt.mul hL0 hL0, hnegGval] at hval
    dsimp only [k, j] at hkj
    omega
  obtain ⟨e, he⟩ := padicValInt_dvd (p := 3) δ
  change δ = (3 : ℤ) ^ k * e at he
  obtain ⟨K₀, hK₀⟩ := padicValInt_dvd (p := 3) K
  change K = (3 : ℤ) ^ j * K₀ at hK₀
  have hLj : (3 : ℤ) ^ j ∣ L := by
    apply pow_dvd_of_le_padicValInt Nat.prime_three
    omega
  obtain ⟨L₀, hL₀⟩ := hLj
  have he0 : e ≠ 0 := by
    intro hezero
    apply hδ0
    rw [he, hezero]
    simp
  have h3e : ¬(3 : ℤ) ∣ e := by
    intro hediv
    rcases hediv with ⟨e₁, he₁⟩
    have htooMuch : (3 : ℤ) ^ (k + 1) ∣ δ := by
      refine ⟨e₁, ?_⟩
      rw [he, he₁, pow_succ]
      ring
    exact
      (not_pow_dvd_of_padicValInt_lt Nat.prime_three hδ0
        (by dsimp only [k]; omega)) htooMuch
  have hKunit : e * D = K₀ ^ 2 := by
    have hscaled :
        (3 : ℤ) ^ (2 * j) * (e * D) =
          (3 : ℤ) ^ (2 * j) * K₀ ^ 2 := by
      calc
        (3 : ℤ) ^ (2 * j) * (e * D) =
            ((3 : ℤ) ^ k * e) * D := by
              rw [hkj]
              ring
        _ = δ * D := by rw [← he]
        _ = K * K := hK
        _ = ((3 : ℤ) ^ j * K₀) *
            ((3 : ℤ) ^ j * K₀) := by rw [hK₀]
        _ = (3 : ℤ) ^ (2 * j) * K₀ ^ 2 := by
              rw [two_mul, pow_add]
              ring
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (3 : ℤ) ≠ 0))
      hscaled
  have hLunit : e * (-G) = L₀ ^ 2 := by
    have hscaled :
        (3 : ℤ) ^ (2 * j) * (e * (-G)) =
          (3 : ℤ) ^ (2 * j) * L₀ ^ 2 := by
      calc
        (3 : ℤ) ^ (2 * j) * (e * (-G)) =
            ((3 : ℤ) ^ k * e) * (-G) := by
              rw [hkj]
              ring
        _ = δ * (-G) := by rw [← he]
        _ = L * L := hL
        _ = ((3 : ℤ) ^ j * L₀) *
            ((3 : ℤ) ^ j * L₀) := by rw [hL₀]
        _ = (3 : ℤ) ^ (2 * j) * L₀ ^ 2 := by
              rw [two_mul, pow_add]
              ring
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (3 : ℤ) ≠ 0))
      hscaled
  have he3 : (e : ZMod 3) ≠ 0 := by
    intro hzero
    exact h3e ((ZMod.intCast_zmod_eq_zero_iff_dvd e 3).mp hzero)
  exfalso
  apply
    negativeCovers_mod_three_unit_impossible
      (m : ZMod 3) n e K₀ L₀ hm3 hn3 he3
  · simpa [D, negativeCoverD, pow_two] using
      congrArg (fun z : ℤ => (z : ZMod 3)) hKunit
  · simpa [G, negativeCurveG, pow_two] using
      congrArg (fun z : ℤ => (z : ZMod 3)) hLunit

end

end Cuboid2
