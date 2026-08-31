import Cuboid2.LinearQuartic.DirectSquareReduction
import Cuboid2.QuadraticReduction.C012

/-!
# Specialized completion of the linear--quartic branch

The public theorem only needs the parameter

`s = sharipovParameter p q = (p / q)²`.

For this parameter a rational root of the normalized quintic has signed-square
class.  The proof below is the degree-one Newton-polygon calculation for the
integral homogeneous quintic.  It is deliberately separate from the
degree-two calculation in `QuadraticReduction.C012`.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- Scaling a rational root by `q⁴` produces an integral root of the
homogeneous quintic. -/
theorem exists_integral_scaled_linear_root
    {p q : ℕ} (hq : 0 < q) {r : ℚ}
    (hr : IsRoot (normalizedQuintic (sharipovParameter p q)) r) :
    ∃ B : ℤ,
      (B : ℚ) = (q : ℚ) ^ 4 * r ∧
      IsRoot (homogeneousQuintic p q) B := by
  let x : ℚ := (q : ℚ) ^ 4 * r
  have hxroot :
      IsRoot ((homogeneousQuintic p q).map (algebraMap ℤ ℚ)) x := by
    rw [map_homogeneousQuintic,
      ← normalizedQuintic_scaleRoots_eq_homogeneous hq]
    rw [IsRoot]
    exact scaleRoots_eval₂_eq_zero (RingHom.id ℚ) (IsRoot.def.mp hr)
  have hdiv :
      X - C x ∣ (homogeneousQuintic p q).map (algebraMap ℤ ℚ) :=
    dvd_iff_isRoot.mpr hxroot
  have hxIntegral : IsIntegral ℤ x := by
    have hnegIntegral : IsIntegral ℤ (-x) := by
      simpa using
        (Polynomial.isIntegral_coeff_of_dvd
          (homogeneousQuintic p q) (X - C x)
          (homogeneousQuintic_monic p q) (monic_X_sub_C x) hdiv 0)
    simpa using hnegIntegral.neg
  obtain ⟨B, hB⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxIntegral
  refine ⟨B, hB, ?_⟩
  apply IsRoot.of_map (f := algebraMap ℤ ℚ)
  · rw [hB]
    exact hxroot
  · exact Int.cast_injective

/-- An integral root divides the constant coefficient of the homogeneous
quintic. -/
theorem integral_linear_root_dvd_parameter_power
    {p q : ℕ} {B : ℤ} (hB : IsRoot (homogeneousQuintic p q) B) :
    B ∣ (p : ℤ) ^ 10 * (q : ℤ) ^ 10 := by
  obtain ⟨G, hG⟩ :=
    (dvd_iff_isRoot.mpr hB :
      X - C B ∣ homogeneousQuintic p q)
  have hcoeff := congrArg (fun P : ℤ[X] => P.coeff 0) hG
  rw [mul_coeff_zero] at hcoeff
  have hproduct :
      -((p : ℤ) ^ 10 * (q : ℤ) ^ 10) = (-B) * G.coeff 0 := by
    rw [homogeneousQuintic_coeff_zero] at hcoeff
    simpa using hcoeff
  exact ⟨G.coeff 0, by
    calc
      (p : ℤ) ^ 10 * (q : ℤ) ^ 10 =
          -(-((p : ℤ) ^ 10 * (q : ℤ) ^ 10)) := by ring
      _ = -((-B) * G.coeff 0) := by rw [hproduct]
      _ = B * G.coeff 0 := by ring⟩

/-- Valuation of a nonzero integral power. -/
theorem padicValInt_pow
    {r n : ℕ} (hrPrime : r.Prime) {z : ℤ} (_hz : z ≠ 0) :
    padicValInt r (z ^ n) = n * padicValInt r z := by
  letI : Fact r.Prime := ⟨hrPrime⟩
  simp only [padicValInt, Int.natAbs_pow]
  exact padicValNat.pow z.natAbs n

/-- A valuation lower bound gives divisibility of a nonzero integer. -/
theorem pow_dvd_of_le_padicValInt
    {r n : ℕ} (hrPrime : r.Prime) {z : ℤ}
    (h : n ≤ padicValInt r z) :
    (r : ℤ) ^ n ∣ z := by
  letI : Fact r.Prime := ⟨hrPrime⟩
  exact (padicValInt_dvd_iff n z).2 (Or.inr h)

/-- Strictly exceeding the exact valuation rules out divisibility. -/
theorem not_pow_dvd_of_padicValInt_lt
    {r n : ℕ} (hrPrime : r.Prime) {z : ℤ}
    (hz : z ≠ 0) (h : padicValInt r z < n) :
    ¬(r : ℤ) ^ n ∣ z := by
  letI : Fact r.Prime := ⟨hrPrime⟩
  intro hdvd
  rcases (padicValInt_dvd_iff n z).1 hdvd with hzero | hle
  · exact hz hzero
  · omega

/-- If one summand has uniquely smallest valuation, a zero sum is
impossible. -/
theorem four_term_unique_low_impossible
    {r n : ℕ} {a b c d : ℤ}
    (ha : ¬(r : ℤ) ^ n ∣ a)
    (hb : (r : ℤ) ^ n ∣ b)
    (hc : (r : ℤ) ^ n ∣ c)
    (hd : (r : ℤ) ^ n ∣ d)
    (hsum : a + b + c + d = 0) :
    False := by
  have hrest : (r : ℤ) ^ n ∣ b + c + d :=
    dvd_add (dvd_add hb hc) hd
  have htotal : (r : ℤ) ^ n ∣ a + b + c + d := hsum ▸ dvd_zero _
  exact ha (by
    have := dvd_sub htotal hrest
    simpa only [show a + b + c + d - (b + c + d) = a by ring] using this)

/-- The degree-one Newton polygon has only the slopes `0`, `-2k`, and
`-4k`; hence every integral root has even valuation. -/
theorem integral_linear_root_factorization_even
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hcop : p.Coprime q)
    {B : ℤ} (hB0 : B ≠ 0) (hroot : IsRoot (homogeneousQuintic p q) B)
    (r : ℕ) (hrPrime : r.Prime) (hr : r ∣ p * q) :
    Even (B.natAbs.factorization r) := by
  letI : Fact r.Prime := ⟨hrPrime⟩
  let k := padicValNat r (p * q)
  let beta := padicValInt r B
  have hpq0 : p * q ≠ 0 :=
    Nat.mul_ne_zero (Nat.ne_of_gt hp) (Nat.ne_of_gt hq)
  have hk : 0 < k := one_le_padicValNat_of_dvd hpq0 hr
  have hbetaFactor :
      B.natAbs.factorization r = beta := by
    rw [B.natAbs.factorization_def hrPrime]
    rfl
  suffices beta = 0 ∨ beta = 2 * k ∨ beta = 4 * k by
    rw [hbetaFactor]
    rcases this with h | h | h
    · rw [h]
      exact ⟨0, by omega⟩
    · rw [h]
      exact ⟨k, by omega⟩
    · rw [h]
      exact ⟨2 * k, by omega⟩
  have hc3unit :
      padicValInt r ((homogeneousQuintic p q).coeff 3) = 0 :=
    homogeneousQuintic_coeff_three_padicValInt hcop hrPrime hr
  have hc3zero :
      (homogeneousQuintic p q).coeff 3 ≠ 0 := by
    intro hz
    exact (homogeneousQuintic_coeff_three_not_dvd hcop hrPrime hr)
      (hz ▸ dvd_zero _)
  have hc2val :
      padicValInt r ((homogeneousQuintic p q).coeff 2) = 2 * k := by
    simpa only [k] using
      homogeneousQuintic_coeff_two_padicValInt
        hp hq hcop hrPrime hr
  have hc2zero :
      (homogeneousQuintic p q).coeff 2 ≠ 0 :=
    homogeneousQuintic_coeff_two_ne_zero hp hq hcop hrPrime hr
  have hc1div :
      (r : ℤ) ^ (6 * k) ∣ (homogeneousQuintic p q).coeff 1 := by
    simpa only [k] using
      homogeneousQuintic_coeff_one_pow_dvd hp hq hrPrime
  have hc0val :
      padicValInt r ((homogeneousQuintic p q).coeff 0) = 10 * k := by
    rw [homogeneousQuintic_coeff_zero]
    exact padicValInt_neg_parameter_powers hrPrime hp hq
  have hc0zero :
      (homogeneousQuintic p q).coeff 0 ≠ 0 := by
    rw [homogeneousQuintic_coeff_zero]
    exact neg_ne_zero.mpr
      (mul_ne_zero
        (pow_ne_zero 10 (by exact_mod_cast (Nat.ne_of_gt hp)))
        (pow_ne_zero 10 (by exact_mod_cast (Nat.ne_of_gt hq))))
  have hrootExpanded :
      B ^ 5 +
          (homogeneousQuintic p q).coeff 4 * B ^ 4 +
          (homogeneousQuintic p q).coeff 3 * B ^ 3 +
          (homogeneousQuintic p q).coeff 2 * B ^ 2 +
          (homogeneousQuintic p q).coeff 1 * B +
          (homogeneousQuintic p q).coeff 0 = 0 := by
    have heval := IsRoot.def.mp hroot
    have hnatDegree : (homogeneousQuintic p q).natDegree = 5 :=
      natDegree_eq_of_degree_eq_some (homogeneousQuintic_degree p q)
    have hcoeffFive : (homogeneousQuintic p q).coeff 5 = 1 := by
      rw [← hnatDegree]
      exact (homogeneousQuintic_monic p q).coeff_natDegree
    rw [eval_eq_sum_range' (n := 6) (by omega)] at heval
    norm_num [Finset.sum_range_succ, hcoeffFive] at heval
    linarith
  by_cases hbeta0 : beta = 0
  · exact Or.inl hbeta0
  have hbetaPos : 0 < beta := Nat.pos_of_ne_zero hbeta0
  have hrB : (r : ℤ) ∣ B := by
    have : 1 ≤ beta := hbetaPos
    simpa only [pow_one] using
      pow_dvd_of_le_padicValInt hrPrime (z := B) this
  have hpowVal (n : ℕ) :
      padicValInt r (B ^ n) = n * beta := by
    simpa only [beta] using padicValInt_pow hrPrime hB0
  have hLzero :
      B ^ 2 +
          (homogeneousQuintic p q).coeff 4 * B +
          (homogeneousQuintic p q).coeff 3 ≠ 0 := by
    intro hz
    have hdiv :
        (r : ℤ) ∣
          B ^ 2 +
            (homogeneousQuintic p q).coeff 4 * B +
            (homogeneousQuintic p q).coeff 3 := hz ▸ dvd_zero _
    have hfirst : (r : ℤ) ∣ B ^ 2 := by
      simpa only [pow_two] using dvd_mul_of_dvd_left hrB B
    have hsecond :
        (r : ℤ) ∣ (homogeneousQuintic p q).coeff 4 * B :=
      dvd_mul_of_dvd_right hrB _
    have hc3div : (r : ℤ) ∣ (homogeneousQuintic p q).coeff 3 := by
      have := dvd_sub (dvd_sub hdiv hfirst) hsecond
      simpa only [show
          B ^ 2 + (homogeneousQuintic p q).coeff 4 * B +
                (homogeneousQuintic p q).coeff 3 -
              B ^ 2 -
              (homogeneousQuintic p q).coeff 4 * B =
            (homogeneousQuintic p q).coeff 3 by ring] using this
    exact (homogeneousQuintic_coeff_three_not_dvd hcop hrPrime hr) hc3div
  have hLunit :
      padicValInt r
          (B ^ 2 +
            (homogeneousQuintic p q).coeff 4 * B +
            (homogeneousQuintic p q).coeff 3) = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro hdiv
    have hfirst : (r : ℤ) ∣ B ^ 2 := by
      simpa only [pow_two] using dvd_mul_of_dvd_left hrB B
    have hsecond :
        (r : ℤ) ∣ (homogeneousQuintic p q).coeff 4 * B :=
      dvd_mul_of_dvd_right hrB _
    have hc3div : (r : ℤ) ∣ (homogeneousQuintic p q).coeff 3 := by
      have := dvd_sub (dvd_sub hdiv hfirst) hsecond
      simpa only [show
          B ^ 2 + (homogeneousQuintic p q).coeff 4 * B +
                (homogeneousQuintic p q).coeff 3 -
              B ^ 2 -
              (homogeneousQuintic p q).coeff 4 * B =
            (homogeneousQuintic p q).coeff 3 by ring] using this
    exact (homogeneousQuintic_coeff_three_not_dvd hcop hrPrime hr) hc3div
  let L : ℤ :=
    B ^ 3 *
      (B ^ 2 +
        (homogeneousQuintic p q).coeff 4 * B +
        (homogeneousQuintic p q).coeff 3)
  let M : ℤ := (homogeneousQuintic p q).coeff 2 * B ^ 2
  let N : ℤ := (homogeneousQuintic p q).coeff 1 * B
  let C : ℤ := (homogeneousQuintic p q).coeff 0
  have hLzero' : L ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hB0) hLzero
  have hMzero : M ≠ 0 :=
    mul_ne_zero hc2zero (pow_ne_zero 2 hB0)
  have hNroot : L + M + N + C = 0 := by
    dsimp only [L, M, N, C]
    calc
      B ^ 3 *
            (B ^ 2 +
              (homogeneousQuintic p q).coeff 4 * B +
              (homogeneousQuintic p q).coeff 3) +
          (homogeneousQuintic p q).coeff 2 * B ^ 2 +
          (homogeneousQuintic p q).coeff 1 * B +
          (homogeneousQuintic p q).coeff 0 =
        B ^ 5 +
          (homogeneousQuintic p q).coeff 4 * B ^ 4 +
          (homogeneousQuintic p q).coeff 3 * B ^ 3 +
          (homogeneousQuintic p q).coeff 2 * B ^ 2 +
          (homogeneousQuintic p q).coeff 1 * B +
          (homogeneousQuintic p q).coeff 0 := by ring
      _ = 0 := hrootExpanded
  have hLval : padicValInt r L = 3 * beta := by
    dsimp only [L]
    rw [padicValInt.mul (pow_ne_zero 3 hB0) hLzero, hpowVal, hLunit]
    omega
  have hMval : padicValInt r M = 2 * k + 2 * beta := by
    dsimp only [M]
    rw [padicValInt.mul hc2zero (pow_ne_zero 2 hB0), hc2val, hpowVal]
  have hNdiv : (r : ℤ) ^ (6 * k + beta) ∣ N := by
    dsimp only [N]
    have hBdiv : (r : ℤ) ^ beta ∣ B := padicValInt_dvd B
    simpa only [pow_add] using mul_dvd_mul hc1div hBdiv
  have hCval : padicValInt r C = 10 * k := by
    exact hc0val
  by_cases hbeta2 : beta = 2 * k
  · exact Or.inr (Or.inl hbeta2)
  by_cases hbeta4 : beta = 4 * k
  · exact Or.inr (Or.inr hbeta4)
  by_cases hlt2 : beta < 2 * k
  · have hnotL :
        ¬(r : ℤ) ^ (3 * beta + 1) ∣ L :=
      not_pow_dvd_of_padicValInt_lt hrPrime hLzero'
        (by rw [hLval]; omega)
    have hMdiv : (r : ℤ) ^ (3 * beta + 1) ∣ M :=
      pow_dvd_of_le_padicValInt hrPrime
        (by rw [hMval]; omega)
    have hNdiv' : (r : ℤ) ^ (3 * beta + 1) ∣ N :=
      dvd_trans (pow_dvd_pow (r : ℤ) (by omega)) hNdiv
    have hCdiv : (r : ℤ) ^ (3 * beta + 1) ∣ C :=
      pow_dvd_of_le_padicValInt hrPrime
        (by rw [hCval]; omega)
    exact False.elim
      (four_term_unique_low_impossible hnotL hMdiv hNdiv' hCdiv hNroot)
  have hgt2 : 2 * k < beta := by omega
  by_cases hlt4 : beta < 4 * k
  · have hnotM :
        ¬(r : ℤ) ^ (2 * k + 2 * beta + 1) ∣ M :=
      not_pow_dvd_of_padicValInt_lt hrPrime hMzero
        (by rw [hMval]; omega)
    have hLdiv :
        (r : ℤ) ^ (2 * k + 2 * beta + 1) ∣ L :=
      pow_dvd_of_le_padicValInt hrPrime
        (by rw [hLval]; omega)
    have hNdiv' :
        (r : ℤ) ^ (2 * k + 2 * beta + 1) ∣ N :=
      dvd_trans (pow_dvd_pow (r : ℤ) (by omega)) hNdiv
    have hCdiv :
        (r : ℤ) ^ (2 * k + 2 * beta + 1) ∣ C :=
      pow_dvd_of_le_padicValInt hrPrime
        (by rw [hCval]; omega)
    exact False.elim
      (four_term_unique_low_impossible hnotM hLdiv hNdiv' hCdiv
        (by linarith [hNroot]))
  have hgt4 : 4 * k < beta := by omega
  have hnotC :
      ¬(r : ℤ) ^ (10 * k + 1) ∣ C :=
    not_pow_dvd_of_padicValInt_lt hrPrime hc0zero
      (by rw [hCval]; omega)
  have hLdiv : (r : ℤ) ^ (10 * k + 1) ∣ L :=
    pow_dvd_of_le_padicValInt hrPrime
      (by rw [hLval]; omega)
  have hMdiv : (r : ℤ) ^ (10 * k + 1) ∣ M :=
    pow_dvd_of_le_padicValInt hrPrime
      (by rw [hMval]; omega)
  have hNdiv' : (r : ℤ) ^ (10 * k + 1) ∣ N :=
    dvd_trans (pow_dvd_pow (r : ℤ) (by omega)) hNdiv
  exact False.elim
    (four_term_unique_low_impossible hnotC hLdiv hMdiv hNdiv'
      (by linarith [hNroot]))

/-- Every rational root at a Sharipov square parameter is a signed rational
square. -/
theorem normalizedQuintic_root_signedSquare_sharipov
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hcop : p.Coprime q)
    {r : ℚ} (hr : IsRoot (normalizedQuintic (sharipovParameter p q)) r) :
    ∃ ε : PhysicalSign, ∃ u : ℚ, r = ε.value * u ^ 2 := by
  obtain ⟨B, hBscale, hBroot⟩ :=
    exists_integral_scaled_linear_root hq hr
  have hs0 : sharipovParameter p q ≠ 0 :=
    ne_of_gt (sharipovParameter_pos hp hq)
  have hr0 : r ≠ 0 := by
    intro hrzero
    have heval := IsRoot.def.mp hr
    rw [hrzero] at heval
    simp [normalizedQuintic, normalizedQuinticLower] at heval
    exact hs0 heval
  have hq0 : (q : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  have hB0 : B ≠ 0 := by
    intro hzero
    have : (q : ℚ) ^ 4 * r = 0 := by simpa [hzero] using hBscale.symm
    exact hr0 ((mul_eq_zero.mp this).resolve_left (pow_ne_zero 4 hq0))
  have hBdvd :
      B ∣ (p : ℤ) ^ 10 * (q : ℤ) ^ 10 :=
    integral_linear_root_dvd_parameter_power hBroot
  have heven :
      ∀ prime : ℕ, prime.Prime →
        Even (B.natAbs.factorization prime) := by
    intro prime hprime
    by_cases hdiv : prime ∣ p * q
    · exact integral_linear_root_factorization_even
        hp hq hcop hB0 hBroot prime hprime hdiv
    · have hnat :
          B.natAbs ∣ p ^ 10 * q ^ 10 := by
        have habs :
            B.natAbs ∣
              (((p : ℤ) ^ 10 * (q : ℤ) ^ 10).natAbs) :=
          Int.natAbs_dvd_natAbs.mpr hBdvd
        simpa [Int.natAbs_mul, Int.natAbs_pow] using habs
      have hprimeB : ¬prime ∣ B.natAbs := by
        intro hprimeB
        have hpqpow : prime ∣ p ^ 10 * q ^ 10 :=
          dvd_trans hprimeB hnat
        rcases hprime.dvd_mul.mp hpqpow with hp' | hq'
        · exact hdiv
            (dvd_mul_of_dvd_left (hprime.dvd_of_dvd_pow hp') q)
        · exact hdiv
            (dvd_mul_of_dvd_right (hprime.dvd_of_dvd_pow hq') p)
      rw [(Nat.factorization_eq_zero_iff B.natAbs prime).2
        (Or.inr (Or.inl hprimeB))]
      exact ⟨0, by omega⟩
  obtain ⟨ε, d, hBsquare⟩ :=
    int_signedSquare_of_even_natAbs_factorization hB0 heven
  refine ⟨ε, (d : ℚ) / (q : ℚ) ^ 2, ?_⟩
  have hq4 : (q : ℚ) ^ 4 ≠ 0 := pow_ne_zero 4 hq0
  apply (mul_left_cancel₀ hq4)
  calc
    (q : ℚ) ^ 4 * r = (B : ℚ) := hBscale.symm
    _ = ε.value * (d : ℚ) ^ 2 := hBsquare
    _ = (q : ℚ) ^ 4 *
        (ε.value * ((d : ℚ) / (q : ℚ) ^ 2) ^ 2) := by
          field_simp [hq0]

end

end Cuboid2
