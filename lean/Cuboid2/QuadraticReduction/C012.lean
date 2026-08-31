import Cuboid2.QuadraticReduction.Extraction

/-!
# Arithmetic entrance to the signed-square reduction

This file isolates the integral arithmetic needed for claim C012.  In
particular, it checks the exact integral scaling of a rational quadratic
factor and records the single local Newton-polygon statement still needed
to conclude that its constant coefficient is a signed square.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/--
The degree-five polynomial in `X = t²` before normalizing by `q⁴`.
It is kept generic so that its integer and rational incarnations are
definitionally synchronized.
-/
def homogeneousQuinticLowerOver {R : Type*} [CommRing R] (p q : R) : R[X] :=
  C ((2 * q ^ 2 + p ^ 2) * (3 * q ^ 2 - 2 * p ^ 2)) * X ^ 4 +
    (C (q ^ 8 + 10 * p ^ 2 * q ^ 6 + 4 * p ^ 4 * q ^ 4 -
      14 * p ^ 6 * q ^ 2 + p ^ 8) * X ^ 3 +
      (C (-p ^ 2 * q ^ 2 *
        (q ^ 8 - 14 * p ^ 2 * q ^ 6 + 4 * p ^ 4 * q ^ 4 +
          10 * p ^ 6 * q ^ 2 + p ^ 8)) * X ^ 2 +
        (C (-p ^ 6 * q ^ 6 * (q ^ 2 + 2 * p ^ 2) *
          (-2 * q ^ 2 + 3 * p ^ 2)) * X +
          C (-p ^ 10 * q ^ 10))))

/-- The full degree-five homogeneous quintic. -/
def homogeneousQuinticOver {R : Type*} [CommRing R] (p q : R) : R[X] :=
  X ^ 5 + homogeneousQuinticLowerOver p q

/-- The integral homogeneous quintic attached to natural parameters. -/
def homogeneousQuintic (p q : ℕ) : ℤ[X] :=
  homogeneousQuinticOver (p : ℤ) (q : ℤ)

/-- Mapping the integral homogeneous quintic to `ℚ` only maps its parameters. -/
theorem map_homogeneousQuintic (p q : ℕ) :
    (homogeneousQuintic p q).map (algebraMap ℤ ℚ) =
      homogeneousQuinticOver (p : ℚ) (q : ℚ) := by
  simp [homogeneousQuintic, homogeneousQuinticOver, homogeneousQuinticLowerOver]
  simp only [map_ofNat]

/-- Everything below the leading term has degree at most four. -/
theorem homogeneousQuinticLowerOver_degree_le
    {R : Type*} [CommRing R] (p q : R) :
    (homogeneousQuinticLowerOver p q).degree ≤ (4 : WithBot ℕ) := by
  unfold homogeneousQuinticLowerOver
  apply degree_add_le_of_degree_le
  · exact degree_C_mul_X_pow_le 4 _
  · apply degree_add_le_of_degree_le
    · exact (degree_C_mul_X_pow_le 3 _).trans (by norm_num)
    · apply degree_add_le_of_degree_le
      · exact (degree_C_mul_X_pow_le 2 _).trans (by norm_num)
      · apply degree_add_le_of_degree_le
        · simpa only [pow_one] using
            (degree_C_mul_X_pow_le 1
              (-p ^ 6 * q ^ 6 * (q ^ 2 + 2 * p ^ 2) *
                (-2 * q ^ 2 + 3 * p ^ 2))).trans (by norm_num)
        · exact degree_C_le.trans (by norm_num)

/-- The homogeneous quintic is monic. -/
theorem homogeneousQuintic_monic (p q : ℕ) :
    (homogeneousQuintic p q).Monic := by
  unfold homogeneousQuintic homogeneousQuinticOver
  apply monic_X_pow_add
  exact (homogeneousQuinticLowerOver_degree_le (p : ℤ) (q : ℤ)).trans_lt
    (by norm_num)

/-- The homogeneous quintic has degree five. -/
theorem homogeneousQuintic_degree (p q : ℕ) :
    (homogeneousQuintic p q).degree = 5 := by
  unfold homogeneousQuintic homogeneousQuinticOver
  rw [degree_add_eq_left_of_degree_lt
    ((homogeneousQuinticLowerOver_degree_le (p : ℤ) (q : ℤ)).trans_lt
      (by norm_num))]
  simp

/-- The constant coefficient of the homogeneous quintic. -/
theorem homogeneousQuintic_coeff_zero (p q : ℕ) :
    (homogeneousQuintic p q).coeff 0 =
      -((p : ℤ) ^ 10 * (q : ℤ) ^ 10) := by
  simp only [homogeneousQuintic, homogeneousQuinticOver,
    homogeneousQuinticLowerOver, coeff_add, coeff_X_pow,
    coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

/-- The linear coefficient of the homogeneous quintic. -/
theorem homogeneousQuintic_coeff_one (p q : ℕ) :
    (homogeneousQuintic p q).coeff 1 =
      -((p : ℤ) ^ 6 * (q : ℤ) ^ 6 *
        ((q : ℤ) ^ 2 + 2 * (p : ℤ) ^ 2) *
        (-2 * (q : ℤ) ^ 2 + 3 * (p : ℤ) ^ 2)) := by
  simp only [homogeneousQuintic, homogeneousQuinticOver,
    homogeneousQuinticLowerOver, coeff_add, coeff_X_pow,
    coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

/-- The quadratic coefficient of the homogeneous quintic. -/
theorem homogeneousQuintic_coeff_two (p q : ℕ) :
    (homogeneousQuintic p q).coeff 2 =
      -((p : ℤ) ^ 2 * (q : ℤ) ^ 2 *
        ((q : ℤ) ^ 8 - 14 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
          4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 +
          10 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8)) := by
  simp only [homogeneousQuintic, homogeneousQuinticOver,
    homogeneousQuinticLowerOver, coeff_add, coeff_X_pow,
    coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

/-- The cubic coefficient of the homogeneous quintic. -/
theorem homogeneousQuintic_coeff_three (p q : ℕ) :
    (homogeneousQuintic p q).coeff 3 =
      (q : ℤ) ^ 8 + 10 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
        4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 -
        14 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8 := by
  simp only [homogeneousQuintic, homogeneousQuinticOver,
    homogeneousQuinticLowerOver, coeff_add, coeff_X_pow,
    coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

/--
At a prime dividing exactly one of the coprime parameters, the cubic
coefficient is a unit.  This is the upper-right endpoint of the local
Newton polygon.
-/
theorem homogeneousQuintic_coeff_three_not_dvd
    {p q r : ℕ} (hcop : p.Coprime q) (hrPrime : r.Prime)
    (hr : r ∣ p * q) :
    ¬(r : ℤ) ∣ (homogeneousQuintic p q).coeff 3 := by
  rw [homogeneousQuintic_coeff_three]
  intro hdvd
  rcases hrPrime.dvd_mul.mp hr with hrp | hrq
  · have hnq : ¬r ∣ q := by
      intro hrq
      have hrgcd : r ∣ Nat.gcd p q := Nat.dvd_gcd hrp hrq
      rw [hcop.gcd_eq_one] at hrgcd
      exact hrPrime.not_dvd_one hrgcd
    have hdifference : (r : ℤ) ∣
        (10 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
          4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 -
          14 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8) := by
      obtain ⟨m, hm⟩ := Int.ofNat_dvd.mpr hrp
      use 10 * m * (p : ℤ) * (q : ℤ) ^ 6 +
        4 * m * (p : ℤ) ^ 3 * (q : ℤ) ^ 4 -
        14 * m * (p : ℤ) ^ 5 * (q : ℤ) ^ 2 +
        m * (p : ℤ) ^ 7
      rw [hm]
      ring
    have hsub := dvd_sub hdvd hdifference
    have hqpow : (r : ℤ) ∣ (q : ℤ) ^ 8 := by
      simpa only [show
          (q : ℤ) ^ 8 + 10 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
              4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 -
              14 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8 -
            (10 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
              4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 -
              14 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8) =
            (q : ℤ) ^ 8 by ring] using hsub
    have hrq : r ∣ q :=
      hrPrime.dvd_of_dvd_pow (by exact_mod_cast hqpow)
    exact hnq hrq
  · have hnp : ¬r ∣ p := by
      intro hrp
      have hrgcd : r ∣ Nat.gcd p q := Nat.dvd_gcd hrp hrq
      rw [hcop.gcd_eq_one] at hrgcd
      exact hrPrime.not_dvd_one hrgcd
    have hdifference : (r : ℤ) ∣
        ((q : ℤ) ^ 8 + 10 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
          4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 -
          14 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2) := by
      obtain ⟨m, hm⟩ := Int.ofNat_dvd.mpr hrq
      use m * (q : ℤ) ^ 7 +
        10 * (p : ℤ) ^ 2 * m * (q : ℤ) ^ 5 +
        4 * (p : ℤ) ^ 4 * m * (q : ℤ) ^ 3 -
        14 * (p : ℤ) ^ 6 * m * q
      rw [hm]
      ring
    have hsub := dvd_sub hdvd hdifference
    have hppow : (r : ℤ) ∣ (p : ℤ) ^ 8 := by
      simpa only [show
          (q : ℤ) ^ 8 + 10 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
              4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 -
              14 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8 -
            ((q : ℤ) ^ 8 + 10 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
              4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 -
              14 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2) =
            (p : ℤ) ^ 8 by ring] using hsub
    have hrp : r ∣ p :=
      hrPrime.dvd_of_dvd_pow (by exact_mod_cast hppow)
    exact hnp hrp

/-- The cubic coefficient consequently has `r`-adic valuation zero. -/
theorem homogeneousQuintic_coeff_three_padicValInt
    {p q r : ℕ} (hcop : p.Coprime q) (hrPrime : r.Prime)
    (hr : r ∣ p * q) :
    padicValInt r ((homogeneousQuintic p q).coeff 3) = 0 := by
  exact padicValInt.eq_zero_of_not_dvd
    (homogeneousQuintic_coeff_three_not_dvd hcop hrPrime hr)

/--
Exact degree-five scaling identity.  Thus a normalized constant `b`
becomes the homogeneous constant `q⁸ b`.
-/
theorem normalizedQuintic_scaleRoots_eq_homogeneous
    {p q : ℕ} (hq : 0 < q) :
    (normalizedQuintic (sharipovParameter p q)).scaleRoots ((q : ℚ) ^ 4) =
      homogeneousQuinticOver (p : ℚ) (q : ℚ) := by
  have hq0 : (q : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  ext i
  rw [coeff_scaleRoots]
  rw [show (normalizedQuintic (sharipovParameter p q)).natDegree = 5 by
    exact natDegree_eq_of_degree_eq_some
      (normalizedQuintic_degree (sharipovParameter p q))]
  by_cases hi : i ≤ 5
  · interval_cases i <;>
      rw [normalizedQuintic_coefficient_form] <;>
      simp only [homogeneousQuinticOver, homogeneousQuinticLowerOver,
        coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] <;>
      norm_num [quinticC4, quinticC3, quinticC2, quinticC1, quinticC0,
        sharipovParameter] <;>
      field_simp [hq0]
  · have h5i : 5 < i := by omega
    have hleft :
        (normalizedQuintic (sharipovParameter p q)).coeff i = 0 :=
      coeff_eq_zero_of_natDegree_lt (by
        rw [natDegree_eq_of_degree_eq_some
          (normalizedQuintic_degree (sharipovParameter p q))]
        exact h5i)
    have hright :
        (homogeneousQuinticOver (p : ℚ) (q : ℚ)).coeff i = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have hdegree :
          (homogeneousQuinticOver (p : ℚ) (q : ℚ)).degree = 5 := by
        unfold homogeneousQuinticOver
        rw [degree_add_eq_left_of_degree_lt
          ((homogeneousQuinticLowerOver_degree_le (p : ℚ) (q : ℚ)).trans_lt
            (by norm_num))]
        simp
      rw [natDegree_eq_of_degree_eq_some hdegree]
      exact h5i
    rw [hleft, hright]
    simp

/-- The homogeneous image of the prospective normalized quadratic. -/
def scaledMonicQuadratic (q a b : ℚ) : ℚ[X] :=
  X ^ 2 + C (q ^ 4 * a) * X + C (q ^ 8 * b)

/-- The stored prospective quadratic is monic. -/
theorem monicQuadratic_monic (a b : ℚ) :
    (monicQuadratic a b).Monic := by
  unfold monicQuadratic
  rw [show X ^ 2 + C a * X + C b = X ^ 2 + (C a * X + C b) by ring]
  apply monic_X_pow_add
  exact (degree_add_le_of_degree_le (degree_C_mul_X_le a)
    (degree_C_le.trans (by norm_num))).trans_lt (by norm_num)

/-- The stored prospective quadratic has degree two. -/
theorem monicQuadratic_natDegree (a b : ℚ) :
    (monicQuadratic a b).natDegree = 2 := by
  apply natDegree_eq_of_degree_eq_some
  unfold monicQuadratic
  rw [show X ^ 2 + C a * X + C b = X ^ 2 + (C a * X + C b) by ring]
  rw [degree_add_eq_left_of_degree_lt]
  · simp
  · exact (degree_add_le_of_degree_le (degree_C_mul_X_le a)
      (degree_C_le.trans (by norm_num))).trans_lt (by norm_num)

/-- The scaled prospective quadratic has degree two. -/
theorem scaledMonicQuadratic_natDegree (q a b : ℚ) :
    (scaledMonicQuadratic q a b).natDegree = 2 := by
  apply natDegree_eq_of_degree_eq_some
  unfold scaledMonicQuadratic
  rw [show X ^ 2 + C (q ^ 4 * a) * X + C (q ^ 8 * b) =
      X ^ 2 + (C (q ^ 4 * a) * X + C (q ^ 8 * b)) by ring]
  rw [degree_add_eq_left_of_degree_lt]
  · simp
  · exact (degree_add_le_of_degree_le (degree_C_mul_X_le (q ^ 4 * a))
      (degree_C_le.trans (by norm_num))).trans_lt (by norm_num)

/-- Scaling the normalized quadratic multiplies its two coefficients by `q⁴,q⁸`. -/
theorem monicQuadratic_scaleRoots (q a b : ℚ) :
    (monicQuadratic a b).scaleRoots (q ^ 4) =
      scaledMonicQuadratic q a b := by
  ext i
  rw [coeff_scaleRoots, monicQuadratic_natDegree]
  by_cases hi : i ≤ 2
  · interval_cases i <;>
      simp only [monicQuadratic, scaledMonicQuadratic, coeff_add,
        coeff_X_pow, coeff_C_mul_X, coeff_C] <;>
      norm_num <;>
      ring
  · have h2i : 2 < i := by omega
    rw [coeff_eq_zero_of_natDegree_lt (by
      rw [monicQuadratic_natDegree]
      exact h2i)]
    rw [coeff_eq_zero_of_natDegree_lt (by
      rw [scaledMonicQuadratic_natDegree]
      exact h2i)]
    simp

/-- The scaled prospective quadratic is monic. -/
theorem scaledMonicQuadratic_monic (q a b : ℚ) :
    (scaledMonicQuadratic q a b).Monic := by
  rw [← monicQuadratic_scaleRoots]
  exact (monic_scaleRoots_iff (q ^ 4)).2 (monicQuadratic_monic a b)

@[simp] theorem scaledMonicQuadratic_coeff_one (q a b : ℚ) :
    (scaledMonicQuadratic q a b).coeff 1 = q ^ 4 * a := by
  simp only [scaledMonicQuadratic, coeff_add, coeff_X_pow,
    coeff_C_mul_X, coeff_C]
  norm_num

@[simp] theorem scaledMonicQuadratic_coeff_zero (q a b : ℚ) :
    (scaledMonicQuadratic q a b).coeff 0 = q ^ 8 * b := by
  simp only [scaledMonicQuadratic, coeff_add, coeff_X_pow,
    coeff_C_mul_X, coeff_C]
  norm_num

/--
An explicit normalized factorization scales to a rational factorization of
the integral homogeneous quintic.
-/
theorem scaledMonicQuadratic_dvd_map_homogeneous
    {p q : ℕ} (hq : 0 < q) {a b : ℚ}
    (hfactor :
      normalizedQuintic (sharipovParameter p q) =
        monicQuadratic a b * forcedCubic (sharipovParameter p q) a b) :
    scaledMonicQuadratic (q : ℚ) a b ∣
      (homogeneousQuintic p q).map (algebraMap ℤ ℚ) := by
  have hscaled := congrArg
    (fun P : ℚ[X] => P.scaleRoots ((q : ℚ) ^ 4)) hfactor
  rw [mul_scaleRoots_of_noZeroDivisors, monicQuadratic_scaleRoots] at hscaled
  rw [map_homogeneousQuintic,
    ← normalizedQuintic_scaleRoots_eq_homogeneous hq]
  exact ⟨_, hscaled⟩

/--
Both scaled coefficients of a rational monic quadratic divisor are rational
integers.  This is the precise Gauss-lemma denominator statement used by
C012.
-/
theorem exists_integral_scaled_quadratic_coefficients
    {p q : ℕ} (hq : 0 < q) {a b : ℚ}
    (hfactor :
      normalizedQuintic (sharipovParameter p q) =
        monicQuadratic a b * forcedCubic (sharipovParameter p q) a b) :
    ∃ A B : ℤ,
      (A : ℚ) = (q : ℚ) ^ 4 * a ∧
      (B : ℚ) = (q : ℚ) ^ 8 * b := by
  have hdiv := scaledMonicQuadratic_dvd_map_homogeneous hq hfactor
  have hAint : IsIntegral ℤ ((q : ℚ) ^ 4 * a) := by
    simpa only [scaledMonicQuadratic_coeff_one] using
      (Polynomial.isIntegral_coeff_of_dvd
        (homogeneousQuintic p q) (scaledMonicQuadratic (q : ℚ) a b)
        (homogeneousQuintic_monic p q)
        (scaledMonicQuadratic_monic (q : ℚ) a b) hdiv 1)
  have hBint : IsIntegral ℤ ((q : ℚ) ^ 8 * b) := by
    simpa only [scaledMonicQuadratic_coeff_zero] using
      (Polynomial.isIntegral_coeff_of_dvd
        (homogeneousQuintic p q) (scaledMonicQuadratic (q : ℚ) a b)
        (homogeneousQuintic_monic p q)
        (scaledMonicQuadratic_monic (q : ℚ) a b) hdiv 0)
  obtain ⟨A, hA⟩ := IsIntegrallyClosed.isIntegral_iff.mp hAint
  obtain ⟨B, hB⟩ := IsIntegrallyClosed.isIntegral_iff.mp hBint
  exact ⟨A, B, hA, hB⟩

/-- The integral monic quadratic with coefficients `A,B`. -/
def integralMonicQuadratic (A B : ℤ) : ℤ[X] :=
  X ^ 2 + C A * X + C B

/-- The integral quadratic is monic. -/
theorem integralMonicQuadratic_monic (A B : ℤ) :
    (integralMonicQuadratic A B).Monic := by
  unfold integralMonicQuadratic
  rw [show X ^ 2 + C A * X + C B = X ^ 2 + (C A * X + C B) by ring]
  apply monic_X_pow_add
  exact (degree_add_le_of_degree_le (degree_C_mul_X_le A)
    (degree_C_le.trans (by norm_num))).trans_lt (by norm_num)

/-- Mapping an integral quadratic maps its two stored coefficients. -/
theorem map_integralMonicQuadratic (A B : ℤ) :
    (integralMonicQuadratic A B).map (algebraMap ℤ ℚ) =
      scaledMonicQuadratic (1 : ℚ) A B := by
  simp [integralMonicQuadratic, scaledMonicQuadratic]

/-- The integral quadratic has degree two. -/
theorem integralMonicQuadratic_natDegree (A B : ℤ) :
    (integralMonicQuadratic A B).natDegree = 2 := by
  apply natDegree_eq_of_degree_eq_some
  unfold integralMonicQuadratic
  rw [show X ^ 2 + C A * X + C B = X ^ 2 + (C A * X + C B) by ring]
  rw [degree_add_eq_left_of_degree_lt]
  · simp
  · exact (degree_add_le_of_degree_le (degree_C_mul_X_le A)
      (degree_C_le.trans (by norm_num))).trans_lt (by norm_num)

/-- Coefficient expansion of an integral monic cubic. -/
theorem integral_monic_cubic_coefficient_form
    {G : ℤ[X]} (hGmonic : G.Monic) (hGdeg : G.natDegree = 3) :
    G =
      X ^ 3 + C (G.coeff 2) * X ^ 2 +
        C (G.coeff 1) * X + C (G.coeff 0) := by
  have hcoeff3 : G.coeff 3 = 1 := by
    rw [← hGdeg]
    exact hGmonic.coeff_natDegree
  ext n
  by_cases hn : n ≤ 3
  · interval_cases n <;>
      simp only [coeff_add, coeff_X_pow, coeff_C_mul_X_pow,
        coeff_C_mul_X, coeff_C] <;>
      norm_num [hcoeff3]
  · have hlt : G.natDegree < n := by omega
    rw [coeff_eq_zero_of_natDegree_lt hlt]
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    simp only [coeff_add, coeff_X_pow, coeff_C_mul_X_pow,
      coeff_C_mul_X, coeff_C]
    simp [hn0, hn1, hn2, hn3]

/-- The four low coefficients of a monic quadratic times a monic cubic. -/
theorem integral_quadratic_times_cubic_coefficients
    (A B D E F : ℤ) :
    let product :=
      integralMonicQuadratic A B *
        (X ^ 3 + C D * X ^ 2 + C E * X + C F)
    product.coeff 0 = B * F ∧
      product.coeff 1 = A * F + B * E ∧
      product.coeff 2 = F + A * E + B * D ∧
      product.coeff 3 = E + A * D + B := by
  have hproduct :
      integralMonicQuadratic A B *
          (X ^ 3 + C D * X ^ 2 + C E * X + C F) =
        X ^ 5 + C (A + D) * X ^ 4 +
          C (E + A * D + B) * X ^ 3 +
          C (F + A * E + B * D) * X ^ 2 +
          C (A * F + B * E) * X + C (B * F) := by
    simp only [integralMonicQuadratic]
    simp only [map_add, map_mul]
    ring
  dsimp only
  rw [hproduct]
  simp only [coeff_add, coeff_X_pow, coeff_C_mul_X_pow,
    coeff_C_mul_X, coeff_C]
  norm_num

/--
The integral coefficient lift is an actual divisor over `ℤ`, not merely a
pair of integral rational numbers.
-/
theorem integralMonicQuadratic_dvd_homogeneous
    {p q : ℕ} (hq : 0 < q) {a b : ℚ}
    (hfactor :
      normalizedQuintic (sharipovParameter p q) =
        monicQuadratic a b * forcedCubic (sharipovParameter p q) a b) :
    ∃ A B : ℤ,
      (A : ℚ) = (q : ℚ) ^ 4 * a ∧
      (B : ℚ) = (q : ℚ) ^ 8 * b ∧
      integralMonicQuadratic A B ∣ homogeneousQuintic p q := by
  obtain ⟨A, B, hA, hB⟩ :=
    exists_integral_scaled_quadratic_coefficients hq hfactor
  have hmap :
      (integralMonicQuadratic A B).map (algebraMap ℤ ℚ) =
        scaledMonicQuadratic (q : ℚ) a b := by
    rw [map_integralMonicQuadratic]
    simp only [scaledMonicQuadratic, one_pow, one_mul]
    rw [hA, hB]
  have hmapdiv :
      (integralMonicQuadratic A B).map (algebraMap ℤ ℚ) ∣
        (homogeneousQuintic p q).map (algebraMap ℤ ℚ) := by
    rw [hmap]
    exact scaledMonicQuadratic_dvd_map_homogeneous hq hfactor
  exact ⟨A, B, hA, hB,
    (homogeneousQuintic_monic p q).dvd_of_fraction_map_dvd_fraction_map
      (integralMonicQuadratic_monic A B) hmapdiv⟩

/-- An integral quadratic divisor has a monic integral cubic quotient. -/
theorem integral_quadratic_quotient
    {p q : ℕ} {A B : ℤ}
    (hdiv : integralMonicQuadratic A B ∣ homogeneousQuintic p q) :
    ∃ G : ℤ[X],
      homogeneousQuintic p q = integralMonicQuadratic A B * G ∧
      G.Monic ∧ G.natDegree = 3 := by
  obtain ⟨G, hG⟩ := hdiv
  have hGmonic : G.Monic :=
    Monic.of_mul_monic_left (integralMonicQuadratic_monic A B)
      (hG ▸ homogeneousQuintic_monic p q)
  have hdegree :
      (homogeneousQuintic p q).natDegree = 5 :=
    natDegree_eq_of_degree_eq_some (homogeneousQuintic_degree p q)
  have hGdegree : G.natDegree = 3 := by
    have hmul :=
      (integralMonicQuadratic_monic A B).natDegree_mul hGmonic
    rw [← hG, hdegree, integralMonicQuadratic_natDegree] at hmul
    omega
  exact ⟨G, hG, hGmonic, hGdegree⟩

/--
The exact four low-coefficient equations for an integral quadratic factor.
These are the input to the local valuation calculation.
-/
theorem integral_quadratic_factor_coefficient_equations
    {p q : ℕ} {A B : ℤ}
    (hdiv : integralMonicQuadratic A B ∣ homogeneousQuintic p q) :
    ∃ D E F : ℤ,
      homogeneousQuintic p q =
        integralMonicQuadratic A B *
          (X ^ 3 + C D * X ^ 2 + C E * X + C F) ∧
      B * F = -((p : ℤ) ^ 10 * (q : ℤ) ^ 10) ∧
      A * F + B * E =
        -((p : ℤ) ^ 6 * (q : ℤ) ^ 6 *
          ((q : ℤ) ^ 2 + 2 * (p : ℤ) ^ 2) *
          (-2 * (q : ℤ) ^ 2 + 3 * (p : ℤ) ^ 2)) ∧
      F + A * E + B * D =
        -((p : ℤ) ^ 2 * (q : ℤ) ^ 2 *
          ((q : ℤ) ^ 8 - 14 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
            4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 +
            10 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8)) ∧
      E + A * D + B =
        (q : ℤ) ^ 8 + 10 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
          4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 -
          14 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8 := by
  obtain ⟨G, hG, hGmonic, hGdegree⟩ :=
    integral_quadratic_quotient hdiv
  let D := G.coeff 2
  let E := G.coeff 1
  let F := G.coeff 0
  have hGform :
      G = X ^ 3 + C D * X ^ 2 + C E * X + C F := by
    simpa only [D, E, F] using
      integral_monic_cubic_coefficient_form hGmonic hGdegree
  have hfactor :
      homogeneousQuintic p q =
        integralMonicQuadratic A B *
          (X ^ 3 + C D * X ^ 2 + C E * X + C F) := by
    rw [← hGform]
    exact hG
  have hcoeffs :=
    integral_quadratic_times_cubic_coefficients A B D E F
  dsimp only at hcoeffs
  refine ⟨D, E, F, hfactor, ?_, ?_, ?_, ?_⟩
  · rw [← homogeneousQuintic_coeff_zero p q]
    rw [hfactor]
    exact hcoeffs.1.symm
  · rw [← homogeneousQuintic_coeff_one p q]
    rw [hfactor]
    exact hcoeffs.2.1.symm
  · rw [← homogeneousQuintic_coeff_two p q]
    rw [hfactor]
    exact hcoeffs.2.2.1.symm
  · rw [← homogeneousQuintic_coeff_three p q]
    rw [hfactor]
    exact hcoeffs.2.2.2.symm

/-- The valuation of the common parameter powers in the low coefficients. -/
theorem padicValInt_neg_parameter_powers
    {r p q n : ℕ} (hrPrime : r.Prime) (hp : 0 < p) (hq : 0 < q) :
    padicValInt r (-((p : ℤ) ^ n * (q : ℤ) ^ n)) =
      n * padicValNat r (p * q) := by
  letI : Fact r.Prime := ⟨hrPrime⟩
  simp only [padicValInt]
  rw [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow]
  simp only [Int.natAbs_natCast]
  rw [padicValNat.mul (pow_ne_zero _ (Nat.ne_of_gt hp))
      (pow_ne_zero _ (Nat.ne_of_gt hq))]
  rw [padicValNat.pow, padicValNat.pow]
  rw [padicValNat.mul (Nat.ne_of_gt hp) (Nat.ne_of_gt hq)]
  exact (Nat.mul_add n _ _).symm

/--
The residual factor of the quadratic coefficient is a unit at every prime
dividing the product of coprime parameters.
-/
theorem homogeneousQuintic_coeff_two_core_not_dvd
    {p q r : ℕ} (hcop : p.Coprime q) (hrPrime : r.Prime)
    (hr : r ∣ p * q) :
    ¬(r : ℤ) ∣
      ((q : ℤ) ^ 8 - 14 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
        4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 +
        10 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8) := by
  intro hdvd
  rcases hrPrime.dvd_mul.mp hr with hrp | hrq
  · have hnq : ¬r ∣ q := by
      intro hrq
      have hrgcd : r ∣ Nat.gcd p q := Nat.dvd_gcd hrp hrq
      rw [hcop.gcd_eq_one] at hrgcd
      exact hrPrime.not_dvd_one hrgcd
    have hdifference : (r : ℤ) ∣
        (-14 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
          4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 +
          10 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8) := by
      obtain ⟨m, hm⟩ := Int.ofNat_dvd.mpr hrp
      use -14 * m * (p : ℤ) * (q : ℤ) ^ 6 +
        4 * m * (p : ℤ) ^ 3 * (q : ℤ) ^ 4 +
        10 * m * (p : ℤ) ^ 5 * (q : ℤ) ^ 2 +
        m * (p : ℤ) ^ 7
      rw [hm]
      ring
    have hsub := dvd_sub hdvd hdifference
    have hqpow : (r : ℤ) ∣ (q : ℤ) ^ 8 := by
      simpa only [show
          (q : ℤ) ^ 8 - 14 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
              4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 +
              10 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8 -
            (-14 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
              4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 +
              10 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8) =
            (q : ℤ) ^ 8 by ring] using hsub
    exact hnq (hrPrime.dvd_of_dvd_pow (by exact_mod_cast hqpow))
  · have hnp : ¬r ∣ p := by
      intro hrp
      have hrgcd : r ∣ Nat.gcd p q := Nat.dvd_gcd hrp hrq
      rw [hcop.gcd_eq_one] at hrgcd
      exact hrPrime.not_dvd_one hrgcd
    have hdifference : (r : ℤ) ∣
        ((q : ℤ) ^ 8 - 14 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
          4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 +
          10 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2) := by
      obtain ⟨m, hm⟩ := Int.ofNat_dvd.mpr hrq
      use m * (q : ℤ) ^ 7 -
        14 * (p : ℤ) ^ 2 * m * (q : ℤ) ^ 5 +
        4 * (p : ℤ) ^ 4 * m * (q : ℤ) ^ 3 +
        10 * (p : ℤ) ^ 6 * m * q
      rw [hm]
      ring
    have hsub := dvd_sub hdvd hdifference
    have hppow : (r : ℤ) ∣ (p : ℤ) ^ 8 := by
      simpa only [show
          (q : ℤ) ^ 8 - 14 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
              4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 +
              10 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8 -
            ((q : ℤ) ^ 8 - 14 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
              4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 +
              10 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2) =
            (p : ℤ) ^ 8 by ring] using hsub
    exact hnp (hrPrime.dvd_of_dvd_pow (by exact_mod_cast hppow))

/-- The quadratic coefficient has precisely valuation `2 v_r(pq)`. -/
theorem homogeneousQuintic_coeff_two_padicValInt
    {p q r : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hcop : p.Coprime q) (hrPrime : r.Prime) (hr : r ∣ p * q) :
    padicValInt r ((homogeneousQuintic p q).coeff 2) =
      2 * padicValNat r (p * q) := by
  letI : Fact r.Prime := ⟨hrPrime⟩
  rw [homogeneousQuintic_coeff_two]
  let core : ℤ :=
    (q : ℤ) ^ 8 - 14 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
      4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 +
      10 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8
  have hcoreDvd : ¬(r : ℤ) ∣ core :=
    homogeneousQuintic_coeff_two_core_not_dvd hcop hrPrime hr
  have hcore : core ≠ 0 := by
    intro hz
    exact hcoreDvd (hz ▸ dvd_zero (r : ℤ))
  rw [show
      -((p : ℤ) ^ 2 * (q : ℤ) ^ 2 * core) =
        (-((p : ℤ) ^ 2 * (q : ℤ) ^ 2)) * core by ring]
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [padicValInt.mul
    (neg_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero 2 hpz) (pow_ne_zero 2 hqz))) hcore]
  rw [padicValInt_neg_parameter_powers hrPrime hp hq]
  rw [padicValInt.eq_zero_of_not_dvd hcoreDvd]
  omega

/-- In particular the quadratic coefficient is nonzero. -/
theorem homogeneousQuintic_coeff_two_ne_zero
    {p q r : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hcop : p.Coprime q) (hrPrime : r.Prime) (hr : r ∣ p * q) :
    (homogeneousQuintic p q).coeff 2 ≠ 0 := by
  rw [homogeneousQuintic_coeff_two]
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hcore : ((q : ℤ) ^ 8 -
      14 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
      4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 +
      10 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8) ≠ 0 := by
    intro hz
    exact homogeneousQuintic_coeff_two_core_not_dvd hcop hrPrime hr
      (hz ▸ dvd_zero (r : ℤ))
  exact neg_ne_zero.mpr
    (mul_ne_zero
      (mul_ne_zero (pow_ne_zero 2 hpz) (pow_ne_zero 2 hqz))
      hcore)

/-- The linear coefficient is divisible through level `6 v_r(pq)`. -/
theorem homogeneousQuintic_coeff_one_pow_dvd
    {p q r : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hrPrime : r.Prime) :
    let k := padicValNat r (p * q)
    (r : ℤ) ^ (6 * k) ∣ (homogeneousQuintic p q).coeff 1 := by
  letI : Fact r.Prime := ⟨hrPrime⟩
  dsimp only
  rw [homogeneousQuintic_coeff_one]
  let rest : ℤ :=
    ((q : ℤ) ^ 2 + 2 * (p : ℤ) ^ 2) *
      (-2 * (q : ℤ) ^ 2 + 3 * (p : ℤ) ^ 2)
  have hbase :
      (r : ℤ) ^ (6 * padicValNat r (p * q)) ∣
        -((p : ℤ) ^ 6 * (q : ℤ) ^ 6) := by
    have hdvd :=
      padicValInt_dvd
        (p := r) (-((p : ℤ) ^ 6 * (q : ℤ) ^ 6))
    rw [padicValInt_neg_parameter_powers hrPrime hp hq] at hdvd
    exact hdvd
  have hmul := dvd_mul_of_dvd_left hbase rest
  simpa only [rest, show
      -((p : ℤ) ^ 6 * (q : ℤ) ^ 6) *
          (((q : ℤ) ^ 2 + 2 * (p : ℤ) ^ 2) *
            (-2 * (q : ℤ) ^ 2 + 3 * (p : ℤ) ^ 2)) =
        -((p : ℤ) ^ 6 * (q : ℤ) ^ 6 *
          ((q : ℤ) ^ 2 + 2 * (p : ℤ) ^ 2) *
          (-2 * (q : ℤ) ^ 2 + 3 * (p : ℤ) ^ 2)) by ring] using hmul

/-- The homogeneous constant of an integral quadratic divisor divides `p¹⁰q¹⁰`. -/
theorem integral_quadratic_constant_dvd
    {p q : ℕ} {A B : ℤ}
    (hdiv : integralMonicQuadratic A B ∣ homogeneousQuintic p q) :
    B ∣ (p : ℤ) ^ 10 * (q : ℤ) ^ 10 := by
  obtain ⟨G, hG⟩ := hdiv
  have hcoeff := congrArg (fun P : ℤ[X] => P.coeff 0) hG
  rw [mul_coeff_zero] at hcoeff
  have hproduct :
      -((p : ℤ) ^ 10 * (q : ℤ) ^ 10) = B * G.coeff 0 := by
    simp only [homogeneousQuintic, homogeneousQuinticOver,
      homogeneousQuinticLowerOver, integralMonicQuadratic, coeff_add,
      coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] at hcoeff
    norm_num at hcoeff
    exact hcoeff
  exact ⟨-(G.coeff 0), by
    calc
      (p : ℤ) ^ 10 * (q : ℤ) ^ 10 =
          -(-((p : ℤ) ^ 10 * (q : ℤ) ^ 10)) := by ring
      _ = -(B * G.coeff 0) := by rw [hproduct]
      _ = B * -(G.coeff 0) := by ring⟩

/--
A finite valuation used in the coefficient calculation.  Sending zero to a
fixed cap avoids separate cases for vanishing middle coefficients.
-/
def boundedPadicValInt (r cap : ℕ) (z : ℤ) : ℕ :=
  if z = 0 then cap else padicValInt r z

@[simp] theorem boundedPadicValInt_zero (r cap : ℕ) :
    boundedPadicValInt r cap 0 = cap := by
  simp [boundedPadicValInt]

theorem boundedPadicValInt_of_ne
    {r cap : ℕ} {z : ℤ} (hz : z ≠ 0) :
    boundedPadicValInt r cap z = padicValInt r z := by
  simp [boundedPadicValInt, hz]

/-- A bounded valuation lower bound gives divisibility, including at zero. -/
theorem pow_dvd_of_le_boundedPadicValInt
    {r cap n : ℕ} [Fact r.Prime] {z : ℤ}
    (h : n ≤ boundedPadicValInt r cap z) :
    (r : ℤ) ^ n ∣ z := by
  by_cases hz : z = 0
  · rw [hz]
    exact dvd_zero _
  · rw [boundedPadicValInt_of_ne hz] at h
    exact (padicValInt_dvd_iff n z).2 (Or.inr h)

/-- Below the cap, the next prime power does not divide. -/
theorem not_pow_dvd_of_boundedPadicValInt_lt
    {r cap n : ℕ} [Fact r.Prime] {z : ℤ}
    (hcap : boundedPadicValInt r cap z < cap)
    (hn : boundedPadicValInt r cap z < n) :
    ¬(r : ℤ) ^ n ∣ z := by
  have hz : z ≠ 0 := by
    intro hz
    rw [hz, boundedPadicValInt_zero] at hcap
    omega
  rw [boundedPadicValInt_of_ne hz] at hcap hn
  intro hdvd
  rcases (padicValInt_dvd_iff n z).1 hdvd with hz0 | hle
  · exact (hz hz0).elim
  · omega

/-- The sum of bounded valuations controls divisibility of a product. -/
theorem pow_dvd_mul_of_le_boundedPadicValInt_add
    {r cap n : ℕ} [Fact r.Prime] {x y : ℤ}
    (h :
      n ≤ boundedPadicValInt r cap x + boundedPadicValInt r cap y) :
    (r : ℤ) ^ n ∣ x * y := by
  by_cases hx : x = 0
  · rw [hx, zero_mul]
    exact dvd_zero _
  by_cases hy : y = 0
  · rw [hy, mul_zero]
    exact dvd_zero _
  rw [boundedPadicValInt_of_ne hx, boundedPadicValInt_of_ne hy] at h
  rw [← padicValInt.mul hx hy] at h
  exact (padicValInt_dvd_iff n (x * y)).2 (Or.inr h)

/-- Below the cap, the bounded sum is the exact valuation of a product. -/
theorem not_pow_dvd_mul_of_boundedPadicValInt_add_lt
    {r cap n : ℕ} [Fact r.Prime] {x y : ℤ}
    (hcap :
      boundedPadicValInt r cap x + boundedPadicValInt r cap y < cap)
    (hn :
      boundedPadicValInt r cap x + boundedPadicValInt r cap y < n) :
    ¬(r : ℤ) ^ n ∣ x * y := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, boundedPadicValInt_zero] at hcap
    omega
  have hy : y ≠ 0 := by
    intro hy
    rw [hy, boundedPadicValInt_zero] at hcap
    omega
  rw [boundedPadicValInt_of_ne hx, boundedPadicValInt_of_ne hy] at hcap hn
  rw [← padicValInt.mul hx hy] at hcap hn
  intro hdvd
  rcases (padicValInt_dvd_iff n (x * y)).1 hdvd with hxy | hle
  · exact (mul_ne_zero hx hy hxy).elim
  · omega

/--
If a two-term sum is divisible to `target`, unequal term valuations force
both terms to have valuation at least `target`.
-/
theorem boundedPadicValInt_two_term_cancellation
    {r cap target : ℕ} [Fact r.Prime] {x₁ x₂ y₁ y₂ : ℤ}
    (hcap : target < cap)
    (hdiv : (r : ℤ) ^ target ∣ x₁ * x₂ + y₁ * y₂) :
    let u :=
      boundedPadicValInt r cap x₁ + boundedPadicValInt r cap x₂
    let v :=
      boundedPadicValInt r cap y₁ + boundedPadicValInt r cap y₂
    u = v ∨ (target ≤ u ∧ target ≤ v) := by
  dsimp only
  let u :=
    boundedPadicValInt r cap x₁ + boundedPadicValInt r cap x₂
  let v :=
    boundedPadicValInt r cap y₁ + boundedPadicValInt r cap y₂
  by_cases huv : u = v
  · exact Or.inl huv
  right
  by_contra hnot
  simp only [not_and_or, not_le] at hnot
  rcases lt_or_gt_of_ne huv with huvlt | hvult
  · have hu : u < target := by omega
    have hucap : u < cap := lt_trans hu hcap
    have hnotx : ¬(r : ℤ) ^ (u + 1) ∣ x₁ * x₂ := by
      exact not_pow_dvd_mul_of_boundedPadicValInt_add_lt
        (r := r) (cap := cap) hucap (lt_add_one u)
    have hdy : (r : ℤ) ^ (u + 1) ∣ y₁ * y₂ := by
      exact pow_dvd_mul_of_le_boundedPadicValInt_add
        (r := r) (cap := cap) (by
          dsimp only [u, v] at huvlt ⊢
          omega)
    have hdsum : (r : ℤ) ^ (u + 1) ∣ x₁ * x₂ + y₁ * y₂ :=
      dvd_trans (pow_dvd_pow (r : ℤ) (by omega)) hdiv
    have hdx := dvd_sub hdsum hdy
    exact hnotx (by
      simpa only [show
          x₁ * x₂ + y₁ * y₂ - y₁ * y₂ = x₁ * x₂ by ring] using hdx)
  · have hv : v < target := by omega
    have hvcap : v < cap := lt_trans hv hcap
    have hnoty : ¬(r : ℤ) ^ (v + 1) ∣ y₁ * y₂ := by
      exact not_pow_dvd_mul_of_boundedPadicValInt_add_lt
        (r := r) (cap := cap) hvcap (lt_add_one v)
    have hdx : (r : ℤ) ^ (v + 1) ∣ x₁ * x₂ := by
      exact pow_dvd_mul_of_le_boundedPadicValInt_add
        (r := r) (cap := cap) (by
          dsimp only [u, v] at hvult ⊢
          omega)
    have hdsum : (r : ℤ) ^ (v + 1) ∣ x₁ * x₂ + y₁ * y₂ :=
      dvd_trans (pow_dvd_pow (r : ℤ) (by omega)) hdiv
    have hdy := dvd_sub hdsum hdx
    exact hnoty (by
      simpa only [show
          x₁ * x₂ + y₁ * y₂ - x₁ * x₂ = y₁ * y₂ by ring] using hdy)

/--
For a three-term sum of exact valuation `target`, a minimum below
`target` must occur at least twice.
-/
theorem boundedPadicValInt_three_term_cancellation
    {r cap target : ℕ} [Fact r.Prime] {x₁ x₂ y₁ y₂ z : ℤ}
    (hcap : target < cap)
    (hdiv : (r : ℤ) ^ target ∣ x₁ * x₂ + y₁ * y₂ + z)
    (hnotdiv : ¬(r : ℤ) ^ (target + 1) ∣ x₁ * x₂ + y₁ * y₂ + z) :
    let u :=
      boundedPadicValInt r cap x₁ + boundedPadicValInt r cap x₂
    let v :=
      boundedPadicValInt r cap y₁ + boundedPadicValInt r cap y₂
    let w := boundedPadicValInt r cap z
    min u (min v w) ≤ target ∧
      (min u (min v w) < target →
        (u = v ∧ u ≤ w) ∨
          (u = w ∧ u ≤ v) ∨
          (v = w ∧ v ≤ u)) := by
  dsimp only
  let u :=
    boundedPadicValInt r cap x₁ + boundedPadicValInt r cap x₂
  let v :=
    boundedPadicValInt r cap y₁ + boundedPadicValInt r cap y₂
  let w := boundedPadicValInt r cap z
  have hminimum : min u (min v w) ≤ target := by
    by_contra hnot
    have hu : target + 1 ≤ u := by omega
    have hv : target + 1 ≤ v := by omega
    have hw : target + 1 ≤ w := by omega
    have hdx : (r : ℤ) ^ (target + 1) ∣ x₁ * x₂ :=
      pow_dvd_mul_of_le_boundedPadicValInt_add
        (r := r) (cap := cap) (by
          dsimp only [u] at hu ⊢
          exact hu)
    have hdy : (r : ℤ) ^ (target + 1) ∣ y₁ * y₂ :=
      pow_dvd_mul_of_le_boundedPadicValInt_add
        (r := r) (cap := cap) (by
          dsimp only [v] at hv ⊢
          exact hv)
    have hdz : (r : ℤ) ^ (target + 1) ∣ z :=
      pow_dvd_of_le_boundedPadicValInt
        (r := r) (cap := cap) (by
          dsimp only [w] at hw ⊢
          exact hw)
    exact hnotdiv (dvd_add (dvd_add hdx hdy) hdz)
  refine ⟨hminimum, ?_⟩
  intro hminimumLt
  by_contra hcancel
  have hunique :
      (u < v ∧ u < w) ∨
        (v < u ∧ v < w) ∨
        (w < u ∧ w < v) := by
    omega
  rcases hunique with hu | hv | hw
  · have hutarget : u < target := by omega
    have hucap : u < cap := lt_trans hutarget hcap
    have hnotx : ¬(r : ℤ) ^ (u + 1) ∣ x₁ * x₂ :=
      not_pow_dvd_mul_of_boundedPadicValInt_add_lt
        (r := r) (cap := cap) hucap (lt_add_one u)
    have hdy : (r : ℤ) ^ (u + 1) ∣ y₁ * y₂ :=
      pow_dvd_mul_of_le_boundedPadicValInt_add
        (r := r) (cap := cap) (by
          dsimp only [u, v] at hu ⊢
          omega)
    have hdz : (r : ℤ) ^ (u + 1) ∣ z :=
      pow_dvd_of_le_boundedPadicValInt
        (r := r) (cap := cap) (by
          dsimp only [u, w] at hu ⊢
          omega)
    have hdsum : (r : ℤ) ^ (u + 1) ∣ x₁ * x₂ + y₁ * y₂ + z :=
      dvd_trans (pow_dvd_pow (r : ℤ) (by omega)) hdiv
    have hdx := dvd_sub (dvd_sub hdsum hdz) hdy
    exact hnotx (by
      simpa only [show
          x₁ * x₂ + y₁ * y₂ + z - z - y₁ * y₂ =
            x₁ * x₂ by ring] using hdx)
  · have hvtarget : v < target := by omega
    have hvcap : v < cap := lt_trans hvtarget hcap
    have hnoty : ¬(r : ℤ) ^ (v + 1) ∣ y₁ * y₂ :=
      not_pow_dvd_mul_of_boundedPadicValInt_add_lt
        (r := r) (cap := cap) hvcap (lt_add_one v)
    have hdx : (r : ℤ) ^ (v + 1) ∣ x₁ * x₂ :=
      pow_dvd_mul_of_le_boundedPadicValInt_add
        (r := r) (cap := cap) (by
          dsimp only [u, v] at hv ⊢
          omega)
    have hdz : (r : ℤ) ^ (v + 1) ∣ z :=
      pow_dvd_of_le_boundedPadicValInt
        (r := r) (cap := cap) (by
          dsimp only [v, w] at hv ⊢
          omega)
    have hdsum : (r : ℤ) ^ (v + 1) ∣ x₁ * x₂ + y₁ * y₂ + z :=
      dvd_trans (pow_dvd_pow (r : ℤ) (by omega)) hdiv
    have hdy := dvd_sub (dvd_sub hdsum hdz) hdx
    exact hnoty (by
      simpa only [show
          x₁ * x₂ + y₁ * y₂ + z - z - x₁ * x₂ =
            y₁ * y₂ by ring] using hdy)
  · have hwtarget : w < target := by omega
    have hwcap : w < cap := lt_trans hwtarget hcap
    have hnotz : ¬(r : ℤ) ^ (w + 1) ∣ z :=
      not_pow_dvd_of_boundedPadicValInt_lt
        (r := r) (cap := cap) hwcap (lt_add_one w)
    have hdx : (r : ℤ) ^ (w + 1) ∣ x₁ * x₂ :=
      pow_dvd_mul_of_le_boundedPadicValInt_add
        (r := r) (cap := cap) (by
          dsimp only [u, w] at hw ⊢
          omega)
    have hdy : (r : ℤ) ^ (w + 1) ∣ y₁ * y₂ :=
      pow_dvd_mul_of_le_boundedPadicValInt_add
        (r := r) (cap := cap) (by
          dsimp only [v, w] at hw ⊢
          omega)
    have hdsum : (r : ℤ) ^ (w + 1) ∣ x₁ * x₂ + y₁ * y₂ + z :=
      dvd_trans (pow_dvd_pow (r : ℤ) (by omega)) hdiv
    have hdz := dvd_sub hdsum (dvd_add hdx hdy)
    exact hnotz (by
      simpa only [show
          x₁ * x₂ + y₁ * y₂ + z - (x₁ * x₂ + y₁ * y₂) =
            z by ring] using hdz)

/--
The finite tropical calculation underlying the degree-two part of the
Newton polygon.  Here `alpha,beta,delta,eta,phi` are the valuations of
the five non-leading coefficients of a monic quadratic times a monic cubic.

The hypotheses are precisely the consequences of coefficient valuations
`v(c₀)=10k`, `v(c₁)≥6k`, `v(c₂)=2k`, and `v(c₃)=0`, including the only
possible cancellation alternatives.
-/
theorem quadratic_tropical_constant_classification
    (k alpha beta delta eta phi : ℕ)
    (h0 : beta + phi = 10 * k)
    (h3 : beta = 0 ∨ alpha + delta = 0 ∨ eta = 0)
    (h2le : min (beta + delta) (min (alpha + eta) phi) ≤ 2 * k)
    (h2cancel :
      min (beta + delta) (min (alpha + eta) phi) < 2 * k →
        (beta + delta = alpha + eta ∧ beta + delta ≤ phi) ∨
        (beta + delta = phi ∧ beta + delta ≤ alpha + eta) ∨
        (alpha + eta = phi ∧ alpha + eta ≤ beta + delta))
    (h1 :
      beta + eta = alpha + phi ∨
        (6 * k ≤ beta + eta ∧ 6 * k ≤ alpha + phi)) :
    beta = 0 ∨ beta = 2 * k ∨ beta = 4 * k ∨
      beta = 6 * k ∨ beta = 8 * k := by
  omega

/-- In particular the valuation selected by a quadratic factor is even. -/
theorem quadratic_tropical_constant_even
    (k alpha beta delta eta phi : ℕ)
    (h0 : beta + phi = 10 * k)
    (h3 : beta = 0 ∨ alpha + delta = 0 ∨ eta = 0)
    (h2le : min (beta + delta) (min (alpha + eta) phi) ≤ 2 * k)
    (h2cancel :
      min (beta + delta) (min (alpha + eta) phi) < 2 * k →
        (beta + delta = alpha + eta ∧ beta + delta ≤ phi) ∨
        (beta + delta = phi ∧ beta + delta ≤ alpha + eta) ∨
        (alpha + eta = phi ∧ alpha + eta ≤ beta + delta))
    (h1 :
      beta + eta = alpha + phi ∨
        (6 * k ≤ beta + eta ∧ 6 * k ≤ alpha + phi)) :
    Even beta := by
  have h := quadratic_tropical_constant_classification
    k alpha beta delta eta phi h0 h3 h2le h2cancel h1
  rcases h with h | h | h | h | h
  · rw [h]
    exact ⟨0, by omega⟩
  · rw [h]
    exact ⟨k, by omega⟩
  · rw [h]
    exact ⟨2 * k, by omega⟩
  · rw [h]
    exact ⟨3 * k, by omega⟩
  · rw [h]
    exact ⟨4 * k, by omega⟩

/-- A positive natural with even multiplicity at every prime is a square. -/
theorem nat_isSquare_of_even_factorization
    {n : ℕ} (hn : n ≠ 0)
    (heven : ∀ r : ℕ, r.Prime → Even (n.factorization r)) :
    IsSquare n := by
  let d : ℕ := n.factorization.prod (fun r e => r ^ (e / 2))
  refine ⟨d, ?_⟩
  rw [← pow_two, ← Nat.prod_factorization_pow_eq_self hn]
  dsimp [d]
  rw [pow_two, ← Finsupp.prod_mul]
  apply Finsupp.prod_congr
  intro r hr
  rw [← pow_add]
  have hrPrime : r.Prime := by
    by_contra hprime
    have hz : n.factorization r = 0 :=
      (Nat.factorization_eq_zero_iff n r).2 (Or.inl hprime)
    exact (Finsupp.mem_support_iff.mp hr) hz
  have htwo :
      n.factorization r / 2 + n.factorization r / 2 =
        n.factorization r := by
    have h := Nat.two_mul_div_two_of_even (heven r hrPrime)
    omega
  rw [htwo]

/-- Even prime multiplicities reconstruct one global physical sign and square. -/
theorem int_signedSquare_of_even_natAbs_factorization
    {B : ℤ} (hB : B ≠ 0)
    (heven : ∀ r : ℕ, r.Prime → Even (B.natAbs.factorization r)) :
    ∃ ε : PhysicalSign, ∃ d : ℤ, (B : ℚ) = ε.value * (d : ℚ) ^ 2 := by
  have hNat : IsSquare B.natAbs :=
    nat_isSquare_of_even_factorization (Int.natAbs_ne_zero.mpr hB) heven
  rcases hNat with ⟨d, hd⟩
  by_cases hnonneg : 0 ≤ B
  · refine ⟨PhysicalSign.positive, (d : ℤ), ?_⟩
    simp only [PhysicalSign.value_positive, one_mul]
    have hInt : B = (d : ℤ) ^ 2 := by
      rw [← Int.natAbs_of_nonneg hnonneg, hd]
      norm_num [pow_two]
    exact_mod_cast hInt
  · have hnegative : B < 0 := lt_of_not_ge hnonneg
    refine ⟨PhysicalSign.negative, (d : ℤ), ?_⟩
    simp only [PhysicalSign.value_negative, neg_one_mul]
    have habs : (B.natAbs : ℤ) = -B := by
      rw [Int.natCast_natAbs, abs_of_neg hnegative]
    have hpos : -B = (d : ℤ) ^ 2 := by
      calc
        -B = (B.natAbs : ℤ) := habs.symm
        _ = ((d * d : ℕ) : ℤ) := by rw [hd]
        _ = (d : ℤ) ^ 2 := by norm_num [pow_two]
    have hInt : B = -(d : ℤ) ^ 2 := by linarith
    exact_mod_cast hInt

/-- A genuine quadratic factor has nonzero constant away from `s=0`. -/
theorem forced_quadratic_constant_ne_zero
    {s a b : ℚ} (hs : s ≠ 0)
    (hfactor :
      normalizedQuintic s = monicQuadratic a b * forcedCubic s a b) :
    b ≠ 0 := by
  have hremainder := quadratic_remainders_of_forced_factorization hfactor
  intro hb
  have hzero : -(s ^ 5) = 0 := by
    simpa [quadraticR0, quinticC0, hb] using hremainder.2
  exact (neg_ne_zero.mpr (pow_ne_zero 5 hs)) hzero

/--
The exact remaining local input for C012.  Only primes dividing `p*q` need
the Newton calculation; divisibility of the constant handles every other
prime automatically.
-/
def HomogeneousQuadraticConstantsLocallyEven (p q : ℕ) : Prop :=
  ∀ A B : ℤ,
    integralMonicQuadratic A B ∣ homogeneousQuintic p q →
      ∀ r : ℕ, r.Prime → r ∣ p * q →
        Even (B.natAbs.factorization r)

/--
The local Newton-polygon conclusion, checked directly from the four
coefficient equations by finite divisibility and cancellation.
-/
theorem homogeneousQuadraticConstantsLocallyEven
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hcop : p.Coprime q) :
    HomogeneousQuadraticConstantsLocallyEven p q := by
  intro A B hdiv r hrPrime hr
  letI : Fact r.Prime := ⟨hrPrime⟩
  obtain ⟨D, E, F, _hfactor, h0eq, h1eq, h2eq, h3eq⟩ :=
    integral_quadratic_factor_coefficient_equations hdiv
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hBF : B * F ≠ 0 := by
    rw [h0eq]
    exact neg_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero 10 hpz) (pow_ne_zero 10 hqz))
  have hB : B ≠ 0 := (mul_ne_zero_iff.mp hBF).1
  have hF : F ≠ 0 := (mul_ne_zero_iff.mp hBF).2
  let k := padicValNat r (p * q)
  have hpq : p * q ≠ 0 :=
    Nat.mul_ne_zero (Nat.ne_of_gt hp) (Nat.ne_of_gt hq)
  have hk : 0 < k :=
    one_le_padicValNat_of_dvd hpq hr
  let cap := 10 * k + 1
  let alpha := boundedPadicValInt r cap A
  let beta := boundedPadicValInt r cap B
  let delta := boundedPadicValInt r cap D
  let eta := boundedPadicValInt r cap E
  let phi := boundedPadicValInt r cap F
  have h0 : beta + phi = 10 * k := by
    rw [show beta = padicValInt r B by
      exact boundedPadicValInt_of_ne hB]
    rw [show phi = padicValInt r F by
      exact boundedPadicValInt_of_ne hF]
    rw [← padicValInt.mul hB hF]
    rw [h0eq]
    exact padicValInt_neg_parameter_powers hrPrime hp hq
  have h3coeff :
      E + A * D + B = (homogeneousQuintic p q).coeff 3 := by
    calc
      E + A * D + B =
          (q : ℤ) ^ 8 + 10 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
            4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 -
            14 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8 := h3eq
      _ = (homogeneousQuintic p q).coeff 3 :=
        (homogeneousQuintic_coeff_three p q).symm
  have h3 : beta = 0 ∨ alpha + delta = 0 ∨ eta = 0 := by
    by_contra hnone
    have hbeta : 1 ≤ beta := by omega
    have halphaDelta : 1 ≤ alpha + delta := by omega
    have heta : 1 ≤ eta := by omega
    have hBdiv : (r : ℤ) ∣ B := by
      simpa only [pow_one] using
        (pow_dvd_of_le_boundedPadicValInt
          (r := r) (cap := cap) hbeta)
    have hADdiv : (r : ℤ) ∣ A * D := by
      simpa only [pow_one] using
        (pow_dvd_mul_of_le_boundedPadicValInt_add
          (r := r) (cap := cap) halphaDelta)
    have hEdiv : (r : ℤ) ∣ E := by
      simpa only [pow_one] using
        (pow_dvd_of_le_boundedPadicValInt
          (r := r) (cap := cap) heta)
    have hsum : (r : ℤ) ∣ E + A * D + B :=
      dvd_add (dvd_add hEdiv hADdiv) hBdiv
    apply homogeneousQuintic_coeff_three_not_dvd hcop hrPrime hr
    rw [← h3coeff]
    exact hsum
  have h2coeff :
      F + A * E + B * D = (homogeneousQuintic p q).coeff 2 := by
    calc
      F + A * E + B * D =
          -((p : ℤ) ^ 2 * (q : ℤ) ^ 2 *
            ((q : ℤ) ^ 8 - 14 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 +
              4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 +
              10 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 +
              (p : ℤ) ^ 8)) := h2eq
      _ = (homogeneousQuintic p q).coeff 2 :=
        (homogeneousQuintic_coeff_two p q).symm
  have hc2val :
      padicValInt r ((homogeneousQuintic p q).coeff 2) = 2 * k :=
    homogeneousQuintic_coeff_two_padicValInt hp hq hcop hrPrime hr
  have hc2ne : (homogeneousQuintic p q).coeff 2 ≠ 0 :=
    homogeneousQuintic_coeff_two_ne_zero hp hq hcop hrPrime hr
  have hc2div :
      (r : ℤ) ^ (2 * k) ∣ (homogeneousQuintic p q).coeff 2 := by
    have hdvd :=
      padicValInt_dvd (p := r) ((homogeneousQuintic p q).coeff 2)
    rw [hc2val] at hdvd
    exact hdvd
  have hc2notdiv :
      ¬(r : ℤ) ^ (2 * k + 1) ∣
        (homogeneousQuintic p q).coeff 2 := by
    intro hdvd
    rcases (padicValInt_dvd_iff
      (2 * k + 1) ((homogeneousQuintic p q).coeff 2)).1 hdvd with hz | hle
    · exact hc2ne hz
    · rw [hc2val] at hle
      omega
  have h2sum :
      B * D + A * E + F = (homogeneousQuintic p q).coeff 2 := by
    calc
      B * D + A * E + F = F + A * E + B * D := by ring
      _ = (homogeneousQuintic p q).coeff 2 := h2coeff
  have h2div : (r : ℤ) ^ (2 * k) ∣ B * D + A * E + F := by
    rw [h2sum]
    exact hc2div
  have h2notdiv :
      ¬(r : ℤ) ^ (2 * k + 1) ∣ B * D + A * E + F := by
    rw [h2sum]
    exact hc2notdiv
  have h2raw :=
    boundedPadicValInt_three_term_cancellation
      (r := r) (cap := cap) (target := 2 * k)
      (x₁ := B) (x₂ := D) (y₁ := A) (y₂ := E) (z := F)
      (by dsimp only [cap]; omega) h2div h2notdiv
  have h2 :
      min (beta + delta) (min (alpha + eta) phi) ≤ 2 * k ∧
        (min (beta + delta) (min (alpha + eta) phi) < 2 * k →
          (beta + delta = alpha + eta ∧ beta + delta ≤ phi) ∨
          (beta + delta = phi ∧ beta + delta ≤ alpha + eta) ∨
          (alpha + eta = phi ∧ alpha + eta ≤ beta + delta)) := by
    simpa only [alpha, beta, delta, eta, phi] using h2raw
  have h1coeff :
      A * F + B * E = (homogeneousQuintic p q).coeff 1 := by
    calc
      A * F + B * E =
          -((p : ℤ) ^ 6 * (q : ℤ) ^ 6 *
            ((q : ℤ) ^ 2 + 2 * (p : ℤ) ^ 2) *
            (-2 * (q : ℤ) ^ 2 + 3 * (p : ℤ) ^ 2)) := h1eq
      _ = (homogeneousQuintic p q).coeff 1 :=
        (homogeneousQuintic_coeff_one p q).symm
  have hc1div :
      (r : ℤ) ^ (6 * k) ∣ (homogeneousQuintic p q).coeff 1 :=
    homogeneousQuintic_coeff_one_pow_dvd hp hq hrPrime
  have h1sum :
      B * E + A * F = (homogeneousQuintic p q).coeff 1 := by
    calc
      B * E + A * F = A * F + B * E := by ring
      _ = (homogeneousQuintic p q).coeff 1 := h1coeff
  have h1div : (r : ℤ) ^ (6 * k) ∣ B * E + A * F := by
    rw [h1sum]
    exact hc1div
  have h1raw :=
    boundedPadicValInt_two_term_cancellation
      (r := r) (cap := cap) (target := 6 * k)
      (x₁ := B) (x₂ := E) (y₁ := A) (y₂ := F)
      (by dsimp only [cap]; omega) h1div
  have h1 :
      beta + eta = alpha + phi ∨
        (6 * k ≤ beta + eta ∧ 6 * k ≤ alpha + phi) := by
    simpa only [alpha, beta, eta, phi] using h1raw
  have hbetaEven : Even beta :=
    quadratic_tropical_constant_even
      k alpha beta delta eta phi h0 h3 h2.1 h2.2 h1
  rw [B.natAbs.factorization_def hrPrime]
  have hbeta : beta = padicValInt r B :=
    boundedPadicValInt_of_ne hB
  rw [hbeta] at hbetaEven
  exact hbetaEven

/--
Once the local Newton calculation is available at primes dividing `p*q`,
the integral lift and unique factorization reconstruct the signed square
required by the compact reduction.
-/
theorem quadraticFactorConstantsSignedSquare_of_locallyEven
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hlocal : HomogeneousQuadraticConstantsLocallyEven p q) :
    QuadraticFactorConstantsSignedSquare (sharipovParameter p q) := by
  intro a b hfactor
  obtain ⟨A, B, hA, hB, hdiv⟩ :=
    integralMonicQuadratic_dvd_homogeneous hq hfactor
  have hs : sharipovParameter p q ≠ 0 :=
    ne_of_gt (sharipovParameter_pos hp hq)
  have hb : b ≠ 0 :=
    forced_quadratic_constant_ne_zero hs hfactor
  have hq0 : (q : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  have hB0 : B ≠ 0 := by
    intro hBzero
    apply hb
    have hz : (q : ℚ) ^ 8 * b = 0 := by
      rw [← hB]
      simp [hBzero]
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 8 hq0)
  have heven :
      ∀ r : ℕ, r.Prime → Even (B.natAbs.factorization r) := by
    intro r hrPrime
    by_cases hr : r ∣ p * q
    · exact hlocal A B hdiv r hrPrime hr
    · have hBdvd :
          B ∣ (p : ℤ) ^ 10 * (q : ℤ) ^ 10 :=
        integral_quadratic_constant_dvd hdiv
      have hnat :
          B.natAbs ∣ p ^ 10 * q ^ 10 := by
        have habs :
            B.natAbs ∣
              (((p : ℤ) ^ 10 * (q : ℤ) ^ 10).natAbs) :=
          Int.natAbs_dvd_natAbs.mpr hBdvd
        simpa [Int.natAbs_mul, Int.natAbs_pow] using habs
      have hrB : ¬r ∣ B.natAbs := by
        intro hrB
        have hrpqpow : r ∣ p ^ 10 * q ^ 10 :=
          dvd_trans hrB hnat
        rcases (hrPrime.dvd_mul.mp hrpqpow) with hrp | hrq
        · exact hr (dvd_mul_of_dvd_left (hrPrime.dvd_of_dvd_pow hrp) q)
        · exact hr (dvd_mul_of_dvd_right (hrPrime.dvd_of_dvd_pow hrq) p)
      rw [(Nat.factorization_eq_zero_iff B.natAbs r).2
        (Or.inr (Or.inl hrB))]
      exact ⟨0, by omega⟩
  obtain ⟨ε, d, hBsquare⟩ :=
    int_signedSquare_of_even_natAbs_factorization hB0 heven
  refine ⟨ε, (d : ℚ) / (q : ℚ) ^ 4, ?_⟩
  field_simp [hq0]
  calc
    b * (q : ℚ) ^ 8 = (q : ℚ) ^ 8 * b := by ring
    _ = (B : ℚ) := hB.symm
    _ = ε.value * (d : ℚ) ^ 2 := hBsquare

/-- Claim C012 for every admissible pair of coprime positive parameters. -/
theorem quadraticFactorConstantsSignedSquare_sharipov
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hcop : p.Coprime q) :
    QuadraticFactorConstantsSignedSquare (sharipovParameter p q) :=
  quadraticFactorConstantsSignedSquare_of_locallyEven hp hq
    (homogeneousQuadraticConstantsLocallyEven hp hq hcop)

/-- The unconditional compact-model entrance for an admissible `2+3` case. -/
theorem quadraticCubicCase_to_compact_sharipov
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hcop : p.Coprime q)
    (hcase : QuadraticCubicCase (sharipovParameter p q)) :
    ∃ ε : PhysicalSign, ∃ z k y : ℚ,
      z ≠ 0 ∧ k ≠ 0 ∧
      sharipovParameter p q = z ^ 2 ∧
      compactF1 ε z k y = 0 ∧ compactF0 ε z k y = 0 :=
  quadraticCubicCase_to_compact hp hq hcase
    (quadraticFactorConstantsSignedSquare_sharipov hp hq hcop)

end

end Cuboid2
