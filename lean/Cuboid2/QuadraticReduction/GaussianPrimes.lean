import Cuboid2.QuadraticReduction.GaussianDescent

/-!
# Distinguished Gaussian primes for the two-isogeny descent

This module records the three Gaussian prime elements that support the four
specialized descent problems.  Primality is proved internally from the
Gaussian norm and the Euclidean-domain structure on `GaussianInt`.  It also
records exact integral factorizations of the four `B` coefficients and the
two squareclasses represented by Gaussian units.
-/

namespace Cuboid2

noncomputable section

namespace GaussianPrimes

open GaussianDescent
open GaussianFraction

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

@[simp] private theorem gaussianRat_one_re :
    (1 : GaussianRat).re = 1 := rfl

@[simp] private theorem gaussianRat_one_im :
    (1 : GaussianRat).im = 0 := rfl

/-- The Gaussian unit `i`. -/
def gaussianIInt : GaussianInt := ⟨0, 1⟩

/-- The ramified Gaussian prime `lambda = 1+i` above `2`. -/
def gaussianLambdaInt : GaussianInt := ⟨1, 1⟩

/-- The Gaussian prime `pi = 1+2i` above `5`. -/
def gaussianPiInt : GaussianInt := ⟨1, 2⟩

/-- The Gaussian prime `rho = 1+4i` above `17`. -/
def gaussianRhoInt : GaussianInt := ⟨1, 4⟩

@[simp] theorem gaussianIInt_norm : gaussianIInt.norm = 1 := by
  norm_num [gaussianIInt, Zsqrtd.norm]

@[simp] theorem gaussianLambdaInt_norm : gaussianLambdaInt.norm = 2 := by
  norm_num [gaussianLambdaInt, Zsqrtd.norm]

@[simp] theorem gaussianPiInt_norm : gaussianPiInt.norm = 5 := by
  norm_num [gaussianPiInt, Zsqrtd.norm]

@[simp] theorem gaussianRhoInt_norm : gaussianRhoInt.norm = 17 := by
  norm_num [gaussianRhoInt, Zsqrtd.norm]

/-- An element of `GaussianInt` with prime absolute norm is prime. -/
theorem prime_of_normNatAbs_prime {z : GaussianInt}
    (hz : Nat.Prime z.norm.natAbs) : Prime z := by
  apply Irreducible.prime
  rw [irreducible_iff]
  constructor
  · intro hu
    exact hz.ne_one ((Zsqrtd.norm_eq_one_iff).2 hu)
  · intro a b hab
    have hnorm :
        z.norm.natAbs = a.norm.natAbs * b.norm.natAbs := by
      rw [hab, Zsqrtd.norm_mul, Int.natAbs_mul]
    have haDvd : a.norm.natAbs ∣ z.norm.natAbs :=
      ⟨b.norm.natAbs, hnorm⟩
    rcases hz.eq_one_or_self_of_dvd _ haDvd with haOne | haPrime
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp haOne)
    · right
      apply Zsqrtd.norm_eq_one_iff.mp
      rw [haPrime] at hnorm
      exact Nat.mul_left_cancel hz.pos (by simpa using hnorm.symm)

/-- `1+i` is prime in `GaussianInt`. -/
theorem gaussianLambdaInt_prime : Prime gaussianLambdaInt := by
  apply prime_of_normNatAbs_prime
  norm_num

/-- `1+2i` is prime in `GaussianInt`. -/
theorem gaussianPiInt_prime : Prime gaussianPiInt := by
  apply prime_of_normNatAbs_prime
  norm_num

/-- `1+4i` is prime in `GaussianInt`. -/
theorem gaussianRhoInt_prime : Prime gaussianRhoInt := by
  apply prime_of_normNatAbs_prime
  norm_num

/-! ## Pairwise nonassociation -/

/-- Divisibility in `GaussianInt` implies divisibility of absolute norms. -/
theorem normNatAbs_dvd_of_dvd {a b : GaussianInt} (h : a ∣ b) :
    a.norm.natAbs ∣ b.norm.natAbs := by
  obtain ⟨c, rfl⟩ := h
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  exact dvd_mul_right _ _

theorem lambda_not_dvd_pi : ¬gaussianLambdaInt ∣ gaussianPiInt := by
  intro h
  have := normNatAbs_dvd_of_dvd h
  norm_num at this

theorem pi_not_dvd_lambda : ¬gaussianPiInt ∣ gaussianLambdaInt := by
  intro h
  have := normNatAbs_dvd_of_dvd h
  norm_num at this

theorem lambda_not_dvd_rho : ¬gaussianLambdaInt ∣ gaussianRhoInt := by
  intro h
  have := normNatAbs_dvd_of_dvd h
  norm_num at this

theorem rho_not_dvd_lambda : ¬gaussianRhoInt ∣ gaussianLambdaInt := by
  intro h
  have := normNatAbs_dvd_of_dvd h
  norm_num at this

theorem pi_not_dvd_rho : ¬gaussianPiInt ∣ gaussianRhoInt := by
  intro h
  have := normNatAbs_dvd_of_dvd h
  norm_num at this

theorem rho_not_dvd_pi : ¬gaussianRhoInt ∣ gaussianPiInt := by
  intro h
  have := normNatAbs_dvd_of_dvd h
  norm_num at this

theorem lambda_not_associated_pi :
    ¬Associated gaussianLambdaInt gaussianPiInt := by
  intro h
  exact lambda_not_dvd_pi h.dvd

theorem lambda_not_associated_rho :
    ¬Associated gaussianLambdaInt gaussianRhoInt := by
  intro h
  exact lambda_not_dvd_rho h.dvd

theorem pi_not_associated_rho :
    ¬Associated gaussianPiInt gaussianRhoInt := by
  intro h
  exact pi_not_dvd_rho h.dvd

/-! ## Embedding into the project model of `ℚ(i)` -/

@[simp] theorem algebraMap_gaussianIInt :
    algebraMap GaussianInt GaussianRat gaussianIInt = gaussianI := by
  rw [algebraMap_gaussianInt_apply]
  ext <;> norm_num [gaussianIInt, gaussianI]

@[simp] theorem algebraMap_gaussianLambdaInt :
    algebraMap GaussianInt GaussianRat gaussianLambdaInt = 1 + gaussianI := by
  rw [algebraMap_gaussianInt_apply]
  ext <;> norm_num [gaussianLambdaInt, gaussianI]

@[simp] theorem algebraMap_gaussianPiInt :
    algebraMap GaussianInt GaussianRat gaussianPiInt = gaussianPi := by
  rw [algebraMap_gaussianInt_apply]
  ext <;>
    norm_num [gaussianPiInt, gaussianPi, gaussianI,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

@[simp] theorem algebraMap_gaussianRhoInt :
    algebraMap GaussianInt GaussianRat gaussianRhoInt = gaussianRho := by
  rw [algebraMap_gaussianInt_apply]
  ext <;>
    norm_num [gaussianRhoInt, gaussianRho, gaussianI,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

/-! ## Exact coefficient factorizations -/

/-- The integral `B` coefficient of `E₀`. -/
def e0BInt : GaussianInt := ⟨-2, -4⟩

/-- The integral `B` coefficient of `E₁`. -/
def e1BInt : GaussianInt := ⟨2, 4⟩

/-- The integral `B` coefficient of the dual of `E₀`. -/
def e0DualBInt : GaussianInt := ⟨4, 16⟩

/-- The integral `B` coefficient of the dual of `E₁`. -/
def e1DualBInt : GaussianInt := ⟨-4, -16⟩

/-- `B(E₀) = i * lambda^2 * pi`. -/
theorem e0BInt_factorization :
    e0BInt =
      gaussianIInt * gaussianLambdaInt ^ 2 * gaussianPiInt := by
  decide

/-- `B(E₁) = -i * lambda^2 * pi`. -/
theorem e1BInt_factorization :
    e1BInt =
      -gaussianIInt * gaussianLambdaInt ^ 2 * gaussianPiInt := by
  decide

/-- `B(E₀') = -lambda^4 * rho`. -/
theorem e0DualBInt_factorization :
    e0DualBInt = -(gaussianLambdaInt ^ 4) * gaussianRhoInt := by
  decide

/-- `B(E₁') = lambda^4 * rho`. -/
theorem e1DualBInt_factorization :
    e1DualBInt = gaussianLambdaInt ^ 4 * gaussianRhoInt := by
  decide

/-- The integral coefficient `e0BInt` maps to the coefficient `E0B`. -/
@[simp] theorem algebraMap_e0BInt :
    algebraMap GaussianInt GaussianRat e0BInt = E0B := by
  rw [algebraMap_gaussianInt_apply]
  ext <;>
    norm_num [e0BInt, E0B, gaussianI,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

/-- The integral coefficient `e1BInt` maps to the coefficient `E1B`. -/
@[simp] theorem algebraMap_e1BInt :
    algebraMap GaussianInt GaussianRat e1BInt = E1B := by
  rw [algebraMap_gaussianInt_apply]
  ext <;>
    norm_num [e1BInt, E1B, gaussianI,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

/-- The integral dual coefficient maps to `E0A^2 - 4*E0B`. -/
@[simp] theorem algebraMap_e0DualBInt :
    algebraMap GaussianInt GaussianRat e0DualBInt =
      E0A ^ 2 - 4 * E0B := by
  rw [algebraMap_gaussianInt_apply]
  ext <;>
    norm_num [e0DualBInt, E0A, E0B, gaussianI, pow_two,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

/-- The integral dual coefficient maps to `E1A^2 - 4*E1B`. -/
@[simp] theorem algebraMap_e1DualBInt :
    algebraMap GaussianInt GaussianRat e1DualBInt =
      E1A ^ 2 - 4 * E1B := by
  rw [algebraMap_gaussianInt_apply]
  ext <;>
    norm_num [e1DualBInt, E1A, E1B, gaussianI, pow_two,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

/-! ## Gaussian units modulo squares -/

/-- Every Gaussian unit represents either the squareclass of `1` or that of
`i`.  The witness is an actual Gaussian integer square.
-/
theorem unit_eq_square_or_i_mul_square (u : GaussianIntˣ) :
    ∃ z : GaussianInt,
      (u : GaussianInt) = z ^ 2 ∨
        (u : GaussianInt) = gaussianIInt * z ^ 2 := by
  have hnorm : (u : GaussianInt).norm = 1 :=
    (Zsqrtd.norm_eq_one_iff' (by norm_num) (u : GaussianInt)).2 u.isUnit
  have hsum :
      (u : GaussianInt).re * (u : GaussianInt).re +
          (u : GaussianInt).im * (u : GaussianInt).im = 1 := by
    simpa [Zsqrtd.norm_def] using hnorm
  have hreLower : -1 ≤ (u : GaussianInt).re := by nlinarith
  have hreUpper : (u : GaussianInt).re ≤ 1 := by nlinarith
  have himLower : -1 ≤ (u : GaussianInt).im := by nlinarith
  have himUpper : (u : GaussianInt).im ≤ 1 := by nlinarith
  interval_cases hre : (u : GaussianInt).re <;>
    interval_cases him : (u : GaussianInt).im <;>
    norm_num at hsum
  · refine ⟨gaussianIInt, Or.inl ?_⟩
    apply Zsqrtd.ext
    · rw [hre]
      decide
    · rw [him]
      decide
  · refine ⟨gaussianIInt, Or.inr ?_⟩
    apply Zsqrtd.ext
    · rw [hre]
      decide
    · rw [him]
      decide
  · refine ⟨1, Or.inr ?_⟩
    apply Zsqrtd.ext
    · simpa [gaussianIInt] using hre
    · simpa [gaussianIInt] using him
  · refine ⟨1, Or.inl ?_⟩
    apply Zsqrtd.ext
    · simpa [gaussianIInt] using hre
    · simpa [gaussianIInt] using him

/-- Element-level form of `unit_eq_square_or_i_mul_square`. -/
theorem isUnit_eq_square_or_i_mul_square {u : GaussianInt} (hu : IsUnit u) :
    ∃ z : GaussianInt,
      u = z ^ 2 ∨ u = gaussianIInt * z ^ 2 := by
  obtain ⟨v, rfl⟩ := hu
  exact unit_eq_square_or_i_mul_square v

end GaussianPrimes

end

end Cuboid2
