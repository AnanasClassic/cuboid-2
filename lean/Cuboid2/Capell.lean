import Cuboid2.Scaling

/-!
# Reflection and even-polynomial infrastructure for Capell's step

The involution `X ↦ -X` is the key symmetry of `P(X^2)`.  This file proves
that its fixed polynomials are exactly the image of the exponent-doubling map
`Polynomial.expand ℚ 2`, with an explicit inverse supplied by
`Polynomial.contract 2`.  These are the algebraic tools needed to turn a
proper factor paired with its reflected factor into a proper factor of the
original quintic.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- Substitute `-X` into a rational polynomial. -/
def reflectPolynomial (P : ℚ[X]) : ℚ[X] :=
  P.comp (-X)

@[simp] theorem reflectPolynomial_zero :
    reflectPolynomial (0 : ℚ[X]) = 0 := by
  simp [reflectPolynomial]

@[simp] theorem reflectPolynomial_one :
    reflectPolynomial (1 : ℚ[X]) = 1 := by
  simp [reflectPolynomial]

@[simp] theorem reflectPolynomial_add (P Q : ℚ[X]) :
    reflectPolynomial (P + Q) = reflectPolynomial P + reflectPolynomial Q := by
  simp [reflectPolynomial]

@[simp] theorem reflectPolynomial_mul (P Q : ℚ[X]) :
    reflectPolynomial (P * Q) = reflectPolynomial P * reflectPolynomial Q := by
  simp [reflectPolynomial]

@[simp] theorem reflectPolynomial_neg (P : ℚ[X]) :
    reflectPolynomial (-P) = -reflectPolynomial P := by
  simp [reflectPolynomial]

/-- Reflection is an involution. -/
@[simp] theorem reflectPolynomial_involutive (P : ℚ[X]) :
    reflectPolynomial (reflectPolynomial P) = P := by
  simp [reflectPolynomial, comp_assoc]

/-- Coefficients under reflection acquire the expected sign. -/
theorem reflectPolynomial_coeff (P : ℚ[X]) (n : ℕ) :
    (reflectPolynomial P).coeff n = P.coeff n * (-1 : ℚ) ^ n := by
  change (P.comp (-X)).coeff n = P.coeff n * (-1 : ℚ) ^ n
  rw [show (-X : ℚ[X]) = C (-1 : ℚ) * X by simp]
  exact comp_C_mul_X_coeff

/-- Reflection preserves and reflects units. -/
theorem isUnit_reflectPolynomial_iff (P : ℚ[X]) :
    IsUnit (reflectPolynomial P) ↔ IsUnit P := by
  constructor
  · intro h
    have hmapped := IsUnit.map (compRingHom (-X : ℚ[X])) h
    change IsUnit (reflectPolynomial (reflectPolynomial P)) at hmapped
    simpa using hmapped
  · intro h
    have hmapped := IsUnit.map (compRingHom (-X : ℚ[X])) h
    change IsUnit (reflectPolynomial P) at hmapped
    exact hmapped

/-- Reflection preserves and reflects irreducibility. -/
theorem irreducible_reflectPolynomial_iff (P : ℚ[X]) :
    Irreducible (reflectPolynomial P) ↔ Irreducible P := by
  have preserve : ∀ Q : ℚ[X], Irreducible Q → Irreducible (reflectPolynomial Q) := by
    intro Q hQ
    refine ⟨?_, ?_⟩
    · intro hunit
      exact hQ.not_isUnit ((isUnit_reflectPolynomial_iff Q).1 hunit)
    · intro A B hfactor
      have hreflected := congrArg reflectPolynomial hfactor
      have hfactor' : Q = reflectPolynomial A * reflectPolynomial B := by
        simpa using hreflected
      rcases hQ.isUnit_or_isUnit hfactor' with hA | hB
      · exact Or.inl ((isUnit_reflectPolynomial_iff A).1 hA)
      · exact Or.inr ((isUnit_reflectPolynomial_iff B).1 hB)
  constructor
  · intro h
    have hh := preserve (reflectPolynomial P) h
    simpa using hh
  · exact preserve P

/-- Reflecting a divisor of a fixed polynomial gives another divisor. -/
theorem reflectPolynomial_dvd_of_dvd_fixed
    {P F : ℚ[X]} (hfixed : reflectPolynomial F = F) (hdiv : P ∣ F) :
    reflectPolynomial P ∣ F := by
  have hmapped := map_dvd (compRingHom (-X : ℚ[X])) hdiv
  change reflectPolynomial P ∣ reflectPolynomial F at hmapped
  rwa [hfixed] at hmapped

/-- Every odd coefficient of a reflection-fixed polynomial vanishes. -/
theorem coeff_odd_eq_zero_of_reflectPolynomial_eq
    {F : ℚ[X]} (hfixed : reflectPolynomial F = F) (k : ℕ) :
    F.coeff (2 * k + 1) = 0 := by
  have hcoeff := congrArg (fun G : ℚ[X] => G.coeff (2 * k + 1)) hfixed
  rw [reflectPolynomial_coeff] at hcoeff
  have hpow : (-1 : ℚ) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hpow] at hcoeff
  linarith

/-- Every exponent-doubled polynomial is fixed by reflection. -/
@[simp] theorem reflectPolynomial_expand_two (F : ℚ[X]) :
    reflectPolynomial (expand ℚ 2 F) = expand ℚ 2 F := by
  apply Polynomial.ext
  intro n
  rw [reflectPolynomial_coeff]
  by_cases hdiv : 2 ∣ n
  · obtain ⟨k, rfl⟩ := hdiv
    simp [pow_mul]
  · rw [coeff_expand (R := ℚ) (p := 2) (by norm_num) F n, if_neg hdiv]
    simp

/--
A polynomial fixed by `X ↦ -X` is exactly recovered from its even
coefficients: `F = G(X^2)` with `G = contract 2 F`.
-/
theorem expand_contract_two_of_reflectPolynomial_eq
    {F : ℚ[X]} (hfixed : reflectPolynomial F = F) :
    expand ℚ 2 (contract 2 F) = F := by
  apply Polynomial.ext
  intro n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · calc
      (expand ℚ 2 (contract 2 F)).coeff (2 * k) =
          (contract 2 F).coeff k := by
            simpa using
              (coeff_expand_mul' (R := ℚ) (p := 2) (by norm_num)
                (contract 2 F) k)
      _ = F.coeff (k * 2) := by
            exact coeff_contract (R := ℚ) (p := 2) (by norm_num) F k
      _ = F.coeff (2 * k) := by rw [mul_comm]
  · have hnot : ¬2 ∣ 2 * k + 1 := Nat.two_not_dvd_two_mul_add_one k
    calc
      (expand ℚ 2 (contract 2 F)).coeff (2 * k + 1) = 0 := by
        rw [coeff_expand (R := ℚ) (p := 2) (by norm_num)
          (contract 2 F) (2 * k + 1), if_neg hnot]
      _ = F.coeff (2 * k + 1) :=
        (coeff_odd_eq_zero_of_reflectPolynomial_eq hfixed k).symm

/-- The product of a polynomial with its reflection is reflection-fixed. -/
theorem reflectPolynomial_mul_self_reflect (P : ℚ[X]) :
    reflectPolynomial (P * reflectPolynomial P) = P * reflectPolynomial P := by
  simp [mul_comm]

/-- The symmetric product therefore descends canonically to a polynomial in `X^2`. -/
theorem symmetric_product_eq_expand_contract (P : ℚ[X]) :
    expand ℚ 2 (contract 2 (P * reflectPolynomial P)) =
      P * reflectPolynomial P :=
  expand_contract_two_of_reflectPolynomial_eq
    (reflectPolynomial_mul_self_reflect P)

/-- The exact even Sharipov polynomial is fixed by reflection. -/
@[simp] theorem reflectPolynomial_normalizedEvenPolynomial (s : ℚ) :
    reflectPolynomial (normalizedEvenPolynomial s) = normalizedEvenPolynomial s := by
  simpa [normalizedEvenPolynomial, expand_eq_comp_X_pow] using
    reflectPolynomial_expand_two (normalizedQuintic s)

end

end Cuboid2
