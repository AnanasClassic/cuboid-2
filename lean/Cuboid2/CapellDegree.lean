import Cuboid2.Capell

/-!
# Degree and divisibility descent for the specialized Capell argument

This file turns the reflection algebra into the exact divisibility statement
needed later: if a symmetric product `R(X)R(-X)` divides `P(X^2)`, then its
contracted polynomial divides `P`.  For irreducible `R`, contraction preserves
the degree of `R` and produces a nonunit.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- Reflection vanishes exactly when the original polynomial vanishes. -/
@[simp] theorem reflectPolynomial_eq_zero_iff (P : ℚ[X]) :
    reflectPolynomial P = 0 ↔ P = 0 := by
  constructor
  · intro h
    have hreflected := congrArg reflectPolynomial h
    simpa using hreflected
  · rintro rfl
    simp

/-- Reflection preserves natural degree. -/
@[simp] theorem reflectPolynomial_natDegree (P : ℚ[X]) :
    (reflectPolynomial P).natDegree = P.natDegree := by
  by_cases hP : P = 0
  · simp [hP]
  unfold reflectPolynomial
  rw [natDegree_comp_eq_of_mul_ne_zero]
  · simp
  · have hleading : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
    simp [hleading]

/-- The symmetric product has twice the degree of its nonzero factor. -/
theorem symmetric_product_natDegree
    {R : ℚ[X]} (hR : R ≠ 0) :
    (R * reflectPolynomial R).natDegree = 2 * R.natDegree := by
  have hreflect : reflectPolynomial R ≠ 0 := by
    simpa using hR
  rw [natDegree_mul hR hreflect, reflectPolynomial_natDegree]
  omega

/--
Exponent doubling reflects divisibility: if `A(X^2)` divides `P(X^2)`, then
`A` divides `P`.  The quotient need not itself be even; `contract_mul_expand`
extracts exactly the coefficients relevant to the divisible exponents.
-/
theorem dvd_of_expand_two_dvd_expand_two
    {A P : ℚ[X]} (hdiv : expand ℚ 2 A ∣ expand ℚ 2 P) :
    A ∣ P := by
  obtain ⟨Q, hQ⟩ := hdiv
  refine ⟨contract 2 Q, ?_⟩
  have hQ' : expand ℚ 2 P = Q * expand ℚ 2 A := by
    simpa [mul_comm] using hQ
  calc
    P = contract 2 (expand ℚ 2 P) := by
      symm
      exact contract_expand (R := ℚ) (p := 2) (by norm_num)
    _ = contract 2 (Q * expand ℚ 2 A) := by rw [hQ']
    _ = contract 2 Q * A := by
      exact contract_mul_expand (R := ℚ) (p := 2) (by norm_num) Q A
    _ = A * contract 2 Q := by rw [mul_comm]

/-- A symmetric divisor of `P(X^2)` contracts to a divisor of `P`. -/
theorem contract_symmetric_product_dvd
    {R P : ℚ[X]}
    (hdiv : R * reflectPolynomial R ∣ expand ℚ 2 P) :
    contract 2 (R * reflectPolynomial R) ∣ P := by
  apply dvd_of_expand_two_dvd_expand_two
  rw [symmetric_product_eq_expand_contract R]
  exact hdiv

/-- Contracting a nonzero symmetric product recovers the degree of one factor. -/
theorem contract_symmetric_product_natDegree
    {R : ℚ[X]} (hR : R ≠ 0) :
    (contract 2 (R * reflectPolynomial R)).natDegree = R.natDegree := by
  have hdegree :=
    congrArg Polynomial.natDegree (symmetric_product_eq_expand_contract R)
  rw [natDegree_expand, symmetric_product_natDegree hR] at hdegree
  omega

/-- For irreducible `R`, the contracted symmetric product is not a unit. -/
theorem contract_symmetric_product_not_isUnit
    {R : ℚ[X]} (hR : Irreducible R) :
    ¬ IsUnit (contract 2 (R * reflectPolynomial R)) := by
  intro hunit
  have hdegree :
      (contract 2 (R * reflectPolynomial R)).degree = 0 :=
    degree_eq_zero_of_isUnit hunit
  have hnat :
      (contract 2 (R * reflectPolynomial R)).natDegree = 0 :=
    natDegree_eq_of_degree_eq_some hdegree
  rw [contract_symmetric_product_natDegree hR.ne_zero] at hnat
  have hpositive : 0 < R.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hR)
  omega

/-- Associated nonzero polynomials over `ℚ` have the same natural degree. -/
theorem natDegree_eq_of_associated
    {P Q : ℚ[X]} (hassoc : Associated P Q) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    P.natDegree = Q.natDegree := by
  apply le_antisymm
  · exact natDegree_le_of_dvd hassoc.dvd hQ
  · exact natDegree_le_of_dvd hassoc.dvd' hP

/--
If `P` and `R` are irreducible and the symmetric product of `R` divides
`P(X^2)`, then `R` has exactly the degree of `P`.
-/
theorem natDegree_eq_of_symmetric_product_dvd_expand_irreducible
    {R P : ℚ[X]}
    (hR : Irreducible R)
    (hP : Irreducible P)
    (hdiv : R * reflectPolynomial R ∣ expand ℚ 2 P) :
    R.natDegree = P.natDegree := by
  let S : ℚ[X] := contract 2 (R * reflectPolynomial R)
  have hSdiv : S ∣ P := by
    exact contract_symmetric_product_dvd hdiv
  have hSnotUnit : ¬ IsUnit S := by
    exact contract_symmetric_product_not_isUnit hR
  have hPassocS : Associated P S :=
    ((hP.dvd_iff).mp hSdiv).resolve_left hSnotUnit
  have hRreflectNonzero : R * reflectPolynomial R ≠ 0 := by
    apply mul_ne_zero hR.ne_zero
    simpa using hR.ne_zero
  have hSnonzero : S ≠ 0 := by
    intro hSzero
    have hexpand := symmetric_product_eq_expand_contract R
    change expand ℚ 2 S = R * reflectPolynomial R at hexpand
    rw [hSzero, map_zero] at hexpand
    exact hRreflectNonzero hexpand.symm
  have hdegrees : P.natDegree = S.natDegree :=
    natDegree_eq_of_associated hPassocS hP.ne_zero hSnonzero
  have hcontract : S.natDegree = R.natDegree := by
    exact contract_symmetric_product_natDegree hR.ne_zero
  omega

end

end Cuboid2
