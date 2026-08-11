import Cuboid2.Polynomial

/-!
# Exact scaling between `Q_{p,q}` and `P_s(u^2)`

The paper's substitution `u=t/q^2` is represented by
`Polynomial.scaleRoots`.  This file proves the exact polynomial identity and
shows that a nonzero scaling preserves and reflects irreducibility.  No
external computation is used.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- The even degree-ten composition `P_s(u^2)`. -/
def normalizedEvenPolynomial (s : ℚ) : ℚ[X] :=
  (normalizedQuintic s).comp (X ^ 2)

/-- `P_s(u^2)` is monic. -/
theorem normalizedEvenPolynomial_monic (s : ℚ) :
    (normalizedEvenPolynomial s).Monic := by
  unfold normalizedEvenPolynomial
  exact (normalizedQuintic_monic s).comp (monic_X.pow 2) (by simp)

/-- `P_s(u^2)` has degree ten. -/
theorem normalizedEvenPolynomial_natDegree (s : ℚ) :
    (normalizedEvenPolynomial s).natDegree = 10 := by
  unfold normalizedEvenPolynomial
  rw [natDegree_comp_eq_of_mul_ne_zero]
  · rw [natDegree_eq_of_degree_eq_some (normalizedQuintic_degree s)]
    norm_num
  · rw [(normalizedQuintic_monic s).leadingCoeff]
    simp

/-- Scaling roots does not change whether a polynomial over a field is a unit. -/
theorem isUnit_scaleRoots_iff
    {K : Type*} [Field K] (P : K[X]) (r : K) :
    IsUnit (P.scaleRoots r) ↔ IsUnit P := by
  rw [Polynomial.isUnit_iff_degree_eq_zero,
    Polynomial.isUnit_iff_degree_eq_zero, degree_scaleRoots]

/-- A nonzero root scaling preserves and reflects irreducibility. -/
theorem irreducible_scaleRoots_iff
    {K : Type*} [Field K] (P : K[X]) {r : K} (hr : r ≠ 0) :
    Irreducible (P.scaleRoots r) ↔ Irreducible P := by
  constructor
  · intro hscaled
    refine ⟨?_, ?_⟩
    · intro hPunit
      exact hscaled.not_isUnit ((isUnit_scaleRoots_iff P r).2 hPunit)
    · intro A B hP
      have hfactor :
          P.scaleRoots r = A.scaleRoots r * B.scaleRoots r := by
        rw [hP, mul_scaleRoots_of_noZeroDivisors]
      rcases hscaled.isUnit_or_isUnit hfactor with hA | hB
      · exact Or.inl ((isUnit_scaleRoots_iff A r).1 hA)
      · exact Or.inr ((isUnit_scaleRoots_iff B r).1 hB)
  · intro hP
    refine ⟨?_, ?_⟩
    · intro hscaledUnit
      exact hP.not_isUnit ((isUnit_scaleRoots_iff P r).1 hscaledUnit)
    · intro A B hfactor
      have hfactor' :
          P = A.scaleRoots r⁻¹ * B.scaleRoots r⁻¹ := by
        have h := congrArg (fun Q : K[X] => Q.scaleRoots r⁻¹) hfactor
        rw [← scaleRoots_mul, mul_inv_cancel₀ hr, scaleRoots_one,
          mul_scaleRoots_of_noZeroDivisors] at h
        exact h
      rcases hP.isUnit_or_isUnit hfactor' with hA | hB
      · exact Or.inl ((isUnit_scaleRoots_iff A r⁻¹).1 hA)
      · exact Or.inr ((isUnit_scaleRoots_iff B r⁻¹).1 hB)

/-- Pointwise evaluation of the scaled even normalized polynomial. -/
theorem eval_normalizedEven_scaleRoots
    {p q : ℕ} (hq : 0 < q) (t : ℚ) :
    eval t
        ((normalizedEvenPolynomial (sharipovParameter p q)).scaleRoots
          ((q : ℚ) ^ 2)) =
      (q : ℚ) ^ 20 *
        eval (t ^ 2 / (q : ℚ) ^ 4)
          (normalizedQuintic (sharipovParameter p q)) := by
  have hq0 : (q : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  calc
    eval t
        ((normalizedEvenPolynomial (sharipovParameter p q)).scaleRoots
          ((q : ℚ) ^ 2)) =
        eval (((q : ℚ) ^ 2) * (t / (q : ℚ) ^ 2))
          ((normalizedEvenPolynomial (sharipovParameter p q)).scaleRoots
            ((q : ℚ) ^ 2)) := by
      rw [show ((q : ℚ) ^ 2) * (t / (q : ℚ) ^ 2) = t by
        field_simp [hq0]]
    _ = ((q : ℚ) ^ 2) ^
          (normalizedEvenPolynomial (sharipovParameter p q)).natDegree *
        eval (t / (q : ℚ) ^ 2)
          (normalizedEvenPolynomial (sharipovParameter p q)) := by
      exact scaleRoots_eval_mul
        (normalizedEvenPolynomial (sharipovParameter p q))
        (t / (q : ℚ) ^ 2) ((q : ℚ) ^ 2)
    _ = (q : ℚ) ^ 20 *
        eval (t ^ 2 / (q : ℚ) ^ 4)
          (normalizedQuintic (sharipovParameter p q)) := by
      rw [normalizedEvenPolynomial_natDegree]
      simp only [normalizedEvenPolynomial, eval_comp, eval_pow, eval_X]
      rw [show (((q : ℚ) ^ 2) ^ 10) = (q : ℚ) ^ 20 by ring]
      rw [show (t / (q : ℚ) ^ 2) ^ 2 = t ^ 2 / (q : ℚ) ^ 4 by
        field_simp [hq0]
        ring]

/-- Exact polynomial, not merely pointwise, form of the paper's scaling identity. -/
theorem sharipovPolynomialQ_eq_scaleRoots
    {p q : ℕ} (hq : 0 < q) :
    sharipovPolynomialQ p q =
      (normalizedEvenPolynomial (sharipovParameter p q)).scaleRoots
        ((q : ℚ) ^ 2) := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hset :
      {t : ℚ |
        eval t (sharipovPolynomialQ p q) =
          eval t
            ((normalizedEvenPolynomial (sharipovParameter p q)).scaleRoots
              ((q : ℚ) ^ 2))} = Set.univ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rw [eval_sharipovPolynomialQ_scaling hq t,
      eval_normalizedEven_scaleRoots hq t]
  rw [hset]
  exact Set.infinite_univ

/-- Irreducibility of `Q_{p,q}` is exactly irreducibility of `P_s(u^2)`. -/
theorem sharipovPolynomialQ_irreducible_iff_normalizedEven
    {p q : ℕ} (hq : 0 < q) :
    Irreducible (sharipovPolynomialQ p q) ↔
      Irreducible (normalizedEvenPolynomial (sharipovParameter p q)) := by
  have hq0 : (q : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  rw [sharipovPolynomialQ_eq_scaleRoots hq]
  exact irreducible_scaleRoots_iff
    (normalizedEvenPolynomial (sharipovParameter p q)) (pow_ne_zero 2 hq0)

end

end Cuboid2
