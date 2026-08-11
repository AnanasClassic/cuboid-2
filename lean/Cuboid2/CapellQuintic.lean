import Cuboid2.CapellFactor

/-!
# Specialized Capell reduction for an irreducible quintic

This file completes the algebraic composition step needed by the final
factorization classification.  No general Capell theorem is imported: the
proof uses only unique factorization in `ℚ[X]`, the involution `X ↦ -X`, and
the fact that the original polynomial has odd prime degree five.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- The even composition is literally exponent doubling. -/
theorem normalizedEvenPolynomial_eq_expand (s : ℚ) :
    normalizedEvenPolynomial s = expand ℚ 2 (normalizedQuintic s) := by
  rfl

/-- For a monic degree-five polynomial, `-R(-X)` is again monic. -/
theorem neg_reflectPolynomial_monic_of_degree_five
    {R : ℚ[X]} (hR : R.Monic) (hdegree : R.natDegree = 5) :
    (-reflectPolynomial R).Monic := by
  unfold Monic
  rw [leadingCoeff_neg, reflectPolynomial_leadingCoeff,
    hR.leadingCoeff, one_mul, hdegree]
  norm_num

/--
Specialized Capell reduction: reducibility of `P(X²)` for a quintic `P`
either comes from reducibility of `P`, or from a symmetric irreducible
factorization into two degree-five factors.
-/
theorem normalizedEven_capell_reduction
    {s : ℚ} :
    ¬ Irreducible (normalizedEvenPolynomial s) →
      ¬ Irreducible (normalizedQuintic s) ∨ SymmetricFiveFiveCase s := by
  intro hEvenReducible
  by_cases hP : Irreducible (normalizedQuintic s)
  · right
    have hPdegree : (normalizedQuintic s).natDegree = 5 :=
      natDegree_eq_of_degree_eq_some (normalizedQuintic_degree s)
    have hEvenMonic : (normalizedEvenPolynomial s).Monic :=
      normalizedEvenPolynomial_monic s
    have hEvenDegree : (normalizedEvenPolynomial s).natDegree = 10 :=
      normalizedEvenPolynomial_natDegree s
    have hEvenNeOne : normalizedEvenPolynomial s ≠ 1 := by
      intro hEq
      have hdegreeEq := congrArg Polynomial.natDegree hEq
      rw [hEvenDegree, natDegree_one] at hdegreeEq
      omega
    obtain ⟨R, hRmonic, hRirreducible, hRdivEven, hRhalf⟩ :=
      exists_monic_irreducible_factor_le_half
        hEvenMonic hEvenNeOne hEvenReducible
    have hRdegreeLeFive : R.natDegree ≤ 5 := by
      rw [hEvenDegree] at hRhalf
      norm_num at hRhalf
      exact hRhalf
    have hRdivExpand : R ∣ expand ℚ 2 (normalizedQuintic s) := by
      rw [← normalizedEvenPolynomial_eq_expand s]
      exact hRdivEven
    have hRnotAssociated : ¬ Associated R (reflectPolynomial R) :=
      not_associated_reflect_of_irreducible_quintic_factor
        hP hPdegree hRmonic hRirreducible hRdivExpand hRdegreeLeFive
    have hreflectDivEven : reflectPolynomial R ∣ normalizedEvenPolynomial s :=
      reflectPolynomial_dvd_of_dvd_fixed
        (reflectPolynomial_normalizedEvenPolynomial s) hRdivEven
    have hsymmetricDivEven :
        R * reflectPolynomial R ∣ normalizedEvenPolynomial s :=
      mul_reflectPolynomial_dvd_of_not_associated
        hRirreducible hRdivEven hreflectDivEven hRnotAssociated
    have hsymmetricDivExpand :
        R * reflectPolynomial R ∣ expand ℚ 2 (normalizedQuintic s) := by
      rw [← normalizedEvenPolynomial_eq_expand s]
      exact hsymmetricDivEven
    have hRdegreeEqP : R.natDegree = (normalizedQuintic s).natDegree :=
      natDegree_eq_of_symmetric_product_dvd_expand_irreducible
        hRirreducible hP hsymmetricDivExpand
    have hRdegree : R.natDegree = 5 := hRdegreeEqP.trans hPdegree
    have hnegativeReflectionMonic : (-reflectPolynomial R).Monic :=
      neg_reflectPolynomial_monic_of_degree_five hRmonic hRdegree
    have hpairMonic : (R * (-reflectPolynomial R)).Monic :=
      hRmonic.mul hnegativeReflectionMonic
    have hpairDivEven :
        R * (-reflectPolynomial R) ∣ normalizedEvenPolynomial s := by
      obtain ⟨Q, hQ⟩ := hsymmetricDivEven
      refine ⟨-Q, ?_⟩
      calc
        normalizedEvenPolynomial s = (R * reflectPolynomial R) * Q := hQ
        _ = (R * (-reflectPolynomial R)) * (-Q) := by ring
    have hpairDegree : (R * (-reflectPolynomial R)).natDegree = 10 := by
      rw [hRmonic.natDegree_mul hnegativeReflectionMonic,
        natDegree_neg, reflectPolynomial_natDegree, hRdegree]
      norm_num
    have hfactorization :
        normalizedEvenPolynomial s = R * (-reflectPolynomial R) := by
      apply eq_of_monic_of_dvd_of_natDegree_le
        hpairMonic hEvenMonic hpairDivEven
      rw [hEvenDegree, hpairDegree]
    refine ⟨R, hRmonic, hRdegree, hRirreducible, ?_⟩
    simpa [normalizedEvenPolynomial, reflectPolynomial] using hfactorization
  · exact Or.inl hP

end

end Cuboid2
