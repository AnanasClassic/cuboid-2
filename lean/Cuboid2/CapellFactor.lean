import Cuboid2.CapellDegree

/-!
# Irreducible factors and the reflection orbit

This file handles the UFD part of the specialized Capell argument.  It
normalizes an irreducible factor, constructs its monic reflected partner, and
rules out a one-element reflection orbit for a divisor of an exponent-doubled
irreducible quintic.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- The reflected polynomial rescaled to have the same monic normalization. -/
def monicReflection (R : ℚ[X]) : ℚ[X] :=
  C ((-1 : ℚ) ^ R.natDegree) * reflectPolynomial R

/-- Leading coefficient under `X ↦ -X`. -/
theorem reflectPolynomial_leadingCoeff (R : ℚ[X]) :
    (reflectPolynomial R).leadingCoeff =
      R.leadingCoeff * (-1 : ℚ) ^ R.natDegree := by
  simp only [leadingCoeff, reflectPolynomial_natDegree, reflectPolynomial_coeff]

/-- The monic reflection differs from the raw reflection only by a unit. -/
theorem monicReflection_associated_reflectPolynomial (R : ℚ[X]) :
    Associated (monicReflection R) (reflectPolynomial R) := by
  unfold monicReflection
  exact associated_unit_mul_left _ _
    (isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num : (-1 : ℚ) ≠ 0))))

/-- Monicity is preserved by monic reflection. -/
theorem monicReflection_monic {R : ℚ[X]} (hR : R.Monic) :
    (monicReflection R).Monic := by
  unfold monicReflection
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [reflectPolynomial_leadingCoeff, hR.leadingCoeff, one_mul, ← pow_add]
  have hsum : R.natDegree + R.natDegree = 2 * R.natDegree := by omega
  rw [hsum, pow_mul]
  norm_num

/-- Monic reflection preserves and reflects irreducibility. -/
theorem irreducible_monicReflection_iff (R : ℚ[X]) :
    Irreducible (monicReflection R) ↔ Irreducible R :=
  (monicReflection_associated_reflectPolynomial R).irreducible_iff.trans
    (irreducible_reflectPolynomial_iff R)

/-- The monic reflected partner also divides a reflection-fixed polynomial. -/
theorem monicReflection_dvd_of_dvd_fixed
    {R F : ℚ[X]} (hfixed : reflectPolynomial F = F) (hdiv : R ∣ F) :
    monicReflection R ∣ F := by
  have hreflect : reflectPolynomial R ∣ F :=
    reflectPolynomial_dvd_of_dvd_fixed hfixed hdiv
  exact (monicReflection_associated_reflectPolynomial R).dvd_iff_dvd_left.mpr hreflect

/-- If a monic polynomial is associated to its reflection, it equals its monic reflection. -/
theorem eq_monicReflection_of_monic_of_associated_reflect
    {R : ℚ[X]} (hR : R.Monic)
    (hassoc : Associated R (reflectPolynomial R)) :
    R = monicReflection R := by
  apply eq_of_monic_of_associated hR (monicReflection_monic hR)
  exact hassoc.trans (monicReflection_associated_reflectPolynomial R).symm

/-- In even degree, self-association means literal reflection invariance. -/
theorem reflectPolynomial_eq_self_of_monic_associated_even
    {R : ℚ[X]} (hR : R.Monic)
    (hassoc : Associated R (reflectPolynomial R))
    {k : ℕ} (hdeg : R.natDegree = 2 * k) :
    reflectPolynomial R = R := by
  have heq := eq_monicReflection_of_monic_of_associated_reflect hR hassoc
  unfold monicReflection at heq
  have hpow : (-1 : ℚ) ^ R.natDegree = 1 := by
    rw [hdeg, pow_mul]
    norm_num
  rw [hpow] at heq
  simp at heq
  exact heq.symm

/-- In odd degree, self-association means anti-invariance under reflection. -/
theorem reflectPolynomial_eq_neg_of_monic_associated_odd
    {R : ℚ[X]} (hR : R.Monic)
    (hassoc : Associated R (reflectPolynomial R))
    {k : ℕ} (hdeg : R.natDegree = 2 * k + 1) :
    reflectPolynomial R = -R := by
  have heq := eq_monicReflection_of_monic_of_associated_reflect hR hassoc
  unfold monicReflection at heq
  have hpow : (-1 : ℚ) ^ R.natDegree = -1 := by
    rw [hdeg, pow_add, pow_mul]
    norm_num
  rw [hpow] at heq
  simp at heq
  have hneg := congrArg Neg.neg heq
  simpa using hneg.symm

/-- A reducible monic polynomial has a normalized irreducible divisor of degree at most half. -/
theorem exists_monic_irreducible_factor_le_half
    {F : ℚ[X]} (hFmonic : F.Monic) (hFneOne : F ≠ 1)
    (hFred : ¬ Irreducible F) :
    ∃ R : ℚ[X],
      R.Monic ∧ Irreducible R ∧ R ∣ F ∧
      R.natDegree ≤ F.natDegree / 2 := by
  classical
  have hfail :
      ¬ ∀ A : ℚ[X], A.Monic →
        A.natDegree ∈ Finset.Ioc 0 (F.natDegree / 2) → ¬ A ∣ F := by
    intro hcriterion
    exact hFred ((hFmonic.irreducible_iff_lt_natDegree_lt hFneOne).2 hcriterion)
  push_neg at hfail
  obtain ⟨A, hAmonic, hArange, hAdivF⟩ := hfail
  have hApositive : 0 < A.natDegree := (Finset.mem_Ioc.mp hArange).1
  have hAnotUnit : ¬ IsUnit A := by
    intro hunit
    have hdegree : A.degree = 0 := degree_eq_zero_of_isUnit hunit
    have hnat : A.natDegree = 0 := natDegree_eq_of_degree_eq_some hdegree
    omega
  obtain ⟨R₀, hR₀irreducible, hR₀divA⟩ :=
    WfDvdMonoid.exists_irreducible_factor hAnotUnit hAmonic.ne_zero
  let R : ℚ[X] := normalize R₀
  have hRdivA : R ∣ A := by
    dsimp [R]
    exact (normalize_dvd_iff).2 hR₀divA
  refine ⟨R, ?_, ?_, hRdivA.trans hAdivF, ?_⟩
  · exact monic_normalize hR₀irreducible.ne_zero
  · exact (normalize_associated R₀).irreducible_iff.mpr hR₀irreducible
  · exact (natDegree_le_of_dvd hRdivA hAmonic.ne_zero).trans
      (Finset.mem_Ioc.mp hArange).2

/-- Distinct irreducible reflection partners occur together in a divisor. -/
theorem mul_reflectPolynomial_dvd_of_not_associated
    {R F : ℚ[X]}
    (hR : Irreducible R)
    (hRdivF : R ∣ F)
    (hreflectDivF : reflectPolynomial R ∣ F)
    (hnotAssociated : ¬ Associated R (reflectPolynomial R)) :
    R * reflectPolynomial R ∣ F := by
  obtain ⟨Q, hF⟩ := hRdivF
  rw [hF] at hreflectDivF
  have hreflectIrreducible : Irreducible (reflectPolynomial R) :=
    (irreducible_reflectPolynomial_iff R).2 hR
  have hreflectPrime : Prime (reflectPolynomial R) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hreflectIrreducible
  rcases hreflectPrime.dvd_or_dvd hreflectDivF with hreflectDivR | hreflectDivQ
  · have hassociated : Associated R (reflectPolynomial R) :=
      (Irreducible.associated_of_dvd hreflectIrreducible hR hreflectDivR).symm
    exact (hnotAssociated hassociated).elim
  · obtain ⟨Q', hQ⟩ := hreflectDivQ
    refine ⟨Q', ?_⟩
    calc
      F = R * Q := hF
      _ = R * (reflectPolynomial R * Q') := by rw [hQ]
      _ = (R * reflectPolynomial R) * Q' := by rw [mul_assoc]

/--
An irreducible monic divisor of an exponent-doubled irreducible quintic cannot
form a one-element orbit under reflection.
-/
theorem not_associated_reflect_of_irreducible_quintic_factor
    {P R : ℚ[X]}
    (hP : Irreducible P) (hPdegree : P.natDegree = 5)
    (hRmonic : R.Monic) (hR : Irreducible R)
    (hRdiv : R ∣ expand ℚ 2 P)
    (hRdegreeLe : R.natDegree ≤ 5) :
    ¬ Associated R (reflectPolynomial R) := by
  intro hassociated
  obtain ⟨k, heven | hodd⟩ := Nat.even_or_odd' R.natDegree
  · have hfixed : reflectPolynomial R = R :=
      reflectPolynomial_eq_self_of_monic_associated_even hRmonic hassociated heven
    let S : ℚ[X] := contract 2 R
    have hexpand : expand ℚ 2 S = R := by
      exact expand_contract_two_of_reflectPolynomial_eq hfixed
    have hSdivP : S ∣ P := by
      apply dvd_of_expand_two_dvd_expand_two
      rw [hexpand]
      exact hRdiv
    have hdegree := congrArg Polynomial.natDegree hexpand
    rw [natDegree_expand] at hdegree
    have hRpositive : 0 < R.natDegree :=
      natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hR)
    have hSpositive : 0 < S.natDegree := by omega
    have hSnotUnit : ¬ IsUnit S := by
      intro hunit
      have hSdegree : S.degree = 0 := degree_eq_zero_of_isUnit hunit
      have hSnat : S.natDegree = 0 := natDegree_eq_of_degree_eq_some hSdegree
      omega
    have hPassocS : Associated P S :=
      ((hP.dvd_iff).mp hSdivP).resolve_left hSnotUnit
    have hSnonzero : S ≠ 0 := by
      intro hzero
      rw [hzero, natDegree_zero] at hSpositive
      exact (Nat.lt_asymm hSpositive hSpositive).elim
    have hSdegreeEq : P.natDegree = S.natDegree :=
      natDegree_eq_of_associated hPassocS hP.ne_zero hSnonzero
    omega
  · have hanti : reflectPolynomial R = -R :=
      reflectPolynomial_eq_neg_of_monic_associated_odd hRmonic hassociated hodd
    have hcoeff := congrArg (fun G : ℚ[X] => G.coeff 0) hanti
    rw [reflectPolynomial_coeff, coeff_neg] at hcoeff
    norm_num at hcoeff
    have hRconstant : R.coeff 0 = 0 := by linarith
    have hXdivR : X ∣ R := X_dvd_iff.mpr hRconstant
    have hXdivExpand : X ∣ expand ℚ 2 P := hXdivR.trans hRdiv
    have hExpandConstant : (expand ℚ 2 P).coeff 0 = 0 :=
      X_dvd_iff.mp hXdivExpand
    have hPconstant : P.coeff 0 = 0 := by
      rw [coeff_expand (R := ℚ) (p := 2) (by norm_num) P 0,
        if_pos (dvd_zero 2)] at hExpandConstant
      simpa using hExpandConstant
    have hXdivP : X ∣ P := X_dvd_iff.mpr hPconstant
    have hXassociatedP : Associated X P :=
      Irreducible.associated_of_dvd irreducible_X hP hXdivP
    have hdegreeEq : (X : ℚ[X]).natDegree = P.natDegree :=
      natDegree_eq_of_associated hXassociatedP X_ne_zero hP.ne_zero
    simp [hPdegree] at hdegreeEq

end

end Cuboid2
