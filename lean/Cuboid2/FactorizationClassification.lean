import Cuboid2.Factorization

/-!
# Elementary factorization classification

This file closes the purely degree-theoretic part of the factorization
classification.  A reducible monic quintic over a field has a monic divisor
of degree one or two.  Degree one gives a rational root; degree two leaves a
monic cubic quotient.  No composition theorem or external certificate is
used here.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/--
A reducible monic quintic over `ℚ` has either a rational root or an exact
monic `2+3` factorization.
-/
theorem monic_quintic_reducible_cases
    {P : ℚ[X]}
    (hmonic : P.Monic)
    (hdeg : P.natDegree = 5)
    (hred : ¬ Irreducible P) :
    (∃ r : ℚ, IsRoot P r) ∨
      ∃ A B : ℚ[X],
        A.Monic ∧ A.natDegree = 2 ∧
        B.Monic ∧ B.natDegree = 3 ∧
        P = A * B := by
  classical
  have hPne : P ≠ 1 := by
    intro hP
    have h := hdeg
    rw [hP, natDegree_one] at h
    omega
  have hfail :
      ¬ ∀ A : ℚ[X], A.Monic →
        A.natDegree ∈ Finset.Ioc 0 (P.natDegree / 2) → ¬ A ∣ P := by
    intro hcriterion
    exact hred ((hmonic.irreducible_iff_lt_natDegree_lt hPne).2 hcriterion)
  push_neg at hfail
  obtain ⟨A, hAmonic, hArange, hAdvd⟩ := hfail
  have hArange' : 0 < A.natDegree ∧ A.natDegree ≤ 2 := by
    simpa [Finset.mem_Ioc, hdeg] using hArange
  have hAcases : A.natDegree = 1 ∨ A.natDegree = 2 := by
    omega
  rcases hAcases with hAdeg | hAdeg
  · left
    let c : ℚ := A.coeff 0
    have hAeq : A = X + C c := by
      dsimp [c]
      exact hAmonic.eq_X_add_C hAdeg
    refine ⟨-c, ?_⟩
    rw [← dvd_iff_isRoot]
    have hdiv : X + C c ∣ P := by
      simpa [hAeq] using hAdvd
    simpa [sub_eq_add_neg] using hdiv
  · right
    obtain ⟨B, hPB⟩ := hAdvd
    have hABmonic : (A * B).Monic := by
      rw [← hPB]
      exact hmonic
    have hBmonic : B.Monic :=
      hAmonic.of_mul_monic_left hABmonic
    have hBdeg : B.natDegree = 3 := by
      have hmul := hAmonic.natDegree_mul hBmonic
      rw [← hPB, hdeg, hAdeg] at hmul
      omega
    exact ⟨A, B, hAmonic, hAdeg, hBmonic, hBdeg, hPB⟩

/-- The reducible normalized quintic contributes exactly the `1+4` or `2+3` branch. -/
theorem normalizedQuintic_reducible_cases
    {s : ℚ} (hred : ¬ Irreducible (normalizedQuintic s)) :
    LinearQuarticCase s ∨ QuadraticCubicCase s := by
  have hdeg : (normalizedQuintic s).natDegree = 5 :=
    natDegree_eq_of_degree_eq_some (normalizedQuintic_degree s)
  simpa [LinearQuarticCase, QuadraticCubicCase] using
    (monic_quintic_reducible_cases
      (hmonic := normalizedQuintic_monic s)
      (hdeg := hdeg)
      (hred := hred))

end

end Cuboid2
