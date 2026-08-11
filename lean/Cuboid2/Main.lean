import Cuboid2.FactorizationClassification
import Cuboid2.CapellDegree
import Cuboid2.DPlus.Basic

/-!
# Final theorem assembly

The theorem below already has the intended public signature and the intended
contradiction structure.  Four narrowly named research gaps remain.  They are
tracked in `lean/FORMALIZATION_STATUS.md`; none is represented by a custom
axiom declaration.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/--
The remaining specialized Capell bridge.  Once the normalized quintic is
irreducible, reducibility of its composition with `u^2` must be the symmetric
irreducible `5+5` mechanism.
-/
theorem normalizedEven_capell_reduction
    {s : ℚ} :
    ¬ Irreducible (normalizedEvenPolynomial s) →
      ¬ Irreducible (normalizedQuintic s) ∨ SymmetricFiveFiveCase s := by
  sorry

/--
Reducibility of the exact degree-ten polynomial either comes from
reducibility of the normalized quintic or from the symmetric `5+5`
composition mechanism.  The weighted variable scaling is kernel-checked in
`Scaling.lean`; only the specialized Capell theorem above remains open.
-/
theorem sharipov_composition_reduction
    {p q : ℕ} (hq : 0 < q) :
    ¬ Irreducible (sharipovPolynomialQ p q) →
      ¬ Irreducible (normalizedQuintic (sharipovParameter p q)) ∨
      SymmetricFiveFiveCase (sharipovParameter p q) := by
  intro hQ
  have hEven :
      ¬ Irreducible (normalizedEvenPolynomial (sharipovParameter p q)) := by
    intro hEvenIrr
    exact hQ
      ((sharipovPolynomialQ_irreducible_iff_normalizedEven hq).2 hEvenIrr)
  exact normalizedEven_capell_reduction hEven

/--
Specialized factorization classification for the exact Sharipov polynomial.
The scaling and reducible-quintic degree split are kernel-checked; the only
remaining input in this branch is `normalizedEven_capell_reduction`.
-/
theorem sharipov_factorization_classification
    {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    (hcop : Nat.Coprime p q) (hne : p ≠ q) :
    ¬ Irreducible (sharipovPolynomialQ p q) →
      LinearQuarticCase (sharipovParameter p q) ∨
      QuadraticCubicCase (sharipovParameter p q) ∨
      SymmetricFiveFiveCase (sharipovParameter p q) := by
  intro hred
  rcases sharipov_composition_reduction hq hred with hnormalized | hsymmetric
  · rcases normalizedQuintic_reducible_cases hnormalized with hlinear | hquadratic
    · exact Or.inl hlinear
    · exact Or.inr (Or.inl hquadratic)
  · exact Or.inr (Or.inr hsymmetric)

/-- The exact linear-factor completion from `research/linear_factor_completion/`. -/
theorem linear_quartic_impossible
    {s : ℚ} (hs : 0 < s) (hs1 : s ≠ 1) :
    ¬ LinearQuarticCase s := by
  sorry

/-- The signed-square/common-character/direct-D+ completion of the `2+3` case. -/
theorem quadratic_cubic_impossible
    {s : ℚ} (hs : 0 < s) (hs1 : s ≠ 1) :
    ¬ QuadraticCubicCase s := by
  sorry

/-- The pinned exact seven-obligation root-exclusion certificate for `5+5`. -/
theorem symmetric_five_five_impossible
    {s : ℚ} (hs : 0 < s) (hs1 : s ≠ 1) :
    ¬ SymmetricFiveFiveCase s := by
  sorry

/-- Rational irreducibility, assembled by exhausting the three cases. -/
theorem sharipovPolynomialQ_irreducible
    {p q : ℕ}
    (hp : 0 < p)
    (hq : 0 < q)
    (hcop : Nat.Coprime p q)
    (hne : p ≠ q) :
    Irreducible (sharipovPolynomialQ p q) := by
  apply irreducible_of_factorization_cases
  · exact sharipov_factorization_classification hp hq hcop hne
  · exact linear_quartic_impossible
      (sharipovParameter_pos hp hq)
      (sharipovParameter_ne_one hp hq hne)
  · exact quadratic_cubic_impossible
      (sharipovParameter_pos hp hq)
      (sharipovParameter_ne_one hp hq hne)
  · exact symmetric_five_five_impossible
      (sharipovParameter_pos hp hq)
      (sharipovParameter_ne_one hp hq hne)

/-- Sharipov's second cuboid conjecture over the exact integer polynomial. -/
theorem sharipov_second_cuboid_conjecture
    {p q : ℕ}
    (hp : 0 < p)
    (hq : 0 < q)
    (hcop : Nat.Coprime p q)
    (hne : p ≠ q) :
    Irreducible (sharipovPolynomial p q) := by
  exact (sharipovPolynomial_irreducible_iff_rational p q).2
    (sharipovPolynomialQ_irreducible hp hq hcop hne)

/-- Explicit contradiction form: neither factor in a product decomposition can be nonunit. -/
theorem no_nontrivial_factorization
    {p q : ℕ}
    (hp : 0 < p)
    (hq : 0 < q)
    (hcop : Nat.Coprime p q)
    (hne : p ≠ q) :
    ¬ HasNontrivialFactorization (sharipovPolynomial p q) := by
  intro hfac
  rcases hfac with ⟨A, B, hAB, hA, hB⟩
  rcases (sharipov_second_cuboid_conjecture hp hq hcop hne).isUnit_or_isUnit hAB with
    hunit | hunit
  · exact hA hunit
  · exact hB hunit

end

end Cuboid2
