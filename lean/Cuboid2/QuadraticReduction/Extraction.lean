import Cuboid2.Factorization
import Cuboid2.QuadraticReduction.CompactModel

/-!
# Extracting the exact quadratic-factor data

This file supplies the coefficient-theoretic bridge from the abstract
`QuadraticCubicCase` used by the factorization classification to the explicit
remainder equations used by the signed-square reduction.

The arithmetic signed-square theorem for an admissible pair `(p,q)` is a
separate valuation statement.  No such statement is assumed here.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- A monic quadratic of natural degree two has the explicit stored form. -/
theorem exists_monicQuadratic_eq
    {A : ℚ[X]} (hAmonic : A.Monic) (hAdeg : A.natDegree = 2) :
    ∃ a b : ℚ, A = monicQuadratic a b := by
  have hA : IsMonicOfDegree A 2 := ⟨hAdeg, hAmonic⟩
  simpa [monicQuadratic] using (isMonicOfDegree_two_iff.mp hA)

/-- Coefficient expansion of a monic cubic. -/
theorem monic_cubic_coefficient_form
    {B : ℚ[X]} (hBmonic : B.Monic) (hBdeg : B.natDegree = 3) :
    B =
      X ^ 3 + C (B.coeff 2) * X ^ 2 +
        C (B.coeff 1) * X + C (B.coeff 0) := by
  have hcoeff3 : B.coeff 3 = 1 := by
    rw [← hBdeg]
    exact hBmonic.coeff_natDegree
  ext n
  by_cases hn : n ≤ 3
  · interval_cases n <;> simp [hcoeff3]
  · have hlt : B.natDegree < n := by omega
    rw [coeff_eq_zero_of_natDegree_lt hlt]
    have hn0 : n ≠ 0 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have h1n : 1 ≠ n := by omega
    simp [coeff_X_pow, coeff_X, coeff_C, hn0, hn2, hn3, h1n]

/--
Every abstract monic `2+3` factorization is the explicit division
factorization used by the remainder equations.
-/
theorem quadraticCubicCase_forced_factorization
    {s : ℚ} (h : QuadraticCubicCase s) :
    ∃ a b : ℚ,
      normalizedQuintic s = monicQuadratic a b * forcedCubic s a b := by
  rcases h with ⟨A, B, hAmonic, hAdeg, _, _, hfactor⟩
  obtain ⟨a, b, hA⟩ := exists_monicQuadratic_eq hAmonic hAdeg
  have hquadMonic : (monicQuadratic a b).Monic := by
    simpa only [hA] using hAmonic
  have hquadDegree : (monicQuadratic a b).natDegree = 2 := by
    simpa only [hA] using hAdeg
  let remainder : ℚ[X] :=
    C (quadraticR1 s a b) * X + C (quadraticR0 s a b)
  have hremainderDegree :
      remainder.degree < (monicQuadratic a b).degree := by
    calc
      remainder.degree ≤ 1 := by
        exact degree_linear_le
      _ < (monicQuadratic a b).degree := by
        rw [degree_eq_natDegree hquadMonic.ne_zero, hquadDegree]
        norm_num
  have hdivision :
      remainder + monicQuadratic a b * forcedCubic s a b =
        normalizedQuintic s := by
    rw [normalizedQuintic_quadratic_division]
    ring
  have hforcedQuotient :
      normalizedQuintic s /ₘ monicQuadratic a b =
        forcedCubic s a b :=
    (div_modByMonic_unique
      (forcedCubic s a b) remainder hquadMonic
      ⟨hdivision, hremainderDegree⟩).1
  have hgivenQuotient :
      normalizedQuintic s /ₘ monicQuadratic a b = B := by
    calc
      normalizedQuintic s /ₘ monicQuadratic a b =
          (monicQuadratic a b * B) /ₘ monicQuadratic a b := by
            rw [← hA, ← hfactor]
      _ = B := mul_divByMonic_cancel_left B hquadMonic
  have hB : B = forcedCubic s a b :=
    hgivenQuotient.symm.trans hforcedQuotient
  refine ⟨a, b, ?_⟩
  rw [← hB, ← hA]
  exact hfactor

/--
An abstract monic `2+3` factorization satisfies exactly the two scalar
remainder equations used by the later certificates.
-/
theorem quadraticCubicCase_remainders
    {s : ℚ} (h : QuadraticCubicCase s) :
    ∃ a b : ℚ, SatisfiesQuadraticRemainders s a b := by
  obtain ⟨a, b, hfactor⟩ := quadraticCubicCase_forced_factorization h
  exact ⟨a, b, quadratic_remainders_of_forced_factorization hfactor⟩

/-- A rational number is a square up to one global physical sign. -/
def IsSignedSquare (b : ℚ) : Prop :=
  ∃ ε : PhysicalSign, ∃ c : ℚ, b = ε.value * c ^ 2

/--
The exact C012 input needed after coefficient extraction: every explicit
quadratic factor of `P_s` has signed-square constant coefficient.
-/
def QuadraticFactorConstantsSignedSquare (s : ℚ) : Prop :=
  ∀ a b : ℚ,
    normalizedQuintic s = monicQuadratic a b * forcedCubic s a b →
      IsSignedSquare b

/-- The admissible parameter is visibly a rational square. -/
theorem sharipovParameter_isSquare (p q : ℕ) :
    ∃ z : ℚ, sharipovParameter p q = z ^ 2 := by
  exact ⟨(p : ℚ) / (q : ℚ), rfl⟩

/--
The coefficient reduction is lossless once the two arithmetic square
inputs are supplied: squarehood of `s` and signed squarehood of the
quadratic constant.  The output is exactly the input expected by
`compact_equations_of_remainders`.
-/
theorem compact_data_of_remainders
    {s a b : ℚ}
    (hs : 0 < s)
    (hremainder : SatisfiesQuadraticRemainders s a b)
    (hsSquare : ∃ z : ℚ, s = z ^ 2)
    (hbSquare : IsSignedSquare b) :
    ∃ ε : PhysicalSign, ∃ z k y : ℚ,
      z ≠ 0 ∧ k ≠ 0 ∧
      s = z ^ 2 ∧
      a = z ^ 2 * k * y ∧
      b = ε.value * z ^ 4 * k ^ 2 ∧
      compactF1 ε z k y = 0 ∧ compactF0 ε z k y = 0 := by
  rcases hsSquare with ⟨z, hsSquare⟩
  rcases hbSquare with ⟨ε, c, hbSquare⟩
  have hsne : s ≠ 0 := ne_of_gt hs
  have hz : z ≠ 0 := by
    intro hz
    apply hsne
    rw [hsSquare, hz]
    norm_num
  have hbne : b ≠ 0 := by
    intro hb
    have hzero : -(s ^ 5) = 0 := by
      simpa [quadraticR0, quinticC0, hb] using hremainder.2
    exact (neg_ne_zero.mpr (pow_ne_zero 5 hsne)) hzero
  have hc : c ≠ 0 := by
    intro hc
    apply hbne
    rw [hbSquare, hc]
    norm_num
  let k : ℚ := c / z ^ 2
  have hk : k ≠ 0 := by
    exact div_ne_zero hc (pow_ne_zero 2 hz)
  let y : ℚ := a / (z ^ 2 * k)
  have ha : a = z ^ 2 * k * y := by
    dsimp [y]
    field_simp [hz, hk]
  have hb : b = ε.value * z ^ 4 * k ^ 2 := by
    rw [hbSquare]
    dsimp [k]
    field_simp [hz]
  have hscaled :
      SatisfiesQuadraticRemainders
        (z ^ 2) (z ^ 2 * k * y) (ε.value * z ^ 4 * k ^ 2) := by
    simpa only [hsSquare, ha, hb] using hremainder
  obtain ⟨h1, h0⟩ :=
    compact_equations_of_remainders (ε := ε) hz hscaled
  exact ⟨ε, z, k, y, hz, hk, hsSquare, ha, hb, h1, h0⟩

/--
Conditional endpoint of the extraction stage.  For an admissible parameter,
the only remaining arithmetic premise is precisely the signed-square
constant theorem C012.
-/
theorem quadraticCubicCase_to_compact
    {p q : ℕ}
    (hp : 0 < p)
    (hq : 0 < q)
    (hcase : QuadraticCubicCase (sharipovParameter p q))
    (hC012 :
      QuadraticFactorConstantsSignedSquare (sharipovParameter p q)) :
    ∃ ε : PhysicalSign, ∃ z k y : ℚ,
      z ≠ 0 ∧ k ≠ 0 ∧
      sharipovParameter p q = z ^ 2 ∧
      compactF1 ε z k y = 0 ∧ compactF0 ε z k y = 0 := by
  obtain ⟨a, b, hfactor⟩ :=
    quadraticCubicCase_forced_factorization hcase
  have hremainder :=
    quadratic_remainders_of_forced_factorization hfactor
  have hs : 0 < sharipovParameter p q :=
    sharipovParameter_pos hp hq
  have hb : IsSignedSquare b :=
    hC012 a b hfactor
  obtain ⟨ε, z, k, y, hz, hk, hsquare, _, _, h1, h0⟩ :=
    compact_data_of_remainders hs hremainder
      (sharipovParameter_isSquare p q) hb
  exact ⟨ε, z, k, y, hz, hk, hsquare, h1, h0⟩

end

end Cuboid2
