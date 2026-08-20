import Cuboid2.QuadraticReduction.GaussianP29SaturationActual

/-!
# The Gaussian-rational root obstruction at `29`

This module turns the closed residue-field certificate for the seventh
preimage polynomial into a characteristic-zero statement.  Monicity first
forces a putative root in `ℚ(i)` to lie in `ℤ[i]`; reducing that integral root
at the split Gaussian prime `i ↦ 12` then contradicts the finite computation.
-/

namespace Cuboid2
namespace GaussianP29PolynomialRootBridge

noncomputable section

open scoped Polynomial
open GaussianDescent GaussianFraction GaussianP29SaturationActual
  GaussianIndexIndependent GaussianSaturationBridge

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

/-! ## Evaluation and reduction of the explicit polynomial -/

theorem eval₂_psiTwoSq
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : R) (x : S) :
    (psiTwoSq A B).eval₂ f x =
      psiTwoSqValue (f A) (f B) x := by
  simp [psiTwoSq, psiTwoSqValue, Polynomial.eval₂_pow,
    _root_.map_ofNat]

theorem eval₂_psiThree
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : R) (x : S) :
    (psiThree A B).eval₂ f x =
      psiThreeValue (f A) (f B) x := by
  simp [psiThree, psiThreeValue, Polynomial.eval₂_pow,
    _root_.map_ofNat]

theorem eval₂_prePsiFour
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : R) (x : S) :
    (prePsiFour A B).eval₂ f x =
      prePsiFourValue (f A) (f B) x := by
  simp [prePsiFour, prePsiFourValue, Polynomial.eval₂_pow,
    _root_.map_ofNat]

theorem eval₂_prePsiFive
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : R) (x : S) :
    (prePsiFive A B).eval₂ f x =
      prePsiFiveValue (f A) (f B) x := by
  simp [prePsiFive, prePsiFiveValue, eval₂_prePsiFour,
    eval₂_psiTwoSq, eval₂_psiThree, Polynomial.eval₂_pow]

theorem eval₂_prePsiSix
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : R) (x : S) :
    (prePsiSix A B).eval₂ f x =
      prePsiSixValue (f A) (f B) x := by
  simp [prePsiSix, prePsiSixValue, eval₂_prePsiFive,
    eval₂_prePsiFour, eval₂_psiThree, Polynomial.eval₂_pow]

theorem eval₂_prePsiSeven
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : R) (x : S) :
    (prePsiSeven A B).eval₂ f x =
      prePsiSevenValue (f A) (f B) x := by
  simp [prePsiSeven, prePsiSevenValue, eval₂_prePsiFive,
    eval₂_prePsiFour, eval₂_psiTwoSq, eval₂_psiThree,
    Polynomial.eval₂_pow]

theorem eval₂_prePsiEight
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : R) (x : S) :
    (prePsiEight A B).eval₂ f x =
      prePsiEightValue (f A) (f B) x := by
  simp [prePsiEight, prePsiEightValue, eval₂_prePsiSix,
    eval₂_prePsiFive, eval₂_prePsiFour, eval₂_psiThree,
    Polynomial.eval₂_pow]

theorem eval₂_psiSevenSq
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : R) (x : S) :
    (psiSevenSq A B).eval₂ f x =
      psiSevenSqValue (f A) (f B) x := by
  simp [psiSevenSq, psiSevenSqValue, eval₂_prePsiSeven,
    Polynomial.eval₂_pow]

theorem eval₂_phiSeven
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : R) (x : S) :
    (phiSeven A B).eval₂ f x =
      phiSevenValue (f A) (f B) x := by
  simp [phiSeven, phiSevenValue, eval₂_psiSevenSq,
    eval₂_prePsiEight, eval₂_prePsiSix, eval₂_psiTwoSq]

/-- Evaluation of the polynomial commutes with any coefficient homomorphism
and is exactly the denominator-free scalar recurrence. -/
theorem eval₂_sevenPreimagePolynomial
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : R) (x : S) :
    (sevenPreimagePolynomial A B).eval₂ f x =
      sevenPreimageValue (f A) (f B) x := by
  simp [sevenPreimagePolynomial, sevenPreimageValue, eval₂_phiSeven,
    eval₂_psiSevenSq]

/-- Ordinary evaluation is the scalar seventh-preimage recurrence. -/
theorem eval_sevenPreimagePolynomial
    {R : Type*} [CommRing R] (A B x : R) :
    (sevenPreimagePolynomial A B).eval x =
      sevenPreimageValue A B x := by
  simpa using
    (eval₂_sevenPreimagePolynomial (RingHom.id R) A B x)

@[simp] theorem residueHom29_e0AInt :
    residueHom29 e0AInt = (24 : ZMod 29) := by
  native_decide

@[simp] theorem residueHom29_e0BInt :
    residueHom29 e0BInt = (8 : ZMod 29) := by
  native_decide

/-- Reduction of the integral seventh-preimage polynomial evaluates to the
closed finite recurrence with coefficients `24` and `8`. -/
theorem eval_map_residueHom29 (z : GaussianInt) :
    ((sevenPreimagePolynomial e0AInt e0BInt).map residueHom29).eval
        (residueHom29 z) =
      sevenPreimageValue 24 8 (residueHom29 z) := by
  rw [Polynomial.eval_map,
    eval₂_sevenPreimagePolynomial,
    residueHom29_e0AInt,
    residueHom29_e0BInt]

/-- Over `ℚ(i)`, algebraic evaluation of the integral polynomial is the
same scalar recurrence used by the actual weighted group-law computation. -/
theorem aeval_sevenPreimagePolynomial_eq_value (x : GaussianRat) :
    Polynomial.aeval x
        (sevenPreimagePolynomial e0AInt e0BInt) =
      sevenPreimageValue E0A E0B x := by
  rw [Polynomial.aeval_def,
    eval₂_sevenPreimagePolynomial,
    algebraMap_e0AInt,
    algebraMap_e0BInt]

theorem sevenPreimageValue_eq_zero_iff_aeval_eq_zero
    (x : GaussianRat) :
    sevenPreimageValue E0A E0B x = 0 ↔
      Polynomial.aeval x
        (sevenPreimagePolynomial e0AInt e0BInt) = 0 := by
  rw [aeval_sevenPreimagePolynomial_eq_value]

/-! ## Lifting and excluding characteristic-zero roots -/

/-- A Gaussian-rational root of the monic seventh-preimage polynomial is the
image of a Gaussian integer.  The extra divisibility conclusion supplied by
the rational-root theorem is retained for downstream reuse. -/
theorem exists_gaussianInt_root_data
    {x : GaussianRat}
    (hx :
      Polynomial.aeval x
        (sevenPreimagePolynomial e0AInt e0BInt) = 0) :
    ∃ z : GaussianInt,
      x = algebraMap GaussianInt GaussianRat z ∧
        z ∣ (sevenPreimagePolynomial e0AInt e0BInt).coeff 0 := by
  exact exists_integer_of_is_root_of_monic
    sevenPreimagePolynomial_monic hx

/-- In particular, every Gaussian-rational root is integral. -/
theorem exists_gaussianInt_of_root
    {x : GaussianRat}
    (hx :
      Polynomial.aeval x
        (sevenPreimagePolynomial e0AInt e0BInt) = 0) :
    ∃ z : GaussianInt,
      x = algebraMap GaussianInt GaussianRat z := by
  obtain ⟨z, hz, _⟩ := exists_gaussianInt_root_data hx
  exact ⟨z, hz⟩

/-- The explicit seventh-preimage polynomial has no root in `ℚ(i)`. -/
theorem sevenPreimagePolynomial_no_gaussianRat_root
    (x : GaussianRat) :
    Polynomial.aeval x
      (sevenPreimagePolynomial e0AInt e0BInt) ≠ 0 := by
  intro hx
  obtain ⟨z, rfl⟩ := exists_gaussianInt_of_root hx
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at hx
  have hz :
      (sevenPreimagePolynomial e0AInt e0BInt).eval z = 0 :=
    FaithfulSMul.algebraMap_injective GaussianInt GaussianRat <| by
      simpa only [map_zero] using hx
  have hz29 :
      ((sevenPreimagePolynomial e0AInt e0BInt).map residueHom29).eval
          (residueHom29 z) = 0 := by
    rw [Polynomial.eval_map_apply]
    simpa only [map_zero] using congrArg residueHom29 hz
  have hvalue :
      sevenPreimageValue 24 8 (residueHom29 z) = 0 := by
    rw [← eval_map_residueHom29]
    exact hz29
  exact p29_sevenPreimagePolynomial_no_root (residueHom29 z) hvalue

/-- Existential form of the Gaussian-rational root obstruction. -/
theorem not_exists_gaussianRat_root :
    ¬ ∃ x : GaussianRat,
      Polynomial.aeval x
        (sevenPreimagePolynomial e0AInt e0BInt) = 0 := by
  rintro ⟨x, hx⟩
  exact sevenPreimagePolynomial_no_gaussianRat_root x hx

/-! ## Actual seven-saturation consumers -/

/-- The first coordinate of the visible point is nonzero in every exact
rank-one normal form. -/
theorem visiblePoint_freeCoordinate_ne_zero
    (e : E0Point ≃+ ℤ × ZMod 2) :
    (e visiblePoint).1 ≠ 0 := by
  obtain ⟨m, δ, hδ, hP⟩ := exists_normalForm e visiblePoint
  have hm : Odd m := visibleCoefficient_odd e hδ hP
  have hfirst : (e visiblePoint).1 = m := by
    rw [hP, map_add, map_zsmul, map_nsmul,
      freeGenerator_image, gaussianE0T_image]
    simp
  rw [hfirst]
  obtain ⟨k, hk⟩ := hm
  omega

/-- The visible point has no seventh preimage in the actual Gaussian
elliptic curve.  The normal-form equivalence is used only to rule out the
torsion case before invoking the coordinate computation. -/
theorem visiblePoint_not_seven_divisible
    (e : E0Point ≃+ ℤ × ZMod 2) :
    ¬ ∃ Q : E0Point, 7 • Q = visiblePoint := by
  rintro ⟨Q, hseven⟩
  have hfree : (e Q).1 ≠ 0 := by
    intro hQ
    apply visiblePoint_freeCoordinate_ne_zero e
    have hmap :=
      congrArg (fun R : E0Point => (e R).1) hseven
    simp only [map_nsmul] at hmap
    simpa [hQ] using hmap.symm
  obtain ⟨x, hvalue⟩ :=
    exists_weighted_seven_preimage e Q hfree hseven
  exact
    sevenPreimagePolynomial_no_gaussianRat_root x
      ((sevenPreimageValue_eq_zero_iff_aeval_eq_zero x).mp hvalue)

/-- In every exact rank-one normal form, the free coefficient of the visible
point is not divisible by seven. -/
theorem seven_not_dvd_visiblePoint_coefficient
    (e : E0Point ≃+ ℤ × ZMod 2)
    {m : ℤ} {δ : ℕ}
    (hP :
      visiblePoint = m • freeGenerator e + δ • twoTorsionPoint) :
    ¬ (7 : ℤ) ∣ m := by
  intro hdiv
  apply visiblePoint_not_seven_divisible e
  exact
    visiblePoint_divisible_of_odd_dvd_coefficient
      e hP (by norm_num) hdiv

end

end GaussianP29PolynomialRootBridge
end Cuboid2
