import Cuboid2.QuadraticReduction.GaussianDescent
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Valuation.PrimeMultiplicity

/-!
# Valuation support for the Gaussian two-isogeny descent

This module builds the prime-element valuation on the actual fraction-field
model `GaussianRat` from multiplicity in the Euclidean domain `GaussianInt`.
It is the global support input for the four specialized Kummer images.
-/

namespace Cuboid2

noncomputable section

namespace GaussianSupport

open GaussianFraction
open GaussianDescent

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

private theorem algebraMap_gaussianInt_ne_zero
    {r : GaussianInt} (hr : r ≠ 0) :
    algebraMap GaussianInt GaussianRat r ≠ 0 := by
  intro h
  apply hr
  apply FaithfulSMul.algebraMap_injective GaussianInt GaussianRat
  simpa only [map_zero] using h

/-- The order-preserving additive embedding
`ℕ∞ → WithTop ℤ`, including the value at infinity. -/
private def enatToWithTopInt : ℕ∞ →+ WithTop ℤ :=
  (Nat.castAddMonoidHom ℤ).ENatMap

private theorem enatToWithTopInt_monotone :
    Monotone enatToWithTopInt := by
  rw [show enatToWithTopInt =
      (Nat.castAddMonoidHom ℤ).ENatMap by rfl]
  apply ENat.monotone_map_iff.mpr
  intro a b hab
  change (a : ℤ) ≤ (b : ℤ)
  exact_mod_cast hab

/-- Multiplicity at a prime element, regarded as an integer-valued additive
valuation on `GaussianInt`. -/
def primeMultiplicityInt {p : GaussianInt} (hp : Prime p) :
    AddValuation GaussianInt (WithTop ℤ) :=
  (multiplicity_addValuation hp).map enatToWithTopInt
    (by simp [enatToWithTopInt])
    enatToWithTopInt_monotone

private theorem primeMultiplicityInt_ne_top
    {p r : GaussianInt} (hp : Prime p) (hr : r ≠ 0) :
    primeMultiplicityInt hp r ≠ (⊤ : WithTop ℤ) := by
  have hfinite : FiniteMultiplicity p r :=
    FiniteMultiplicity.of_prime_left hp hr
  simp only [primeMultiplicityInt, AddValuation.map_apply,
    multiplicity_addValuation_apply, enatToWithTopInt]
  rw [hfinite.emultiplicity_eq_multiplicity]
  simp

private theorem primeMultiplicityInt_nonZeroDivisors
    {p : GaussianInt} (hp : Prime p) :
    nonZeroDivisors GaussianInt ≤
      (AddValuation.toValuation (primeMultiplicityInt hp)).supp.primeCompl := by
  intro r hr
  apply Set.mem_compl
  intro hmem
  have htop : primeMultiplicityInt hp r = (⊤ : WithTop ℤ) :=
    (AddValuation.mem_supp_iff (primeMultiplicityInt hp) r).mp hmem
  exact primeMultiplicityInt_ne_top hp
    (mem_nonZeroDivisors_iff_ne_zero.mp hr) htop

/-- The additive `p`-adic order on the actual field `GaussianRat`, obtained
by extending prime multiplicity through `IsFractionRing`. -/
def gaussianPrimeOrder {p : GaussianInt} (hp : Prime p) :
    AddValuation GaussianRat (WithTop ℤ) :=
  AddValuation.ofValuation <|
    (AddValuation.toValuation (primeMultiplicityInt hp)).extendToLocalization
      (S := nonZeroDivisors GaussianInt)
      (primeMultiplicityInt_nonZeroDivisors hp)
      GaussianRat

@[simp] theorem gaussianPrimeOrder_algebraMap
    {p : GaussianInt} (hp : Prime p) (r : GaussianInt) :
    gaussianPrimeOrder hp (algebraMap GaussianInt GaussianRat r) =
      primeMultiplicityInt hp r := by
  simp only [gaussianPrimeOrder, AddValuation.ofValuation_apply,
    Valuation.extendToLocalization_apply_map_apply,
    AddValuation.toValuation_apply]
  rfl

private theorem primeMultiplicityInt_eq_coe
    {p r : GaussianInt} (hp : Prime p) (hr : r ≠ 0) :
    primeMultiplicityInt hp r =
      ((multiplicity p r : ℤ) : WithTop ℤ) := by
  have hfinite : FiniteMultiplicity p r :=
    FiniteMultiplicity.of_prime_left hp hr
  simp only [primeMultiplicityInt, AddValuation.map_apply,
    multiplicity_addValuation_apply, enatToWithTopInt]
  rw [hfinite.emultiplicity_eq_multiplicity]
  rfl

theorem gaussianPrimeOrder_algebraMap_nonneg
    {p : GaussianInt} (hp : Prime p) (r : GaussianInt) :
    (0 : WithTop ℤ) ≤
      gaussianPrimeOrder hp (algebraMap GaussianInt GaussianRat r) := by
  rw [gaussianPrimeOrder_algebraMap]
  by_cases hr : r = 0
  · subst r
    simp [primeMultiplicityInt]
  · rw [primeMultiplicityInt_eq_coe hp hr]
    exact_mod_cast (Nat.zero_le (multiplicity p r))

theorem gaussianPrimeOrder_algebraMap_eq_zero_of_not_dvd
    {p r : GaussianInt} (hp : Prime p) (hr : ¬p ∣ r) :
    gaussianPrimeOrder hp (algebraMap GaussianInt GaussianRat r) = 0 := by
  have hr0 : r ≠ 0 := by
    intro h
    subst r
    exact hr (dvd_zero p)
  rw [gaussianPrimeOrder_algebraMap,
    primeMultiplicityInt_eq_coe hp hr0,
    (multiplicity_eq_zero.mpr hr)]
  rfl

/-- The extended Gaussian prime order is the numerator multiplicity minus
the denominator multiplicity in Mathlib's canonical reduced fraction. -/
theorem gaussianPrimeOrder_eq_num_sub_den
    {p : GaussianInt} (hp : Prime p) {x : GaussianRat} (hx : x ≠ 0) :
    gaussianPrimeOrder hp x =
      (((multiplicity p (IsFractionRing.num GaussianInt x) : ℤ) -
        (multiplicity p
          (IsFractionRing.den GaussianInt x : GaussianInt) : ℤ) : ℤ) :
        WithTop ℤ) := by
  have hn : IsFractionRing.num GaussianInt x ≠ 0 :=
    (IsFractionRing.num_eq_zero x).not.mpr hx
  have hd :
      (IsFractionRing.den GaussianInt x : GaussianInt) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp
      (IsFractionRing.den GaussianInt x).property
  calc
    gaussianPrimeOrder hp x =
        gaussianPrimeOrder hp
          (algebraMap GaussianInt GaussianRat
              (IsFractionRing.num GaussianInt x) /
            algebraMap GaussianInt GaussianRat
              (IsFractionRing.den GaussianInt x : GaussianInt)) :=
      congrArg (gaussianPrimeOrder hp)
        (IsFractionRing.mk'_num_den' GaussianInt x).symm
    _ = _ := by
      rw [(gaussianPrimeOrder hp).map_div,
        gaussianPrimeOrder_algebraMap,
        gaussianPrimeOrder_algebraMap,
        primeMultiplicityInt_eq_coe hp hn,
        primeMultiplicityInt_eq_coe hp hd]
      norm_cast

/-- A nonzero field element has the same squareclass as the product of the
numerator and denominator of its canonical reduced Gaussian fraction. -/
theorem squareClassOf_eq_num_mul_den
    {x : GaussianRat} (hx : x ≠ 0) :
    squareClassOf x hx =
      squareClassOf
        (algebraMap GaussianInt GaussianRat
          (IsFractionRing.num GaussianInt x *
            (IsFractionRing.den GaussianInt x : GaussianInt)))
        (by
          apply algebraMap_gaussianInt_ne_zero
          exact mul_ne_zero
            ((IsFractionRing.num_eq_zero x).not.mpr hx)
            (mem_nonZeroDivisors_iff_ne_zero.mp
              (IsFractionRing.den GaussianInt x).property)) := by
  have hn : IsFractionRing.num GaussianInt x ≠ 0 :=
    (IsFractionRing.num_eq_zero x).not.mpr hx
  have hd :
      (IsFractionRing.den GaussianInt x : GaussianInt) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp
      (IsFractionRing.den GaussianInt x).property
  have hmapd :
      algebraMap GaussianInt GaussianRat
          (IsFractionRing.den GaussianInt x : GaussianInt) ≠ 0 :=
    algebraMap_gaussianInt_ne_zero hd
  apply (squareClassOf_eq_iff hx
    (algebraMap_gaussianInt_ne_zero (mul_ne_zero hn hd))).mpr
  refine ⟨(algebraMap GaussianInt GaussianRat
    (IsFractionRing.den GaussianInt x : GaussianInt))⁻¹,
    inv_ne_zero hmapd, ?_⟩
  calc
    x = algebraMap GaussianInt GaussianRat
          (IsFractionRing.num GaussianInt x) /
        algebraMap GaussianInt GaussianRat
          (IsFractionRing.den GaussianInt x : GaussianInt) :=
      (IsFractionRing.mk'_num_den' GaussianInt x).symm
    _ = algebraMap GaussianInt GaussianRat
          (IsFractionRing.num GaussianInt x *
            (IsFractionRing.den GaussianInt x : GaussianInt)) *
        (algebraMap GaussianInt GaussianRat
          (IsFractionRing.den GaussianInt x : GaussianInt))⁻¹ ^ 2 := by
      rw [map_mul]
      field_simp [hmapd]

/-- On `y² = x(x² + Ax + B)`, the order of a nonzero abscissa is even at
every additive valuation for which `A` is integral and `B` is a unit. -/
theorem curve_abscissa_order_even
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    {A B x y : K}
    (hx : x ≠ 0)
    (hA : (0 : WithTop ℤ) ≤ v A)
    (hB : v B = 0)
    (hcurve : y ^ 2 = x * (x ^ 2 + A * x + B)) :
    ∃ n : ℤ, v x = ((2 * n : ℤ) : WithTop ℤ) := by
  have hvxTop : v x ≠ (⊤ : WithTop ℤ) :=
    (v.ne_top_iff).mpr hx
  lift v x to ℤ using hvxTop with vx hvx
  rcases lt_trichotomy vx 0 with hvxNeg | hvxZero | hvxPos
  · have hxSq :
        v (x ^ 2) = ((2 * vx : ℤ) : WithTop ℤ) := by
      rw [v.map_pow, ← hvx]
      simp only [two_nsmul]
      norm_cast
      ring
    have hAx :
        ((vx : ℤ) : WithTop ℤ) ≤ v (A * x) := by
      rw [v.map_mul, ← hvx]
      simpa [add_comm] using add_le_add_right hA (vx : WithTop ℤ)
    have hxSq_lt_x :
        ((2 * vx : ℤ) : WithTop ℤ) < (vx : WithTop ℤ) := by
      exact_mod_cast (by omega : 2 * vx < vx)
    have hxSq_lt_Ax :
        ((2 * vx : ℤ) : WithTop ℤ) < v (A * x) :=
      hxSq_lt_x.trans_le hAx
    have hxSq_lt_B :
        ((2 * vx : ℤ) : WithTop ℤ) < v B := by
      rw [hB]
      exact_mod_cast (by omega : 2 * vx < 0)
    have hfirst :
        v (x ^ 2 + A * x) = ((2 * vx : ℤ) : WithTop ℤ) := by
      rw [v.map_add_eq_of_lt_left (hxSq ▸ hxSq_lt_Ax), hxSq]
    have hfactor :
        v (x ^ 2 + A * x + B) =
          ((2 * vx : ℤ) : WithTop ℤ) := by
      rw [v.map_add_eq_of_lt_left (hfirst ▸ hxSq_lt_B), hfirst]
    have hfactor0 : x ^ 2 + A * x + B ≠ 0 := by
      apply (v.ne_top_iff).mp
      rw [hfactor]
      exact WithTop.coe_ne_top
    have hy : y ≠ 0 := by
      intro hy
      rw [hy, zero_pow (by norm_num)] at hcurve
      exact (mul_ne_zero hx hfactor0) hcurve.symm
    have hvyTop : v y ≠ (⊤ : WithTop ℤ) :=
      (v.ne_top_iff).mpr hy
    lift v y to ℤ using hvyTop with vy hvy
    have horders := congrArg v hcurve
    simp only [v.map_pow, v.map_mul, ← hvx, ← hvy, hfactor] at horders
    simp only [two_nsmul] at horders
    norm_cast at horders
    have hInt : 2 * vy = 3 * vx := by
      omega
    have heven : Even vx := by
      rw [Int.even_iff]
      omega
    obtain ⟨n, hn⟩ := heven
    exact ⟨n, by rw [hn]; norm_cast; ring⟩
  · exact ⟨0, by rw [hvxZero]; norm_num⟩
  · have hxSqPos :
        (0 : WithTop ℤ) < v (x ^ 2) := by
      rw [v.map_pow, ← hvx]
      exact_mod_cast (by omega : 0 < 2 * vx)
    have hAxPos :
        (0 : WithTop ℤ) < v (A * x) := by
      have hAxLower :
          ((vx : ℤ) : WithTop ℤ) ≤ v (A * x) := by
        rw [v.map_mul, ← hvx]
        simpa [add_comm] using
          add_le_add_right hA (vx : WithTop ℤ)
      exact (by exact_mod_cast hvxPos : (0 : WithTop ℤ) < vx).trans_le
        hAxLower
    have hfirstPos :
        (0 : WithTop ℤ) < v (x ^ 2 + A * x) :=
      v.map_lt_add hxSqPos hAxPos
    have hfactor :
        v (x ^ 2 + A * x + B) = 0 := by
      rw [v.map_add_eq_of_lt_right]
      · exact hB
      · simpa [hB] using hfirstPos
    have hfactor0 : x ^ 2 + A * x + B ≠ 0 := by
      apply (v.ne_top_iff).mp
      rw [hfactor]
      simp
    have hy : y ≠ 0 := by
      intro hy
      rw [hy, zero_pow (by norm_num)] at hcurve
      exact (mul_ne_zero hx hfactor0) hcurve.symm
    have hvyTop : v y ≠ (⊤ : WithTop ℤ) :=
      (v.ne_top_iff).mpr hy
    lift v y to ℤ using hvyTop with vy hvy
    have horders := congrArg v hcurve
    simp only [v.map_pow, v.map_mul, ← hvx, ← hvy, hfactor,
      add_zero] at horders
    simp only [two_nsmul] at horders
    norm_cast at horders
    have hInt : 2 * vy = vx := by
      omega
    have heven : Even vx := by
      rw [Int.even_iff]
      omega
    obtain ⟨n, hn⟩ := heven
    exact ⟨n, by rw [hn]; norm_cast; ring⟩

/-- A prime away from the constant coefficient occurs to even total
multiplicity in the numerator times denominator of a nonzero abscissa. -/
theorem curve_abscissa_num_mul_den_even
    {p A B : GaussianInt} (hp : Prime p) (hpB : ¬p ∣ B)
    {x y : GaussianRat} (hx : x ≠ 0)
    (hcurve :
      y ^ 2 =
        x * (x ^ 2 +
          algebraMap GaussianInt GaussianRat A * x +
          algebraMap GaussianInt GaussianRat B)) :
    Even (multiplicity p
      (IsFractionRing.num GaussianInt x *
        (IsFractionRing.den GaussianInt x : GaussianInt))) := by
  have hn : IsFractionRing.num GaussianInt x ≠ 0 :=
    (IsFractionRing.num_eq_zero x).not.mpr hx
  have hd :
      (IsFractionRing.den GaussianInt x : GaussianInt) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp
      (IsFractionRing.den GaussianInt x).property
  obtain ⟨n, hnOrder⟩ := curve_abscissa_order_even
    (gaussianPrimeOrder hp) hx
    (gaussianPrimeOrder_algebraMap_nonneg hp A)
    (gaussianPrimeOrder_algebraMap_eq_zero_of_not_dvd hp hpB)
    hcurve
  rw [gaussianPrimeOrder_eq_num_sub_den hp hx] at hnOrder
  have hdiff :
      (multiplicity p (IsFractionRing.num GaussianInt x) : ℤ) -
        (multiplicity p
          (IsFractionRing.den GaussianInt x : GaussianInt) : ℤ) =
        2 * n := by
    exact_mod_cast hnOrder
  have hfinite :
      FiniteMultiplicity p
        (IsFractionRing.num GaussianInt x *
          (IsFractionRing.den GaussianInt x : GaussianInt)) :=
    FiniteMultiplicity.of_prime_left hp (mul_ne_zero hn hd)
  rw [multiplicity_mul hp hfinite]
  rw [Nat.even_iff]
  omega

end GaussianSupport

end

end Cuboid2
