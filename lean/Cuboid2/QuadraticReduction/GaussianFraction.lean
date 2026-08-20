import Cuboid2.QuadraticReduction.GaussianCover
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Gaussian rationals as the fraction field of Gaussian integers

The project represents `ℚ(i)` by `QuadraticAlgebra ℚ (-1) 0`, while Mathlib's
Euclidean Gaussian integers are `GaussianInt = Zsqrtd (-1)`.  This file gives
the explicit inclusion and proves that the former is the fraction field of
the latter.  The bridge allows the fixed two-isogeny descent to use
factorization and valuation facts from `GaussianInt` without changing its
elliptic-curve models.
-/

namespace Cuboid2

noncomputable section

open scoped QuadraticAlgebra

namespace GaussianFraction

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

/-- The coordinatewise inclusion `ℤ[i] → ℚ(i)`. -/
def gaussianIntToRat : GaussianInt →+* GaussianRat :=
  Zsqrtd.lift
    ⟨gaussianI, by
      simpa [pow_two] using gaussianI_sq⟩

@[simp] theorem gaussianIntToRat_apply (z : GaussianInt) :
    gaussianIntToRat z =
      (⟨(z.re : ℚ), (z.im : ℚ)⟩ : GaussianRat) := by
  ext <;> simp [gaussianIntToRat, gaussianI]

instance gaussianIntAlgebra : Algebra GaussianInt GaussianRat :=
  gaussianIntToRat.toAlgebra

@[simp] theorem algebraMap_gaussianInt_apply (z : GaussianInt) :
    algebraMap GaussianInt GaussianRat z =
      (⟨(z.re : ℚ), (z.im : ℚ)⟩ : GaussianRat) :=
  gaussianIntToRat_apply z

theorem gaussianIntToRat_injective :
    Function.Injective gaussianIntToRat := by
  apply Zsqrtd.lift_injective
  intro n hn
  have hnonneg : 0 ≤ n * n := mul_self_nonneg n
  omega

instance gaussianIntFaithfulSMul : FaithfulSMul GaussianInt GaussianRat :=
  (faithfulSMul_iff_algebraMap_injective GaussianInt GaussianRat).mpr
    gaussianIntToRat_injective

private def commonNumerator (z : GaussianRat) : GaussianInt :=
  ⟨z.re.num * z.im.den, z.im.num * z.re.den⟩

private def commonDenominator (z : GaussianRat) : GaussianInt :=
  ⟨z.re.den * z.im.den, 0⟩

private theorem commonDenominator_ne_zero (z : GaussianRat) :
    commonDenominator z ≠ 0 := by
  intro h
  have hre := congrArg Zsqrtd.re h
  simp only [commonDenominator, Zsqrtd.re_zero] at hre
  have hprod : z.re.den * z.im.den = 0 := by exact_mod_cast hre
  exact (Nat.mul_ne_zero z.re.den_ne_zero z.im.den_ne_zero) hprod

private theorem eq_common_fraction (z : GaussianRat) :
    z =
      algebraMap GaussianInt GaussianRat (commonNumerator z) /
        algebraMap GaussianInt GaussianRat (commonDenominator z) := by
  have hd :
      algebraMap GaussianInt GaussianRat (commonDenominator z) ≠ 0 :=
    fun h ↦ commonDenominator_ne_zero z <|
      FaithfulSMul.algebraMap_injective GaussianInt GaussianRat <| by
        simpa only [map_zero] using h
  apply (eq_div_iff hd).2
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_mul, algebraMap_gaussianInt_apply,
      commonNumerator, commonDenominator, Int.cast_mul,
      Int.cast_natCast]
    have hre :
        z.re * (z.re.den : ℚ) = (z.re.num : ℚ) :=
      Rat.mul_den_eq_num z.re
    norm_num
    linear_combination (z.im.den : ℚ) * hre
  · simp only [QuadraticAlgebra.im_mul, algebraMap_gaussianInt_apply,
      commonNumerator, commonDenominator, Int.cast_mul,
      Int.cast_natCast]
    have him :
        z.im * (z.im.den : ℚ) = (z.im.num : ℚ) :=
      Rat.mul_den_eq_num z.im
    norm_num
    linear_combination (z.re.den : ℚ) * him

/-- The actual `QuadraticAlgebra` model `ℚ(i)` is the fraction field of
Mathlib's Euclidean domain of Gaussian integers. -/
instance gaussianRatIsFractionRing :
    IsFractionRing GaussianInt GaussianRat :=
  IsFractionRing.of_field GaussianInt GaussianRat fun z =>
    ⟨commonNumerator z, commonDenominator z, eq_common_fraction z⟩

end GaussianFraction

end

end Cuboid2
