import Cuboid2.QuadraticReduction.GaussianMordellWeil
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity

/-!
# Excluding Gaussian three-torsion

This file uses one inert Gaussian prime, `11`, to exclude roots of the
three-division quartics of the two specialized curves.  Working at an inert
prime keeps the residue ring a field, while a closed finite computation checks
both quartics on all `11²` residue classes.
-/

namespace Cuboid2
namespace GaussianThreeTorsion

noncomputable section

open GaussianDescent
open GaussianFraction

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

private local instance :
    Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

private local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The inert quadratic residue field `𝔽₁₁(i)`. -/
abbrev GaussianResidue11 :=
  QuadraticAlgebra (ZMod 11) (-1) 0

private theorem residue11_irreducible :
    ∀ x : ZMod 11, x ^ 2 ≠ (-1 : ZMod 11) + 0 * x := by
  native_decide

private local instance :
    Fact (∀ x : ZMod 11, x ^ 2 ≠ (-1 : ZMod 11) + 0 * x) :=
  ⟨residue11_irreducible⟩

private local instance : Fintype GaussianResidue11 :=
  Fintype.ofEquiv (ZMod 11 × ZMod 11)
    (QuadraticAlgebra.equivProd (-1 : ZMod 11) 0).symm

/-- The residue of the Gaussian unit `i`. -/
def residueI : GaussianResidue11 := ⟨0, 1⟩

@[simp] theorem residueI_sq :
    residueI ^ 2 = (-1 : GaussianResidue11) := by
  apply QuadraticAlgebra.ext <;> native_decide

/-- Coordinatewise reduction of a Gaussian integer modulo the inert prime
`11`. -/
def residueHom : GaussianInt →+* GaussianResidue11 :=
  Zsqrtd.lift ⟨residueI, by simpa [pow_two] using residueI_sq⟩

@[simp] theorem residueHom_apply (z : GaussianInt) :
    residueHom z =
      (⟨(z.re : ZMod 11), (z.im : ZMod 11)⟩ :
        GaussianResidue11) := by
  apply QuadraticAlgebra.ext <;> simp [residueHom, residueI]

/-- The two specialized three-division quartics. -/
def threeDivisionValue
    (A B x : GaussianResidue11) : GaussianResidue11 :=
  3 * x ^ 4 + 4 * A * x ^ 3 + 6 * B * x ^ 2 - B ^ 2

/-- Closed no-root certificate for the `E₀` three-division quartic. -/
theorem e0_threeDivision_no_root :
    ∀ x : GaussianResidue11,
      threeDivisionValue (2 * residueI) (-2 - 4 * residueI) x ≠ 0 := by
  native_decide

/-- Closed no-root certificate for the `E₁` three-division quartic. -/
theorem e1_threeDivision_no_root :
    ∀ x : GaussianResidue11,
      threeDivisionValue 2 (2 + 4 * residueI) x ≠ 0 := by
  native_decide

private theorem gaussian11_prime :
    Prime (11 : GaussianInt) := by
  exact GaussianInt.prime_of_nat_prime_of_mod_four_eq_three
    11 (by norm_num)

/-- Reduction modulo `11` vanishes exactly on multiples of the inert
Gaussian prime. -/
theorem residueHom_eq_zero_iff (z : GaussianInt) :
    residueHom z = 0 ↔ (11 : GaussianInt) ∣ z := by
  constructor
  · intro hz
    have hre :
        (z.re : ZMod 11) = 0 := by
      have := congrArg QuadraticAlgebra.re hz
      simpa [residueHom_apply] using this
    have him :
        (z.im : ZMod 11) = 0 := by
      have := congrArg QuadraticAlgebra.im hz
      simpa [residueHom_apply] using this
    have hreDvd : (11 : ℤ) ∣ z.re :=
      (CharP.intCast_eq_zero_iff (ZMod 11) 11 z.re).mp hre
    have himDvd : (11 : ℤ) ∣ z.im :=
      (CharP.intCast_eq_zero_iff (ZMod 11) 11 z.im).mp him
    obtain ⟨a, ha⟩ := hreDvd
    obtain ⟨b, hb⟩ := himDvd
    refine ⟨(⟨a, b⟩ : GaussianInt), ?_⟩
    apply Zsqrtd.ext
    · simp [ha, mul_comm]
    · simp [hb, mul_comm]
  · rintro ⟨w, rfl⟩
    rw [map_mul]
    have h11 : residueHom (11 : GaussianInt) = 0 := by
      apply QuadraticAlgebra.ext
      · change (11 : ZMod 11) = 0
        native_decide
      · change (0 : ZMod 11) = 0
        rfl
    rw [h11, zero_mul]

/-- A root in `ℚ(i)` of an integral quartic whose leading coefficient is a
unit modulo `11` would reduce to a root in `𝔽₁₁(i)`. -/
theorem no_threeDivision_root_of_residue
    (a b : GaussianInt)
    (hfinite :
      ∀ r : GaussianResidue11,
        threeDivisionValue (residueHom a) (residueHom b) r ≠ 0) :
    ∀ x : GaussianRat,
      3 * x ^ 4 +
          4 * algebraMap GaussianInt GaussianRat a * x ^ 3 +
          6 * algebraMap GaussianInt GaussianRat b * x ^ 2 -
            (algebraMap GaussianInt GaussianRat b) ^ 2 ≠ 0 := by
  intro x hx
  let U : GaussianInt := IsFractionRing.num GaussianInt x
  let V : GaussianInt := IsFractionRing.den GaussianInt x
  have hV : V ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp
      (IsFractionRing.den GaussianInt x).2
  have hVK :
      algebraMap GaussianInt GaussianRat V ≠ 0 :=
    fun h ↦ hV <|
      FaithfulSMul.algebraMap_injective GaussianInt GaussianRat <| by
        simpa only [map_zero] using h
  have hxfrac :
      x =
        algebraMap GaussianInt GaussianRat U /
          algebraMap GaussianInt GaussianRat V :=
    (IsFractionRing.mk'_num_den' GaussianInt x).symm
  have hrel : IsRelPrime U V :=
    IsFractionRing.num_den_reduced GaussianInt x
  have hEqK :
      algebraMap GaussianInt GaussianRat
        (3 * U ^ 4 + 4 * a * U ^ 3 * V +
          6 * b * U ^ 2 * V ^ 2 - b ^ 2 * V ^ 4) = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
    rw [hxfrac] at hx
    field_simp [hVK] at hx ⊢
    linear_combination hx
  have hEq :
      3 * U ^ 4 + 4 * a * U ^ 3 * V +
          6 * b * U ^ 2 * V ^ 2 - b ^ 2 * V ^ 4 = 0 :=
    FaithfulSMul.algebraMap_injective GaussianInt GaussianRat
      (by simpa only [map_zero] using hEqK)
  have hresV : residueHom V ≠ 0 := by
    intro hzero
    have hEqRes := congrArg residueHom hEq
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat,
      map_zero, hzero, mul_zero, zero_pow (by norm_num : (4 : ℕ) ≠ 0),
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, add_zero] at hEqRes
    have hresU : residueHom U = 0 := by
      have h3 : (3 : GaussianResidue11) ≠ 0 := by native_decide
      exact (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp
        ((mul_eq_zero.mp hEqRes).resolve_left h3)
    have hqU : (11 : GaussianInt) ∣ U :=
      (residueHom_eq_zero_iff U).mp hresU
    have hqV : (11 : GaussianInt) ∣ V :=
      (residueHom_eq_zero_iff V).mp hzero
    exact gaussian11_prime.not_isUnit (hrel hqU hqV)
  have hEqRes := congrArg residueHom hEq
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat,
    map_zero] at hEqRes
  let r : GaussianResidue11 := residueHom U / residueHom V
  have hr :
      threeDivisionValue (residueHom a) (residueHom b) r = 0 := by
    dsimp only [r, threeDivisionValue]
    field_simp [hresV]
    linear_combination hEqRes
  exact hfinite r hr

/-- The affine abscissa of a nonzero point killed by `3` satisfies the
standard three-division quartic for `y² = x(x²+Ax+B)`. -/
theorem threeDivision_eq_zero_of_three_nsmul_eq_zero
    (A B : GaussianRat)
    {x y : GaussianRat}
    (hxy : (curve A B).toAffine.Nonsingular x y)
    (hthree :
      3 • (WeierstrassCurve.Affine.Point.some x y hxy :
        (curve A B).toAffine.Point) = 0) :
    3 * x ^ 4 + 4 * A * x ^ 3 + 6 * B * x ^ 2 - B ^ 2 = 0 := by
  let P : (curve A B).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some x y hxy
  have hdouble : P + P = -P := by
    apply add_right_cancel (b := P)
    simpa only [P, three_nsmul, neg_add_cancel, add_assoc] using hthree
  have hy : y ≠ 0 := by
    intro hy
    have hself : P + P = 0 := by
      apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
      simp [curve, WeierstrassCurve.Affine.negY, hy]
    have hPzero : P = 0 := by
      change 3 • P = 0 at hthree
      rw [three_nsmul, hself, add_zero] at hthree
      exact hthree
    exact WeierstrassCurve.Affine.Point.some_ne_zero hxy hPzero
  have hnegY :
      y ≠ (curve A B).toAffine.negY x y := by
    simp only [curve, WeierstrassCurve.Affine.negY, zero_mul,
      sub_zero]
    intro h
    apply hy
    have htwo : (2 : GaussianRat) * y = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  dsimp only [P] at hdouble
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hnegY] at hdouble
  have hxDouble :=
    (WeierstrassCurve.Affine.Point.some.inj hdouble).1
  have hcurve :
      y ^ 2 = x * (x ^ 2 + A * x + B) :=
    curve_equation_iff.mp hxy.1
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hnegY] at hxDouble
  simp only [curve, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY, zero_mul, sub_zero] at hxDouble
  field_simp [hy] at hxDouble
  linear_combination -hxDouble - 4 * (A + 3 * x) * hcurve

/-- Integral coefficient `2i` of `E₀`. -/
def e0AInt : GaussianInt := ⟨0, 2⟩

/-- Integral coefficient `2` of `E₁`. -/
def e1AInt : GaussianInt := ⟨2, 0⟩

@[simp] theorem algebraMap_e0AInt :
    algebraMap GaussianInt GaussianRat e0AInt = E0A := by
  rw [algebraMap_gaussianInt_apply]
  apply QuadraticAlgebra.ext <;>
    norm_num [e0AInt, E0A, gaussianI,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

@[simp] theorem algebraMap_e1AInt :
    algebraMap GaussianInt GaussianRat e1AInt = E1A := by
  rw [algebraMap_gaussianInt_apply]
  apply QuadraticAlgebra.ext <;>
    norm_num [e1AInt, E1A,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

private theorem residue_e0A :
    residueHom e0AInt = 2 * residueI := by
  apply QuadraticAlgebra.ext <;>
    norm_num [e0AInt, residueHom_apply, residueI,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

private theorem residue_e1A :
    residueHom e1AInt = 2 := by
  apply QuadraticAlgebra.ext <;>
    norm_num [e1AInt, residueHom_apply,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

private theorem residue_e0B :
    residueHom GaussianPrimes.e0BInt = -2 - 4 * residueI := by
  apply QuadraticAlgebra.ext <;>
    norm_num [GaussianPrimes.e0BInt, residueHom_apply, residueI,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

private theorem residue_e1B :
    residueHom GaussianPrimes.e1BInt = 2 + 4 * residueI := by
  apply QuadraticAlgebra.ext <;>
    norm_num [GaussianPrimes.e1BInt, residueHom_apply, residueI,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

/-- The `E₀` three-division quartic has no root in `ℚ(i)`. -/
theorem gaussianE0_threeDivision_no_root (x : GaussianRat) :
    3 * x ^ 4 + 4 * E0A * x ^ 3 + 6 * E0B * x ^ 2 - E0B ^ 2 ≠ 0 := by
  have hfinite :
      ∀ r : GaussianResidue11,
        threeDivisionValue
          (residueHom e0AInt)
          (residueHom GaussianPrimes.e0BInt) r ≠ 0 := by
    intro r
    rw [residue_e0A, residue_e0B]
    exact e0_threeDivision_no_root r
  simpa only [algebraMap_e0AInt, GaussianPrimes.algebraMap_e0BInt]
    using
      no_threeDivision_root_of_residue
        e0AInt GaussianPrimes.e0BInt hfinite x

/-- The `E₁` three-division quartic has no root in `ℚ(i)`. -/
theorem gaussianE1_threeDivision_no_root (x : GaussianRat) :
    3 * x ^ 4 + 4 * E1A * x ^ 3 + 6 * E1B * x ^ 2 - E1B ^ 2 ≠ 0 := by
  have hfinite :
      ∀ r : GaussianResidue11,
        threeDivisionValue
          (residueHom e1AInt)
          (residueHom GaussianPrimes.e1BInt) r ≠ 0 := by
    intro r
    rw [residue_e1A, residue_e1B]
    exact e1_threeDivision_no_root r
  simpa only [algebraMap_e1AInt, GaussianPrimes.algebraMap_e1BInt]
    using
      no_threeDivision_root_of_residue
        e1AInt GaussianPrimes.e1BInt hfinite x

/-- The actual group `E₀(ℚ(i))` has no nonzero point killed by `3`. -/
theorem gaussianE0_three_nsmul_eq_zero_iff
    (P : gaussianE0.toAffine.Point) :
    3 • P = 0 ↔ P = 0 := by
  constructor
  · intro hthree
    rcases P with (_ | ⟨x, y, hxy⟩)
    · rfl
    · exact
        (gaussianE0_threeDivision_no_root x
          (threeDivision_eq_zero_of_three_nsmul_eq_zero
            E0A E0B hxy hthree)).elim
  · rintro rfl
    exact nsmul_zero 3

/-- The actual group `E₁(ℚ(i))` has no nonzero point killed by `3`. -/
theorem gaussianE1_three_nsmul_eq_zero_iff
    (P : gaussianE1.toAffine.Point) :
    3 • P = 0 ↔ P = 0 := by
  constructor
  · intro hthree
    rcases P with (_ | ⟨x, y, hxy⟩)
    · rfl
    · exact
        (gaussianE1_threeDivision_no_root x
          (threeDivision_eq_zero_of_three_nsmul_eq_zero
            E1A E1B hxy hthree)).elim
  · rintro rfl
    exact nsmul_zero 3

end

end GaussianThreeTorsion
end Cuboid2
