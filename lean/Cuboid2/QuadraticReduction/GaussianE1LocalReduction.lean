import Cuboid2.QuadraticReduction.GaussianFiniteExponent
import Cuboid2.QuadraticReduction.GaussianProjectiveReductionHom

/-!
# The two actual split-37 local models of the rank-zero Gaussian curve

This file base-changes `E₁(ℚ(i))` through the same two embeddings used for
`E₀`, transports the points to the generic integral local models, and defines
their executable projective reductions.  Additivity of those reductions is
supplied separately by the generic formal-kernel theorem.
-/

namespace Cuboid2
namespace GaussianE1LocalReduction

noncomputable section

open GaussianGoodReduction GaussianProjectiveReduction
  GaussianProjectiveReductionHom GaussianFinite GaussianFiniteExponent

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have hxnonneg : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : DecidableEq ℚ_[37] := Classical.decEq _

/-- Integral coefficients of the plus local `E₁` model. -/
def plusA : ℤ_[37] := 2

def plusB : ℤ_[37] := 2 + 4 * splitRootPlus

/-- Integral coefficients of the minus local `E₁` model. -/
def minusA : ℤ_[37] := 2

def minusB : ℤ_[37] := 2 + 4 * splitRootMinus

def integralPlus : WeierstrassCurve ℤ_[37] where
  a₁ := 0
  a₂ := plusA
  a₃ := 0
  a₄ := plusB
  a₆ := 0

def integralMinus : WeierstrassCurve ℤ_[37] where
  a₁ := 0
  a₂ := minusA
  a₃ := 0
  a₄ := minusB
  a₆ := 0

private theorem plusResidue_discriminant_ne_zero :
    (localResidueCurve plusA plusB).Δ ≠ 0 := by
  simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    localResidueCurve, localCurve, plusA, plusB, splitRootPlus_toZMod]
  simp only [map_ofNat]
  native_decide

private theorem minusResidue_discriminant_ne_zero :
    (localResidueCurve minusA minusB).Δ ≠ 0 := by
  simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    localResidueCurve, localCurve, minusA, minusB, splitRootMinus_toZMod]
  simp only [map_ofNat]
  native_decide

instance plusResidue_isElliptic :
    (localResidueCurve plusA plusB).IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr plusResidue_discriminant_ne_zero

instance minusResidue_isElliptic :
    (localResidueCurve minusA minusB).IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr minusResidue_discriminant_ne_zero

abbrev gaussianE1PadicPlus : WeierstrassCurve ℚ_[37] :=
  gaussianE1.map gaussianToPadicPlus.toRingHom

abbrev gaussianE1PadicMinus : WeierstrassCurve ℚ_[37] :=
  gaussianE1.map gaussianToPadicMinus.toRingHom

/-- The displayed plus integral model base-changes to the actual curve. -/
theorem integralPlus_baseChange :
    integralPlus.map (algebraMap ℤ_[37] ℚ_[37]) =
      gaussianE1PadicPlus := by
  ext <;>
    simp [integralPlus, gaussianE1PadicPlus, gaussianE1,
      plusA, plusB, gaussianToPadicPlus_i, PadicInt.algebraMap_apply]
  · exact PadicInt.coe_natCast (p := 37) 2
  · rw [show ((2 : ℤ_[37]) : ℚ_[37]) = 2 from
        PadicInt.coe_natCast (p := 37) 2,
      show ((4 : ℤ_[37]) : ℚ_[37]) = 4 from
        PadicInt.coe_natCast (p := 37) 4]

/-- The displayed minus integral model base-changes to the actual curve. -/
theorem integralMinus_baseChange :
    integralMinus.map (algebraMap ℤ_[37] ℚ_[37]) =
      gaussianE1PadicMinus := by
  ext <;>
    simp [integralMinus, gaussianE1PadicMinus, gaussianE1,
      minusA, minusB, gaussianToPadicMinus_i, PadicInt.algebraMap_apply]
  · exact PadicInt.coe_natCast (p := 37) 2
  · rw [show ((2 : ℤ_[37]) : ℚ_[37]) = 2 from
        PadicInt.coe_natCast (p := 37) 2,
      show ((4 : ℤ_[37]) : ℚ_[37]) = 4 from
        PadicInt.coe_natCast (p := 37) 4]

/-- The displayed plus local model is the actual base change of `E₁`. -/
theorem gaussianE1PadicPlus_eq_local :
    gaussianE1PadicPlus = localPadicCurve plusA plusB := by
  exact integralPlus_baseChange.symm

/-- The displayed minus local model is the actual base change of `E₁`. -/
theorem gaussianE1PadicMinus_eq_local :
    gaussianE1PadicMinus = localPadicCurve minusA minusB := by
  exact integralMinus_baseChange.symm

/-- Actual base change through the plus split embedding. -/
def mapE1PointPlus :
    gaussianE1.toAffine.Point →+ gaussianE1PadicPlus.toAffine.Point := by
  letI : Algebra GaussianRat ℚ_[37] :=
    gaussianToPadicPlus.toRingHom.toAlgebra
  exact
    WeierstrassCurve.Affine.Point.map
      (W' := gaussianE1.toAffine)
      (R := GaussianRat) (S := GaussianRat)
      (F := GaussianRat) (K := ℚ_[37])
      (Algebra.ofId GaussianRat ℚ_[37])

/-- Actual base change through the minus split embedding. -/
def mapE1PointMinus :
    gaussianE1.toAffine.Point →+ gaussianE1PadicMinus.toAffine.Point := by
  letI : Algebra GaussianRat ℚ_[37] :=
    gaussianToPadicMinus.toRingHom.toAlgebra
  exact
    WeierstrassCurve.Affine.Point.map
      (W' := gaussianE1.toAffine)
      (R := GaussianRat) (S := GaussianRat)
      (F := GaussianRat) (K := ℚ_[37])
      (Algebra.ofId GaussianRat ℚ_[37])

/-- Plus base change transported to the generic local model. -/
def mapE1PointPlusLocal
    (Q : gaussianE1.toAffine.Point) :
    (localPadicCurve plusA plusB).toAffine.Point :=
  castPoint gaussianE1PadicPlus_eq_local (mapE1PointPlus Q)

/-- Minus base change transported to the generic local model. -/
def mapE1PointMinusLocal
    (Q : gaussianE1.toAffine.Point) :
    (localPadicCurve minusA minusB).toAffine.Point :=
  castPoint gaussianE1PadicMinus_eq_local (mapE1PointMinus Q)

/-- Executable projective plus reduction of an actual `E₁` point. -/
def reduceE1Plus (Q : gaussianE1.toAffine.Point) : FinitePoint :=
  finiteReducePoint plusA plusB (mapE1PointPlusLocal Q)

/-- Executable projective minus reduction of an actual `E₁` point. -/
def reduceE1Minus (Q : gaussianE1.toAffine.Point) : FinitePoint :=
  finiteReducePoint minusA minusB (mapE1PointMinusLocal Q)

private theorem castPoint_some_exists
    {W V : WeierstrassCurve ℚ_[37]} (h : W = V)
    {x y : ℚ_[37]} (hxy : W.toAffine.Nonsingular x y) :
    ∃ hxy' : V.toAffine.Nonsingular x y,
      castPoint h (.some x y hxy) = .some x y hxy' := by
  subst V
  exact ⟨hxy, rfl⟩

private theorem mapE1PointPlus_gaussianE1T_exists :
    ∃ hxy : gaussianE1PadicPlus.toAffine.Nonsingular 0 0,
      mapE1PointPlus gaussianE1T = .some 0 0 hxy := by
  have hxy : gaussianE1PadicPlus.toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp [gaussianE1PadicPlus, gaussianE1])
  unfold mapE1PointPlus gaussianE1T
  refine ⟨hxy, ?_⟩
  change
    WeierstrassCurve.Affine.Point.some
        (gaussianToPadicPlus (0 : GaussianRat))
        (gaussianToPadicPlus (0 : GaussianRat)) _ =
      WeierstrassCurve.Affine.Point.some 0 0 _
  congr 1 <;> simp

private theorem mapE1PointMinus_gaussianE1T_exists :
    ∃ hxy : gaussianE1PadicMinus.toAffine.Nonsingular 0 0,
      mapE1PointMinus gaussianE1T = .some 0 0 hxy := by
  have hxy : gaussianE1PadicMinus.toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp [gaussianE1PadicMinus, gaussianE1])
  unfold mapE1PointMinus gaussianE1T
  refine ⟨hxy, ?_⟩
  change
    WeierstrassCurve.Affine.Point.some
        (gaussianToPadicMinus (0 : GaussianRat))
        (gaussianToPadicMinus (0 : GaussianRat)) _ =
      WeierstrassCurve.Affine.Point.some 0 0 _
  congr 1 <;> simp

/-- The local coefficient residues are exactly the executable finite rows. -/
theorem plus_coefficients :
    (PadicInt.toZMod plusA).val = e1PlusCoefficients.1 ∧
      (PadicInt.toZMod plusB).val = e1PlusCoefficients.2 := by
  have hA : PadicInt.toZMod plusA = (2 : ZMod 37) := by
    simp only [plusA, map_ofNat]
  have hB : PadicInt.toZMod plusB = (26 : ZMod 37) := by
    rw [plusB, map_add, map_mul, splitRootPlus_toZMod]
    simp only [map_ofNat]
    native_decide
  rw [hA, hB]
  native_decide

theorem minus_coefficients :
    (PadicInt.toZMod minusA).val = e1MinusCoefficients.1 ∧
      (PadicInt.toZMod minusB).val = e1MinusCoefficients.2 := by
  have hA : PadicInt.toZMod minusA = (2 : ZMod 37) := by
    simp only [minusA, map_ofNat]
  have hB : PadicInt.toZMod minusB = (15 : ZMod 37) := by
    rw [minusB, map_add, map_mul, splitRootMinus_toZMod]
    simp only [map_ofNat]
    native_decide
  rw [hA, hB]
  native_decide

@[simp] theorem mapE1PointPlusLocal_zero :
    mapE1PointPlusLocal 0 = 0 := by
  rw [mapE1PointPlusLocal, map_zero, castPoint_zero]

@[simp] theorem mapE1PointMinusLocal_zero :
    mapE1PointMinusLocal 0 = 0 := by
  rw [mapE1PointMinusLocal, map_zero, castPoint_zero]

theorem mapE1PointPlusLocal_add
    (Q R : gaussianE1.toAffine.Point) :
    mapE1PointPlusLocal (Q + R) =
      mapE1PointPlusLocal Q + mapE1PointPlusLocal R := by
  change castPoint _ (mapE1PointPlus (Q + R)) =
    castPoint _ (mapE1PointPlus Q) + castPoint _ (mapE1PointPlus R)
  rw [map_add, castPoint_add]

theorem mapE1PointMinusLocal_add
    (Q R : gaussianE1.toAffine.Point) :
    mapE1PointMinusLocal (Q + R) =
      mapE1PointMinusLocal Q + mapE1PointMinusLocal R := by
  change castPoint _ (mapE1PointMinus (Q + R)) =
    castPoint _ (mapE1PointMinus Q) + castPoint _ (mapE1PointMinus R)
  rw [map_add, castPoint_add]

theorem mapE1PointPlusLocal_neg
    (Q : gaussianE1.toAffine.Point) :
    mapE1PointPlusLocal (-Q) = -mapE1PointPlusLocal Q := by
  change castPoint _ (mapE1PointPlus (-Q)) =
    -castPoint _ (mapE1PointPlus Q)
  rw [map_neg, castPoint_neg]

theorem mapE1PointMinusLocal_neg
    (Q : gaussianE1.toAffine.Point) :
    mapE1PointMinusLocal (-Q) = -mapE1PointMinusLocal Q := by
  change castPoint _ (mapE1PointMinus (-Q)) =
    -castPoint _ (mapE1PointMinus Q)
  rw [map_neg, castPoint_neg]

@[simp] theorem reduceE1Plus_zero :
    reduceE1Plus 0 = none := by
  rw [reduceE1Plus, mapE1PointPlusLocal_zero, finiteReducePoint_zero]

@[simp] theorem reduceE1Minus_zero :
    reduceE1Minus 0 = none := by
  rw [reduceE1Minus, mapE1PointMinusLocal_zero, finiteReducePoint_zero]

/-- The named two-torsion point reduces to `(0,0)` at both split primes. -/
theorem reduceE1Plus_gaussianE1T :
    reduceE1Plus gaussianE1T = some (0, 0) := by
  obtain ⟨hxy, hmap⟩ := mapE1PointPlus_gaussianE1T_exists
  obtain ⟨hxy', hcast⟩ :=
    castPoint_some_exists gaussianE1PadicPlus_eq_local hxy
  rw [reduceE1Plus, mapE1PointPlusLocal, hmap, hcast]
  simp [finiteReducePoint, reducePoint, finitePointOfResidue,
    WeierstrassCurve.Affine.Point.mk]

theorem reduceE1Minus_gaussianE1T :
    reduceE1Minus gaussianE1T = some (0, 0) := by
  obtain ⟨hxy, hmap⟩ := mapE1PointMinus_gaussianE1T_exists
  obtain ⟨hxy', hcast⟩ :=
    castPoint_some_exists gaussianE1PadicMinus_eq_local hxy
  rw [reduceE1Minus, mapE1PointMinusLocal, hmap, hcast]
  simp [finiteReducePoint, reducePoint, finitePointOfResidue,
    WeierstrassCurve.Affine.Point.mk]

end

end GaussianE1LocalReduction
end Cuboid2
