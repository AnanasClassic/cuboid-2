import Cuboid2.QuadraticReduction.GaussianProjectiveReductionHom

/-!
# Actual reductions of the visible Gaussian points

This file evaluates the specialized projective reduction on the two displayed
global points `P = (2,2)` and `T = (0,0)`.  These are direct coordinate
computations and do not use an assumed reduction homomorphism.
-/

namespace Cuboid2
namespace GaussianVisibleReduction

noncomputable section

open GaussianGoodReduction
open GaussianProjectiveReduction
open GaussianP37Bridge

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

/-- The explicit translate `P+T` on the global Gaussian curve. -/
def gaussianE0PaddT : gaussianE0.toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk
    (x := -1 - 2 * gaussianI) (y := 1 + 2 * gaussianI) (by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp [gaussianE0, gaussianI_sq]
      ring)

/-- Direct characteristic-zero addition of the two displayed points. -/
theorem gaussianE0P_add_gaussianE0T :
    gaussianE0P + gaussianE0T = gaussianE0PaddT := by
  change
    (WeierstrassCurve.Affine.Point.some (2 : GaussianRat) 2 _) +
        (WeierstrassCurve.Affine.Point.some 0 0 _) =
      gaussianE0PaddT
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num)]
  change
    WeierstrassCurve.Affine.Point.some
        (gaussianE0.toAffine.addX 2 0
          (gaussianE0.toAffine.slope 2 0 2 0))
        (gaussianE0.toAffine.addY 2 0 2
          (gaussianE0.toAffine.slope 2 0 2 0)) _ =
      WeierstrassCurve.Affine.Point.some
        (-1 - 2 * gaussianI) (1 + 2 * gaussianI) _
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · simp [gaussianE0PaddT, gaussianE0,
      WeierstrassCurve.Affine.slope_of_X_ne]
    ring
  · simp [gaussianE0PaddT, gaussianE0,
      WeierstrassCurve.Affine.slope_of_X_ne,
      WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY]
    ring

private theorem castPoint_some_exists
    {W V : WeierstrassCurve ℚ_[37]} (h : W = V)
    {x y : ℚ_[37]} (hxy : W.toAffine.Nonsingular x y) :
    ∃ hxy' : V.toAffine.Nonsingular x y,
      castPoint h (.some x y hxy) = .some x y hxy' := by
  subst V
  exact ⟨hxy, rfl⟩

/-- Evaluation of projective reduction on a point already presented with
integral affine coordinates. -/
theorem finiteReducePoint_some_coe
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (x y : ℤ_[37])
    (hxy :
      (localPadicCurve A B).toAffine.Nonsingular
        (x : ℚ_[37]) (y : ℚ_[37])) :
    finiteReducePoint A B
        (.some (x : ℚ_[37]) (y : ℚ_[37]) hxy) =
      some ((PadicInt.toZMod x).val, (PadicInt.toZMod y).val) := by
  have hx : ‖(x : ℚ_[37])‖ ≤ 1 := x.property
  unfold finiteReducePoint
  simp only [reducePoint]
  rw [dif_pos hx]
  simp only [finitePointOfResidue,
    WeierstrassCurve.Affine.Point.mk]
  have hxInt :
      (⟨(x : ℚ_[37]), hx⟩ : ℤ_[37]) = x :=
    Subtype.ext rfl
  have hy :
      ‖(y : ℚ_[37])‖ ≤ 1 :=
    norm_y_le_one_of_norm_x_le_one A B hxy.1 hx
  have hyInt :
      (⟨(y : ℚ_[37]), hy⟩ : ℤ_[37]) = y :=
    Subtype.ext rfl
  rw [hxInt, hyInt]

private theorem mapE0PointPlus_gaussianE0P_exists :
    ∃ hxy : gaussianE0PadicPlus.toAffine.Nonsingular 2 2,
      mapE0PointPlus gaussianE0P = .some 2 2 hxy := by
  have hxy : gaussianE0PadicPlus.toAffine.Nonsingular 2 2 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp [gaussianE0PadicPlus, gaussianE0]
      ring)
  unfold mapE0PointPlus gaussianE0P
  refine ⟨hxy, ?_⟩
  change
    WeierstrassCurve.Affine.Point.some
        (gaussianToPadicPlus (2 : GaussianRat))
        (gaussianToPadicPlus (2 : GaussianRat)) _ =
      WeierstrassCurve.Affine.Point.some 2 2 _
  congr 1 <;> simp

private theorem mapE0PointMinus_gaussianE0P_exists :
    ∃ hxy : gaussianE0PadicMinus.toAffine.Nonsingular 2 2,
      mapE0PointMinus gaussianE0P = .some 2 2 hxy := by
  have hxy : gaussianE0PadicMinus.toAffine.Nonsingular 2 2 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp [gaussianE0PadicMinus, gaussianE0]
      ring)
  unfold mapE0PointMinus gaussianE0P
  refine ⟨hxy, ?_⟩
  change
    WeierstrassCurve.Affine.Point.some
        (gaussianToPadicMinus (2 : GaussianRat))
        (gaussianToPadicMinus (2 : GaussianRat)) _ =
      WeierstrassCurve.Affine.Point.some 2 2 _
  congr 1 <;> simp

private theorem mapE0PointPlus_gaussianE0T_exists :
    ∃ hxy : gaussianE0PadicPlus.toAffine.Nonsingular 0 0,
      mapE0PointPlus gaussianE0T = .some 0 0 hxy := by
  have hxy : gaussianE0PadicPlus.toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp [gaussianE0PadicPlus, gaussianE0])
  unfold mapE0PointPlus gaussianE0T
  refine ⟨hxy, ?_⟩
  change
    WeierstrassCurve.Affine.Point.some
        (gaussianToPadicPlus (0 : GaussianRat))
        (gaussianToPadicPlus (0 : GaussianRat)) _ =
      WeierstrassCurve.Affine.Point.some 0 0 _
  congr 1 <;> simp

private theorem mapE0PointMinus_gaussianE0T_exists :
    ∃ hxy : gaussianE0PadicMinus.toAffine.Nonsingular 0 0,
      mapE0PointMinus gaussianE0T = .some 0 0 hxy := by
  have hxy : gaussianE0PadicMinus.toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp [gaussianE0PadicMinus, gaussianE0])
  unfold mapE0PointMinus gaussianE0T
  refine ⟨hxy, ?_⟩
  change
    WeierstrassCurve.Affine.Point.some
        (gaussianToPadicMinus (0 : GaussianRat))
        (gaussianToPadicMinus (0 : GaussianRat)) _ =
      WeierstrassCurve.Affine.Point.some 0 0 _
  congr 1 <;> simp

/-- The visible point reduces to `(2,2)` at the plus prime above `37`. -/
theorem reduceE0Plus_gaussianE0P :
    reduceE0Plus gaussianE0P = some (2, 2) := by
  obtain ⟨hxy, hmap⟩ := mapE0PointPlus_gaussianE0P_exists
  obtain ⟨hxy', hcast⟩ :=
    castPoint_some_exists localPadicCurve_plus_eq.symm hxy
  rw [reduceE0Plus, mapE0PointPlusLocal, hmap, hcast]
  have hnorm : ‖(2 : ℚ_[37])‖ ≤ 1 :=
    Padic.norm_int_le_one (p := 37) 2
  have htwo :
      (⟨(2 : ℚ_[37]), hnorm⟩ : ℤ_[37]) =
        ((2 : ℕ) : ℤ_[37]) := by
    apply PadicInt.ext
    exact (PadicInt.coe_natCast 2).symm
  simp [finiteReducePoint, reducePoint, finitePointOfResidue, hnorm,
    WeierstrassCurve.Affine.Point.mk, htwo,
    PadicInt.val_toZMod_eq_zmodRepr]
  exact PadicInt.zmodRepr_natCast_of_lt (p := 37) (n := 2) (by norm_num)

/-- The visible point reduces to `(2,2)` at the minus prime above `37`. -/
theorem reduceE0Minus_gaussianE0P :
    reduceE0Minus gaussianE0P = some (2, 2) := by
  obtain ⟨hxy, hmap⟩ := mapE0PointMinus_gaussianE0P_exists
  obtain ⟨hxy', hcast⟩ :=
    castPoint_some_exists localPadicCurve_minus_eq.symm hxy
  rw [reduceE0Minus, mapE0PointMinusLocal, hmap, hcast]
  have hnorm : ‖(2 : ℚ_[37])‖ ≤ 1 :=
    Padic.norm_int_le_one (p := 37) 2
  have htwo :
      (⟨(2 : ℚ_[37]), hnorm⟩ : ℤ_[37]) =
        ((2 : ℕ) : ℤ_[37]) := by
    apply PadicInt.ext
    exact (PadicInt.coe_natCast 2).symm
  simp [finiteReducePoint, reducePoint, finitePointOfResidue, hnorm,
    WeierstrassCurve.Affine.Point.mk, htwo,
    PadicInt.val_toZMod_eq_zmodRepr]
  exact PadicInt.zmodRepr_natCast_of_lt (p := 37) (n := 2) (by norm_num)

/-- The named two-torsion point reduces to `(0,0)` at the plus prime. -/
theorem reduceE0Plus_gaussianE0T :
    reduceE0Plus gaussianE0T = some (0, 0) := by
  obtain ⟨hxy, hmap⟩ := mapE0PointPlus_gaussianE0T_exists
  obtain ⟨hxy', hcast⟩ :=
    castPoint_some_exists localPadicCurve_plus_eq.symm hxy
  rw [reduceE0Plus, mapE0PointPlusLocal, hmap, hcast]
  simp [finiteReducePoint, reducePoint, finitePointOfResidue,
    WeierstrassCurve.Affine.Point.mk]

/-- The named two-torsion point reduces to `(0,0)` at the minus prime. -/
theorem reduceE0Minus_gaussianE0T :
    reduceE0Minus gaussianE0T = some (0, 0) := by
  obtain ⟨hxy, hmap⟩ := mapE0PointMinus_gaussianE0T_exists
  obtain ⟨hxy', hcast⟩ :=
    castPoint_some_exists localPadicCurve_minus_eq.symm hxy
  rw [reduceE0Minus, mapE0PointMinusLocal, hmap, hcast]
  simp [finiteReducePoint, reducePoint, finitePointOfResidue,
    WeierstrassCurve.Affine.Point.mk]

/-- Integral plus-prime coordinates of `P+T`. -/
def plusPaddTX : ℤ_[37] := -1 - 2 * splitRootPlus

/-- Integral plus-prime ordinate of `P+T`. -/
def plusPaddTY : ℤ_[37] := 1 + 2 * splitRootPlus

private theorem mapE0PointPlus_gaussianE0PaddT_exists :
    ∃ hxy :
        gaussianE0PadicPlus.toAffine.Nonsingular
          (plusPaddTX : ℚ_[37]) (plusPaddTY : ℚ_[37]),
      mapE0PointPlus gaussianE0PaddT =
        .some (plusPaddTX : ℚ_[37]) (plusPaddTY : ℚ_[37]) hxy := by
  have hxy :
      gaussianE0PadicPlus.toAffine.Nonsingular
        (plusPaddTX : ℚ_[37]) (plusPaddTY : ℚ_[37]) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp [gaussianE0PadicPlus, gaussianE0, plusPaddTX, plusPaddTY]
      rw [show ((2 : ℤ_[37]) : ℚ_[37]) = 2 from
        PadicInt.coe_natCast 2]
      ring)
  unfold mapE0PointPlus gaussianE0PaddT
  refine ⟨hxy, ?_⟩
  change
    WeierstrassCurve.Affine.Point.some
        (gaussianToPadicPlus (-1 - 2 * gaussianI))
        (gaussianToPadicPlus (1 + 2 * gaussianI)) _ =
      WeierstrassCurve.Affine.Point.some
        (plusPaddTX : ℚ_[37]) (plusPaddTY : ℚ_[37]) _
  congr 1 <;>
    simp [plusPaddTX, plusPaddTY, PadicInt.coe_neg,
      PadicInt.coe_sub, PadicInt.coe_add, PadicInt.coe_mul,
      show ((2 : ℤ_[37]) : ℚ_[37]) = 2 from
        PadicInt.coe_natCast 2]

/-- Direct plus-prime reduction of the visible torsion translate. -/
theorem reduceE0Plus_gaussianE0PaddT :
    reduceE0Plus gaussianE0PaddT = some (24, 13) := by
  obtain ⟨hxy, hmap⟩ := mapE0PointPlus_gaussianE0PaddT_exists
  obtain ⟨hxy', hcast⟩ :=
    castPoint_some_exists localPadicCurve_plus_eq.symm hxy
  have hxRed :
      PadicInt.toZMod plusPaddTX = (24 : ZMod 37) := by
    simp only [plusPaddTX, map_sub, map_neg, map_one, map_mul,
      map_ofNat, splitRootPlus_toZMod]
    native_decide
  have hyRed :
      PadicInt.toZMod plusPaddTY = (13 : ZMod 37) := by
    simp only [plusPaddTY, map_add, map_one, map_mul,
      map_ofNat, splitRootPlus_toZMod]
    native_decide
  rw [reduceE0Plus, mapE0PointPlusLocal, hmap, hcast,
    finiteReducePoint_some_coe, hxRed, hyRed]
  native_decide

/-- Integral minus-prime coordinates of `P+T`. -/
def minusPaddTX : ℤ_[37] := -1 - 2 * splitRootMinus

/-- Integral minus-prime ordinate of `P+T`. -/
def minusPaddTY : ℤ_[37] := 1 + 2 * splitRootMinus

private theorem mapE0PointMinus_gaussianE0PaddT_exists :
    ∃ hxy :
        gaussianE0PadicMinus.toAffine.Nonsingular
          (minusPaddTX : ℚ_[37]) (minusPaddTY : ℚ_[37]),
      mapE0PointMinus gaussianE0PaddT =
        .some (minusPaddTX : ℚ_[37]) (minusPaddTY : ℚ_[37]) hxy := by
  have hxy :
      gaussianE0PadicMinus.toAffine.Nonsingular
        (minusPaddTX : ℚ_[37]) (minusPaddTY : ℚ_[37]) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp [gaussianE0PadicMinus, gaussianE0, minusPaddTX, minusPaddTY]
      rw [show ((2 : ℤ_[37]) : ℚ_[37]) = 2 from
        PadicInt.coe_natCast 2]
      ring)
  unfold mapE0PointMinus gaussianE0PaddT
  refine ⟨hxy, ?_⟩
  change
    WeierstrassCurve.Affine.Point.some
        (gaussianToPadicMinus (-1 - 2 * gaussianI))
        (gaussianToPadicMinus (1 + 2 * gaussianI)) _ =
      WeierstrassCurve.Affine.Point.some
        (minusPaddTX : ℚ_[37]) (minusPaddTY : ℚ_[37]) _
  congr 1 <;>
    simp [minusPaddTX, minusPaddTY, PadicInt.coe_neg,
      PadicInt.coe_sub, PadicInt.coe_add, PadicInt.coe_mul,
      show ((2 : ℤ_[37]) : ℚ_[37]) = 2 from
        PadicInt.coe_natCast 2]

/-- Direct minus-prime reduction of the visible torsion translate. -/
theorem reduceE0Minus_gaussianE0PaddT :
    reduceE0Minus gaussianE0PaddT = some (11, 26) := by
  obtain ⟨hxy, hmap⟩ := mapE0PointMinus_gaussianE0PaddT_exists
  obtain ⟨hxy', hcast⟩ :=
    castPoint_some_exists localPadicCurve_minus_eq.symm hxy
  have hxRed :
      PadicInt.toZMod minusPaddTX = (11 : ZMod 37) := by
    simp only [minusPaddTX, map_sub, map_neg, map_one, map_mul,
      map_ofNat, splitRootMinus_toZMod]
    native_decide
  have hyRed :
      PadicInt.toZMod minusPaddTY = (26 : ZMod 37) := by
    simp only [minusPaddTY, map_add, map_one, map_mul,
      map_ofNat, splitRootMinus_toZMod]
    native_decide
  rw [reduceE0Minus, mapE0PointMinusLocal, hmap, hcast,
    finiteReducePoint_some_coe, hxRed, hyRed]
  native_decide

/-- The negative visible point has the expected plus-prime residue. -/
theorem reduceE0Plus_neg_gaussianE0P :
    reduceE0Plus (-gaussianE0P) = some (2, 35) := by
  rw [GaussianProjectiveReductionHom.reduceE0Plus_neg,
    reduceE0Plus_gaussianE0P]
  native_decide

/-- The negative visible point has the expected minus-prime residue. -/
theorem reduceE0Minus_neg_gaussianE0P :
    reduceE0Minus (-gaussianE0P) = some (2, 35) := by
  rw [GaussianProjectiveReductionHom.reduceE0Minus_neg,
    reduceE0Minus_gaussianE0P]
  native_decide

end

end GaussianVisibleReduction
end Cuboid2
