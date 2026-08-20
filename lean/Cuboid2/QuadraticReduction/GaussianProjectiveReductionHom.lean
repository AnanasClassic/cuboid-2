import Cuboid2.QuadraticReduction.GaussianProjectiveReduction

/-!
# Group-law compatibility of specialized projective reduction

This module proves zero and negation compatibility for the concrete
normalization map defined in `GaussianProjectiveReduction`, together with the
zero-input and inverse-pair cases of addition.  It also proves that both actual
split base-change maps preserve addition before reduction.

General additivity of `reducePoint` is not asserted here: its remaining cases
are precisely the projective valuation argument showing that the infinity
disk is a subgroup and the coincident-reduction argument for integral points.
-/

namespace Cuboid2
namespace GaussianProjectiveReductionHom

noncomputable section

open GaussianProjectiveReduction
open GaussianGoodReduction
open GaussianFinite
open GaussianP37Bridge
open GaussianP37

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : DecidableEq ℚ_[37] := Classical.decEq _

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have hxnonneg : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

/-- Projective reduction commutes with negation on every integral
two-torsion model over `ℤ_[37]`. -/
theorem reducePoint_neg
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : (localPadicCurve A B).toAffine.Point) :
    reducePoint A B (-P) = -reducePoint A B P := by
  rcases P with (_ | ⟨x, y, hxy⟩)
  · rfl
  · rw [WeierstrassCurve.Affine.Point.neg_some]
    by_cases hx : ‖x‖ ≤ 1
    · simp [reducePoint, hx, localPadicCurve, localResidueCurve, localCurve,
        WeierstrassCurve.Affine.Point.mk]
      change WeierstrassCurve.Affine.Point.some _ _ _ =
        WeierstrassCurve.Affine.Point.some _ _ _
      congr 1
      simp only [WeierstrassCurve.Affine.negY, localResidueCurve, localCurve,
        WeierstrassCurve.map, map_zero, zero_mul, sub_zero]
      let yInt : ℤ_[37] :=
        ⟨y, norm_y_le_one_of_norm_x_le_one A B hxy.1 hx⟩
      let negYInt : ℤ_[37] := ⟨-y, by simpa [yInt] using yInt.property⟩
      change PadicInt.toZMod negYInt = -PadicInt.toZMod yInt
      rw [show negYInt = -yInt by
        apply PadicInt.ext
        rw [PadicInt.coe_neg], map_neg]
    · simp [reducePoint, hx]

/-- Forgetting the proof and choosing canonical representatives converts
geometric negation on a residue point into the executable `finiteNeg`. -/
theorem finitePointOfResidue_neg
    (A B : ℤ_[37])
    [_hEll : (localResidueCurve A B).IsElliptic]
    (P : (localResidueCurve A B).toAffine.Point) :
    finitePointOfResidue (-P) =
      finiteNeg 37 (finitePointOfResidue P) := by
  rcases P with (_ | ⟨x, y, hxy⟩)
  · rfl
  · rw [WeierstrassCurve.Affine.Point.neg_some]
    simp only [finitePointOfResidue, finiteNeg, localResidueCurve, localCurve,
      WeierstrassCurve.map, WeierstrassCurve.Affine.negY, map_zero, zero_mul,
      sub_zero]
    congr 2
    by_cases hy : y = 0
    · subst y
      simp [residueSub]
    · let _ : NeZero y := ⟨hy⟩
      rw [ZMod.val_neg_of_ne_zero]
      have hylt : y.val < 37 := ZMod.val_lt y
      have hyval : y.val ≠ 0 := fun h =>
        hy ((ZMod.val_eq_zero y).mp h)
      have hypos : 0 < y.val := by
        omega
      have hsub : 37 - y.val < 37 := by
        omega
      simp [residueSub, Nat.mod_eq_of_lt hylt, Nat.mod_eq_of_lt hsub]

/-- Executable projective reduction commutes with finite negation. -/
theorem finiteReducePoint_neg
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : (localPadicCurve A B).toAffine.Point) :
    finiteReducePoint A B (-P) =
      finiteNeg 37 (finiteReducePoint A B P) := by
  change finitePointOfResidue (reducePoint A B (-P)) =
    finiteNeg 37 (finitePointOfResidue (reducePoint A B P))
  rw [reducePoint_neg, finitePointOfResidue_neg]

/-- The executable addition law cancels a canonical residue point with its
executable negation.  The curve coefficients are irrelevant in this vertical
line case. -/
theorem finiteAdd_finiteNeg_finitePointOfResidue
    {W : WeierstrassCurve (ZMod 37)} (C D : ℕ)
    (P : W.toAffine.Point) :
    finiteAdd 37 C D (finitePointOfResidue P)
      (finiteNeg 37 (finitePointOfResidue P)) = none := by
  rcases P with (_ | ⟨x, y, hxy⟩)
  · rfl
  · have hxlt : x.val < 37 := ZMod.val_lt x
    have hylt : y.val < 37 := ZMod.val_lt y
    have hsum :
        (y.val + residueSub 37 0 y.val) % 37 = 0 := by
      by_cases hy : y.val = 0
      · simp [hy, residueSub]
      · have hypos : 0 < y.val := Nat.pos_of_ne_zero hy
        have hsub : 37 - y.val < 37 := by omega
        simp only [residueSub, Nat.zero_mod, Nat.zero_add,
          Nat.mod_eq_of_lt hylt, Nat.mod_eq_of_lt hsub]
        omega
    simp [finitePointOfResidue, finiteNeg, finiteAdd,
      Nat.mod_eq_of_lt hxlt, hsum]

/-- Reduction respects the addition of a point and its inverse.  This is the
vertical-line part of additivity and uses no valuation case split. -/
theorem reducePoint_add_neg
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : (localPadicCurve A B).toAffine.Point) :
    reducePoint A B (P + -P) =
      reducePoint A B P + reducePoint A B (-P) := by
  rw [add_neg_cancel, reducePoint_zero, reducePoint_neg, add_neg_cancel]

/-- The executable reduction satisfies the corresponding inverse-pair
addition formula. -/
theorem finiteReducePoint_add_neg
    (A B : ℤ_[37]) (C D : ℕ)
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : (localPadicCurve A B).toAffine.Point) :
    finiteReducePoint A B (P + -P) =
      finiteAdd 37 C D (finiteReducePoint A B P)
        (finiteReducePoint A B (-P)) := by
  rw [add_neg_cancel, finiteReducePoint_zero, finiteReducePoint_neg]
  exact
    (finiteAdd_finiteNeg_finitePointOfResidue C D
      (reducePoint A B P)).symm

/-! ## The two actual split maps -/

/-- Transport across equality of Weierstrass models preserves zero. -/
@[simp] theorem castPoint_zero
    {W V : WeierstrassCurve ℚ_[37]} (h : W = V) :
    castPoint h (0 : W.toAffine.Point) = 0 := by
  subst V
  rfl

/-- Transport across equality of Weierstrass models preserves negation. -/
theorem castPoint_neg
    {W V : WeierstrassCurve ℚ_[37]} (h : W = V)
    (P : W.toAffine.Point) :
    castPoint h (-P) = -castPoint h P := by
  subst V
  rfl

/-- Transport across equality of Weierstrass models preserves addition. -/
theorem castPoint_add
    {W V : WeierstrassCurve ℚ_[37]} (h : W = V)
    (P Q : W.toAffine.Point) :
    castPoint h (P + Q) = castPoint h P + castPoint h Q := by
  subst V
  rfl

@[simp] theorem mapE0PointPlusLocal_zero :
    mapE0PointPlusLocal 0 = 0 := by
  rw [mapE0PointPlusLocal, map_zero, castPoint_zero]

@[simp] theorem mapE0PointMinusLocal_zero :
    mapE0PointMinusLocal 0 = 0 := by
  rw [mapE0PointMinusLocal, map_zero, castPoint_zero]

private theorem mapE0PointPlus_neg_direct (Q : E0Point) :
    mapE0PointPlus (-Q) = -mapE0PointPlus Q := by
  rcases Q with (_ | ⟨x, y, hxy⟩)
  · rfl
  · rw [WeierstrassCurve.Affine.Point.neg_some]
    simp only [mapE0PointPlus]
    change WeierstrassCurve.Affine.Point.some _ _ _ =
      WeierstrassCurve.Affine.Point.some _ _ _
    congr 1
    simp [gaussianE0, gaussianE0PadicPlus, WeierstrassCurve.Affine.negY]

private theorem mapE0PointMinus_neg_direct (Q : E0Point) :
    mapE0PointMinus (-Q) = -mapE0PointMinus Q := by
  rcases Q with (_ | ⟨x, y, hxy⟩)
  · rfl
  · rw [WeierstrassCurve.Affine.Point.neg_some]
    simp only [mapE0PointMinus]
    change WeierstrassCurve.Affine.Point.some _ _ _ =
      WeierstrassCurve.Affine.Point.some _ _ _
    congr 1
    simp [gaussianE0, gaussianE0PadicMinus, WeierstrassCurve.Affine.negY]

private theorem mapE0PointPlus_add_direct (Q R : E0Point) :
    mapE0PointPlus (Q + R) = mapE0PointPlus Q + mapE0PointPlus R :=
  mapE0PointPlus.map_add Q R

private theorem mapE0PointMinus_add_direct (Q R : E0Point) :
    mapE0PointMinus (Q + R) = mapE0PointMinus Q + mapE0PointMinus R :=
  mapE0PointMinus.map_add Q R

theorem mapE0PointPlusLocal_neg (Q : E0Point) :
    mapE0PointPlusLocal (-Q) = -mapE0PointPlusLocal Q := by
  change castPoint _ (mapE0PointPlus (-Q)) =
    -castPoint _ (mapE0PointPlus Q)
  calc
    castPoint _ (mapE0PointPlus (-Q)) =
        castPoint _ (-mapE0PointPlus Q) :=
      congrArg _ (mapE0PointPlus_neg_direct Q)
    _ = -castPoint _ (mapE0PointPlus Q) := castPoint_neg _ _

theorem mapE0PointMinusLocal_neg (Q : E0Point) :
    mapE0PointMinusLocal (-Q) = -mapE0PointMinusLocal Q := by
  change castPoint _ (mapE0PointMinus (-Q)) =
    -castPoint _ (mapE0PointMinus Q)
  calc
    castPoint _ (mapE0PointMinus (-Q)) =
        castPoint _ (-mapE0PointMinus Q) :=
      congrArg _ (mapE0PointMinus_neg_direct Q)
    _ = -castPoint _ (mapE0PointMinus Q) := castPoint_neg _ _

theorem mapE0PointPlusLocal_add (Q R : E0Point) :
    mapE0PointPlusLocal (Q + R) =
      mapE0PointPlusLocal Q + mapE0PointPlusLocal R := by
  change castPoint _ (mapE0PointPlus (Q + R)) =
    castPoint _ (mapE0PointPlus Q) + castPoint _ (mapE0PointPlus R)
  calc
    castPoint _ (mapE0PointPlus (Q + R)) =
        castPoint _ (mapE0PointPlus Q + mapE0PointPlus R) :=
      congrArg _ (mapE0PointPlus_add_direct Q R)
    _ = castPoint _ (mapE0PointPlus Q) +
        castPoint _ (mapE0PointPlus R) := castPoint_add _ _ _

theorem mapE0PointMinusLocal_add (Q R : E0Point) :
    mapE0PointMinusLocal (Q + R) =
      mapE0PointMinusLocal Q + mapE0PointMinusLocal R := by
  change castPoint _ (mapE0PointMinus (Q + R)) =
    castPoint _ (mapE0PointMinus Q) + castPoint _ (mapE0PointMinus R)
  calc
    castPoint _ (mapE0PointMinus (Q + R)) =
        castPoint _ (mapE0PointMinus Q + mapE0PointMinus R) :=
      congrArg _ (mapE0PointMinus_add_direct Q R)
    _ = castPoint _ (mapE0PointMinus Q) +
        castPoint _ (mapE0PointMinus R) := castPoint_add _ _ _

/-- The actual plus reduction supplies the zero field of
`Split37GoodReduction`. -/
@[simp] theorem reduceE0Plus_zero :
    reduceE0Plus 0 = none := by
  rw [reduceE0Plus, mapE0PointPlusLocal_zero, finiteReducePoint_zero]

/-- The actual minus reduction supplies the zero field of
`Split37GoodReduction`. -/
@[simp] theorem reduceE0Minus_zero :
    reduceE0Minus 0 = none := by
  rw [reduceE0Minus, mapE0PointMinusLocal_zero, finiteReducePoint_zero]

/-- The actual plus reduction supplies the negation field of
`Split37GoodReduction`. -/
theorem reduceE0Plus_neg (Q : E0Point) :
    reduceE0Plus (-Q) = finiteNeg 37 (reduceE0Plus Q) := by
  change finiteReducePoint plusA plusB (mapE0PointPlusLocal (-Q)) =
    finiteNeg 37 (finiteReducePoint plusA plusB (mapE0PointPlusLocal Q))
  rw [mapE0PointPlusLocal_neg, finiteReducePoint_neg]

/-- The actual minus reduction supplies the negation field of
`Split37GoodReduction`. -/
theorem reduceE0Minus_neg (Q : E0Point) :
    reduceE0Minus (-Q) = finiteNeg 37 (reduceE0Minus Q) := by
  change finiteReducePoint minusA minusB (mapE0PointMinusLocal (-Q)) =
    finiteNeg 37 (finiteReducePoint minusA minusB (mapE0PointMinusLocal Q))
  rw [mapE0PointMinusLocal_neg, finiteReducePoint_neg]

/-- The plus addition formula when the right input is zero. -/
theorem reduceE0Plus_add_zero (Q : E0Point) :
    reduceE0Plus (Q + 0) =
      finiteAdd 37 plusCoefficients.1 plusCoefficients.2
        (reduceE0Plus Q) (reduceE0Plus 0) := by
  rw [add_zero, reduceE0Plus_zero]
  cases reduceE0Plus Q <;> rfl

/-- The plus addition formula when the left input is zero. -/
theorem reduceE0Plus_zero_add (Q : E0Point) :
    reduceE0Plus (0 + Q) =
      finiteAdd 37 plusCoefficients.1 plusCoefficients.2
        (reduceE0Plus 0) (reduceE0Plus Q) := by
  rw [zero_add, reduceE0Plus_zero]
  rfl

/-- The minus addition formula when the right input is zero. -/
theorem reduceE0Minus_add_zero (Q : E0Point) :
    reduceE0Minus (Q + 0) =
      finiteAdd 37 minusCoefficients.1 minusCoefficients.2
        (reduceE0Minus Q) (reduceE0Minus 0) := by
  rw [add_zero, reduceE0Minus_zero]
  cases reduceE0Minus Q <;> rfl

/-- The minus addition formula when the left input is zero. -/
theorem reduceE0Minus_zero_add (Q : E0Point) :
    reduceE0Minus (0 + Q) =
      finiteAdd 37 minusCoefficients.1 minusCoefficients.2
        (reduceE0Minus 0) (reduceE0Minus Q) := by
  rw [zero_add, reduceE0Minus_zero]
  rfl

/-- The plus addition formula for a point and its inverse. -/
theorem reduceE0Plus_add_neg (Q : E0Point) :
    reduceE0Plus (Q + -Q) =
      finiteAdd 37 plusCoefficients.1 plusCoefficients.2
        (reduceE0Plus Q) (reduceE0Plus (-Q)) := by
  change
    finiteReducePoint plusA plusB
        (mapE0PointPlusLocal (Q + -Q)) =
      finiteAdd 37 plusCoefficients.1 plusCoefficients.2
        (finiteReducePoint plusA plusB (mapE0PointPlusLocal Q))
        (finiteReducePoint plusA plusB (mapE0PointPlusLocal (-Q)))
  rw [mapE0PointPlusLocal_add, mapE0PointPlusLocal_neg]
  exact finiteReducePoint_add_neg plusA plusB
    plusCoefficients.1 plusCoefficients.2 (mapE0PointPlusLocal Q)

/-- The minus addition formula for a point and its inverse. -/
theorem reduceE0Minus_add_neg (Q : E0Point) :
    reduceE0Minus (Q + -Q) =
      finiteAdd 37 minusCoefficients.1 minusCoefficients.2
        (reduceE0Minus Q) (reduceE0Minus (-Q)) := by
  change
    finiteReducePoint minusA minusB
        (mapE0PointMinusLocal (Q + -Q)) =
      finiteAdd 37 minusCoefficients.1 minusCoefficients.2
        (finiteReducePoint minusA minusB (mapE0PointMinusLocal Q))
        (finiteReducePoint minusA minusB (mapE0PointMinusLocal (-Q)))
  rw [mapE0PointMinusLocal_add, mapE0PointMinusLocal_neg]
  exact finiteReducePoint_add_neg minusA minusB
    minusCoefficients.1 minusCoefficients.2 (mapE0PointMinusLocal Q)

end

end GaussianProjectiveReductionHom
end Cuboid2
