import Cuboid2.QuadraticReduction.GaussianFormalKernelDisk
import Cuboid2.QuadraticReduction.GaussianReductionSurjective
import Cuboid2.QuadraticReduction.GaussianVisibleReduction
import Cuboid2.QuadraticReduction.GaussianCoverReductionActual

/-!
# Actual split-37 reduction homomorphisms

This file completes the group-law compatibility of the explicit projective
reduction constructed in `GaussianProjectiveReduction`.  The proof first
identifies the executable natural-number formulas with the affine group law
on the special fibre.  It then combines the integral secant/tangent
calculation with the already established formal-kernel fibre theorem.
-/

namespace Cuboid2
namespace GaussianSplit37ReductionActual

noncomputable section

open GaussianFinite
open GaussianP37
open GaussianP37Bridge
open GaussianGoodReduction
open GaussianProjectiveReduction
open GaussianProjectiveReductionHom
open GaussianFormalKernelDisk
open GaussianReductionSurjective
open GaussianVisibleReduction
open GaussianCoverReductionActual

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : DecidableEq ℚ_[37] := Classical.decEq _

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

/-! ## Canonical representatives of residue-field arithmetic -/

theorem residueSub_val_37 (a b : ZMod 37) :
    residueSub 37 a.val b.val = (a - b).val := by
  native_decide +revert

theorem residueAdd_val_37 (a b : ZMod 37) :
    (a.val + b.val) % 37 = (a + b).val := by
  native_decide +revert

theorem residueMul_val_37 (a b : ZMod 37) :
    (a.val * b.val) % 37 = (a * b).val := by
  native_decide +revert

theorem residuePowTwo_val_37 (a : ZMod 37) :
    a.val ^ 2 % 37 = (a ^ 2).val := by
  native_decide +revert

theorem residueInv_val_37 (a : ZMod 37) :
    residueInv 37 a.val = a⁻¹.val := by
  native_decide +revert

theorem tangentSlope_val_37 (a b x y : ZMod 37) :
    ((3 * x.val ^ 2 + 2 * a.val * x.val + b.val) *
          residueInv 37 (2 * y.val % 37)) % 37 =
      ((3 * x ^ 2 + 2 * a * x + b) / (2 * y)).val := by
  native_decide +revert

theorem secantSlope_val_37 (x X y Y : ZMod 37) :
    (residueSub 37 Y.val y.val *
          residueInv 37 (residueSub 37 X.val x.val)) % 37 =
      ((y - Y) / (x - X)).val := by
  native_decide +revert

theorem addX_val_37 (a x X slope : ZMod 37) :
    residueSub 37
        (residueSub 37
          (residueSub 37 (slope.val ^ 2) a.val) x.val) X.val =
      (slope ^ 2 - a - x - X).val := by
  native_decide +revert

theorem addY_val_37 (x y slope xr : ZMod 37) :
    residueSub 37
        (slope.val * residueSub 37 x.val xr.val) y.val =
      (slope * (x - xr) - y).val := by
  native_decide +revert

theorem finiteCurveRhs_val_37 (a b x : ZMod 37) :
    finiteCurveRhs 37 a.val b.val x.val =
      (x ^ 3 + a * x ^ 2 + b * x).val := by
  native_decide +revert

/-! ## The executable and geometric special-fibre laws agree -/

/-- Canonical natural-number representatives convert the geometric group law
on every special fibre `y² = x³ + A x² + B x` into `finiteAdd`. -/
theorem finitePointOfResidue_add
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P Q : (localResidueCurve A B).toAffine.Point) :
    finitePointOfResidue (P + Q) =
      finiteAdd 37 (PadicInt.toZMod A).val (PadicInt.toZMod B).val
        (finitePointOfResidue P) (finitePointOfResidue Q) := by
  rcases P with (_ | ⟨x, y, hP⟩)
  · rfl
  · rcases Q with (_ | ⟨X, Y, hQ⟩)
    · rfl
    · let W := (localResidueCurve A B).toAffine
      have hnegY :
          W.negY X Y = -Y := by
        simp [W, localResidueCurve, localCurve,
          WeierstrassCurve.Affine.negY]
      by_cases hvertical : x = X ∧ y = W.negY X Y
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq
          hvertical.1 hvertical.2]
        simp only [finitePointOfResidue]
        have hxval : x.val = X.val :=
          congrArg ZMod.val hvertical.1
        have hyadd : (y.val + Y.val) % 37 = 0 := by
          rw [residueAdd_val_37]
          have hy : y = -Y := by
            simpa only [hnegY] using hvertical.2
          rw [hy, neg_add_cancel]
          rfl
        simp [finiteAdd, hxval, ZMod.val_lt, hyadd]
      · rw [WeierstrassCurve.Affine.Point.add_some hvertical]
        simp only [finitePointOfResidue,
          WeierstrassCurve.Affine.Point.mk]
        have hnotFiniteVertical :
            ¬(x.val % 37 = X.val % 37 ∧
              (y.val + Y.val) % 37 = 0) := by
          rintro ⟨hxval, hyval⟩
          have hxval' : x.val = X.val := by
            simpa [Nat.mod_eq_of_lt x.val_lt,
              Nat.mod_eq_of_lt X.val_lt] using hxval
          have hx : x = X := ZMod.val_injective 37 hxval'
          have hyzero : y + Y = 0 := by
            apply ZMod.val_injective 37
            rw [ZMod.val_zero]
            simpa only [residueAdd_val_37] using hyval
          have hy : y = -Y := eq_neg_of_add_eq_zero_left hyzero
          apply hvertical
          exact ⟨hx, by simpa only [hnegY] using hy⟩
        have hcondition :
            (decide (x.val % 37 = X.val % 37) &&
                decide ((y.val + Y.val) % 37 = 0)) = false := by
          by_cases hxval : x.val % 37 = X.val % 37
          · have hyval : (y.val + Y.val) % 37 ≠ 0 :=
              fun h => hnotFiniteVertical ⟨hxval, h⟩
            simp [hxval, hyval]
          · simp [hxval]
        simp only [finiteAdd, hcondition, Bool.false_eq_true,
          ↓reduceIte]
        by_cases hx : x = X
        · have hy : y = Y := by
            exact
              (WeierstrassCurve.Affine.Y_eq_of_X_eq
                hP.1 hQ.1 hx).resolve_right (fun h => hvertical ⟨hx, h⟩)
          subst X
          subst Y
          have hyNot : y ≠ W.negY x y :=
            fun h => hvertical ⟨rfl, h⟩
          rw [if_pos rfl]
          let slope : ZMod 37 :=
            (3 * x ^ 2 + 2 * PadicInt.toZMod A * x +
                PadicInt.toZMod B) / (2 * y)
          have hslope :
              ((3 * x.val ^ 2 +
                    2 * (PadicInt.toZMod A).val * x.val +
                    (PadicInt.toZMod B).val) *
                  residueInv 37 (2 * y.val % 37)) % 37 =
                slope.val := by
            exact tangentSlope_val_37
              (PadicInt.toZMod A) (PadicInt.toZMod B) x y
          rw [hslope]
          have hmathSlope :
              W.slope x x y y = slope := by
            rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyNot]
            rw [hnegY]
            dsimp only [W]
            simp only [localResidueCurve, localCurve,
              WeierstrassCurve.map, map_zero, zero_mul, sub_zero]
            change
              (3 * x ^ 2 + 2 * PadicInt.toZMod A * x +
                    PadicInt.toZMod B) /
                  (y - -y) =
                slope
            dsimp only [slope]
            congr 1 <;> ring
          rw [hmathSlope]
          let xr : ZMod 37 :=
            slope ^ 2 - PadicInt.toZMod A - x - x
          have hxr :
              residueSub 37
                  (residueSub 37
                    (residueSub 37 (slope.val ^ 2)
                      (PadicInt.toZMod A).val) x.val) x.val =
                xr.val :=
            addX_val_37 (PadicInt.toZMod A) x x slope
          rw [hxr]
          have haddX :
              W.addX x x slope = xr := by
            simp only [W, xr, localResidueCurve, localCurve,
              WeierstrassCurve.map, WeierstrassCurve.Affine.addX,
              map_zero, zero_mul, add_zero]
          rw [haddX]
          have haddY :
              W.addY x x y slope = slope * (x - xr) - y := by
            rw [WeierstrassCurve.Affine.addY,
              WeierstrassCurve.Affine.negAddY, haddX]
            simp only [W,
              WeierstrassCurve.Affine.negY, localResidueCurve,
              localCurve, WeierstrassCurve.map, map_zero, zero_mul,
              sub_zero]
            ring
          rw [haddY]
          have hyr :
              residueSub 37
                  (slope.val * residueSub 37 x.val xr.val) y.val =
                (slope * (x - xr) - y).val :=
            addY_val_37 x y slope xr
          rw [hyr]
        · have hxvalNe : x.val ≠ X.val :=
            fun h => hx (ZMod.val_injective 37 h)
          have hxmodNe : x.val % 37 ≠ X.val % 37 := by
            simpa [Nat.mod_eq_of_lt x.val_lt,
              Nat.mod_eq_of_lt X.val_lt] using hxvalNe
          rw [if_neg hxmodNe]
          let slope : ZMod 37 := (y - Y) / (x - X)
          have hslope :
              (residueSub 37 Y.val y.val *
                    residueInv 37 (residueSub 37 X.val x.val)) % 37 =
                slope.val :=
            secantSlope_val_37 x X y Y
          rw [hslope]
          have hmathSlope :
              W.slope x X y Y = slope := by
            rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
          rw [hmathSlope]
          let xr : ZMod 37 :=
            slope ^ 2 - PadicInt.toZMod A - x - X
          have hxr :
              residueSub 37
                  (residueSub 37
                    (residueSub 37 (slope.val ^ 2)
                      (PadicInt.toZMod A).val) x.val) X.val =
                xr.val :=
            addX_val_37 (PadicInt.toZMod A) x X slope
          rw [hxr]
          have haddX :
              W.addX x X slope = xr := by
            simp only [W, xr, localResidueCurve, localCurve,
              WeierstrassCurve.map, WeierstrassCurve.Affine.addX,
              map_zero, zero_mul, add_zero]
          rw [haddX]
          have haddY :
              W.addY x X y slope = slope * (x - xr) - y := by
            rw [WeierstrassCurve.Affine.addY,
              WeierstrassCurve.Affine.negAddY, haddX]
            simp only [W,
              WeierstrassCurve.Affine.negY, localResidueCurve,
              localCurve, WeierstrassCurve.map, map_zero, zero_mul,
              sub_zero]
            ring
          rw [haddY]
          have hyr :
              residueSub 37
                  (slope.val * residueSub 37 x.val xr.val) y.val =
                (slope * (x - xr) - y).val :=
            addY_val_37 x y slope xr
          rw [hyr]

theorem finitePointOfResidue_injective
    {W : WeierstrassCurve (ZMod 37)} :
    Function.Injective
      (finitePointOfResidue :
        W.toAffine.Point → FinitePoint) := by
  intro P Q h
  rcases P with (_ | ⟨x, y, hP⟩) <;>
    rcases Q with (_ | ⟨X, Y, hQ⟩)
  · rfl
  · simp [finitePointOfResidue] at h
  · simp [finitePointOfResidue] at h
  · simp only [finitePointOfResidue, Option.some.injEq,
      Prod.mk.injEq] at h
    have hx : x = X := ZMod.val_injective 37 h.1
    have hy : y = Y := ZMod.val_injective 37 h.2
    subst X
    subst Y
    rfl

/-- Reduction of an affine point already given by integral coordinates,
at the geometric (proof-carrying) residue-point level. -/
theorem reducePoint_some_coe
    (A B x y : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (hxy :
      (localPadicCurve A B).toAffine.Nonsingular
        (x : ℚ_[37]) (y : ℚ_[37])) :
    reducePoint A B (.some (x : ℚ_[37]) (y : ℚ_[37]) hxy) =
      .some (PadicInt.toZMod x) (PadicInt.toZMod y)
        (residue_nonsingular_of_integral_point
          A B hxy x.property) := by
  apply finitePointOfResidue_injective
  exact
    GaussianVisibleReduction.finiteReducePoint_some_coe
      A B x y hxy

/-- Reduction commutes with division by a 37-adic unit. -/
theorem toZMod_integral_quotient
    (num den : ℤ_[37])
    (hden : PadicInt.toZMod den ≠ 0) :
    let q : ℤ_[37] :=
      ⟨(num : ℚ_[37]) / (den : ℚ_[37]), by
        rw [norm_div,
          norm_coe_eq_one_of_toZMod_ne_zero den hden, div_one]
        exact num.property⟩
    PadicInt.toZMod q =
      PadicInt.toZMod num / PadicInt.toZMod den := by
  intro q
  apply (eq_div_iff hden).2
  rw [← map_mul]
  apply congrArg PadicInt.toZMod
  apply Subtype.val_injective
  change
    ((num : ℚ_[37]) / (den : ℚ_[37])) *
        (den : ℚ_[37]) =
      (num : ℚ_[37])
  have hdenCoe : (den : ℚ_[37]) ≠ 0 := by
    intro hzero
    apply hden
    have hdenZero : den = 0 := Subtype.ext hzero
    rw [hdenZero, map_zero]
  exact div_mul_cancel₀ _ hdenCoe

/-! ## Integral secants and tangents -/

/-- The secant formula commutes with reduction when the two reduced
abscissae are distinct. -/
theorem finiteReducePoint_add_of_integral_residue_x_ne
    (A B x y X Y : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (hP :
      (localPadicCurve A B).toAffine.Nonsingular
        (x : ℚ_[37]) (y : ℚ_[37]))
    (hQ :
      (localPadicCurve A B).toAffine.Nonsingular
        (X : ℚ_[37]) (Y : ℚ_[37]))
    (hxRed : PadicInt.toZMod x ≠ PadicInt.toZMod X) :
    finiteReducePoint A B
        ((.some (x : ℚ_[37]) (y : ℚ_[37]) hP :
            (localPadicCurve A B).toAffine.Point) +
          .some (X : ℚ_[37]) (Y : ℚ_[37]) hQ) =
      finiteAdd 37 (PadicInt.toZMod A).val
        (PadicInt.toZMod B).val
        (finiteReducePoint A B (.some (x : ℚ_[37]) (y : ℚ_[37]) hP))
        (finiteReducePoint A B (.some (X : ℚ_[37]) (Y : ℚ_[37]) hQ)) := by
  let num : ℤ_[37] := y - Y
  let den : ℤ_[37] := x - X
  have hdenRed : PadicInt.toZMod den ≠ 0 := by
    simpa only [den, map_sub, sub_ne_zero] using hxRed
  let slopeInt : ℤ_[37] :=
    ⟨(num : ℚ_[37]) / (den : ℚ_[37]), by
      rw [norm_div,
        norm_coe_eq_one_of_toZMod_ne_zero den hdenRed, div_one]
      exact num.property⟩
  have hslopeRed :
      PadicInt.toZMod slopeInt =
        (PadicInt.toZMod y - PadicInt.toZMod Y) /
          (PadicInt.toZMod x - PadicInt.toZMod X) := by
    have h :=
      toZMod_integral_quotient num den hdenRed
    simpa only [slopeInt, num, den, map_sub] using h
  let xrInt : ℤ_[37] := slopeInt ^ 2 - A - x - X
  let yrInt : ℤ_[37] := slopeInt * (x - xrInt) - y
  have hxCoe : (x : ℚ_[37]) ≠ (X : ℚ_[37]) := by
    intro h
    apply hxRed
    have hxInt : x = X := Subtype.ext h
    rw [hxInt]
  have hslope :
      (localPadicCurve A B).toAffine.slope
          (x : ℚ_[37]) (X : ℚ_[37])
          (y : ℚ_[37]) (Y : ℚ_[37]) =
        (slopeInt : ℚ_[37]) := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hxCoe]
    simp only [slopeInt, num, den, PadicInt.coe_sub]
  have hxCoord :
      (localPadicCurve A B).toAffine.addX
          (x : ℚ_[37]) (X : ℚ_[37]) (slopeInt : ℚ_[37]) =
        (xrInt : ℚ_[37]) := by
    simp only [localPadicCurve, localCurve,
      WeierstrassCurve.map, WeierstrassCurve.Affine.addX,
      map_zero, zero_mul, add_zero, xrInt, PadicInt.coe_sub,
      PadicInt.coe_pow]
    rw [show PadicInt.Coe.ringHom A = (A : ℚ_[37]) by rfl]
  have hyCoord :
      (localPadicCurve A B).toAffine.addY
          (x : ℚ_[37]) (X : ℚ_[37])
          (y : ℚ_[37]) (slopeInt : ℚ_[37]) =
        (yrInt : ℚ_[37]) := by
    rw [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, hxCoord]
    simp only [localPadicCurve, localCurve,
      WeierstrassCurve.map, WeierstrassCurve.Affine.negY,
      map_zero, zero_mul, sub_zero, yrInt, PadicInt.coe_sub,
      PadicInt.coe_mul]
    ring
  have hnot :
      ¬((x : ℚ_[37]) = (X : ℚ_[37]) ∧
        (y : ℚ_[37]) =
          (localPadicCurve A B).toAffine.negY
            (X : ℚ_[37]) (Y : ℚ_[37])) :=
    fun h => hxCoe h.1
  have hsumActual :
      (localPadicCurve A B).toAffine.Nonsingular
        ((localPadicCurve A B).toAffine.addX
          (x : ℚ_[37]) (X : ℚ_[37])
          ((localPadicCurve A B).toAffine.slope
            (x : ℚ_[37]) (X : ℚ_[37])
            (y : ℚ_[37]) (Y : ℚ_[37])))
        ((localPadicCurve A B).toAffine.addY
          (x : ℚ_[37]) (X : ℚ_[37]) (y : ℚ_[37])
          ((localPadicCurve A B).toAffine.slope
            (x : ℚ_[37]) (X : ℚ_[37])
            (y : ℚ_[37]) (Y : ℚ_[37]))) :=
    WeierstrassCurve.Affine.nonsingular_add hP hQ hnot
  have hsum :
      (localPadicCurve A B).toAffine.Nonsingular
        (xrInt : ℚ_[37]) (yrInt : ℚ_[37]) := by
    have h := hsumActual
    rw [hslope] at h
    simpa only [hxCoord, hyCoord] using h
  rw [WeierstrassCurve.Affine.Point.add_some hnot]
  have hpointEq :
      (WeierstrassCurve.Affine.Point.some
          ((localPadicCurve A B).toAffine.addX
            (x : ℚ_[37]) (X : ℚ_[37])
            ((localPadicCurve A B).toAffine.slope
              (x : ℚ_[37]) (X : ℚ_[37])
              (y : ℚ_[37]) (Y : ℚ_[37])))
          ((localPadicCurve A B).toAffine.addY
            (x : ℚ_[37]) (X : ℚ_[37])
            (y : ℚ_[37])
            ((localPadicCurve A B).toAffine.slope
              (x : ℚ_[37]) (X : ℚ_[37])
              (y : ℚ_[37]) (Y : ℚ_[37]))) hsumActual :
          (localPadicCurve A B).toAffine.Point) =
        .some (xrInt : ℚ_[37]) (yrInt : ℚ_[37]) hsum := by
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · rw [hslope]
      exact hxCoord
    · rw [hslope]
      exact hyCoord
  rw [hpointEq,
    GaussianVisibleReduction.finiteReducePoint_some_coe,
    GaussianVisibleReduction.finiteReducePoint_some_coe,
    GaussianVisibleReduction.finiteReducePoint_some_coe]
  have hxValNe :
      (PadicInt.toZMod x).val ≠ (PadicInt.toZMod X).val :=
    fun h => hxRed (ZMod.val_injective 37 h)
  have hxModNe :
      (PadicInt.toZMod x).val % 37 ≠
        (PadicInt.toZMod X).val % 37 := by
    intro h
    apply hxValNe
    calc
      (PadicInt.toZMod x).val =
          (PadicInt.toZMod x).val % 37 :=
        (Nat.mod_eq_of_lt (PadicInt.toZMod x).val_lt).symm
      _ = (PadicInt.toZMod X).val % 37 := h
      _ = (PadicInt.toZMod X).val :=
        Nat.mod_eq_of_lt (PadicInt.toZMod X).val_lt
  simp only [finiteAdd, hxModNe, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]
  have hslopeNat :
      (residueSub 37 (PadicInt.toZMod Y).val
            (PadicInt.toZMod y).val *
          residueInv 37
            (residueSub 37 (PadicInt.toZMod X).val
              (PadicInt.toZMod x).val)) % 37 =
        (PadicInt.toZMod slopeInt).val := by
    rw [secantSlope_val_37, hslopeRed]
  rw [hslopeNat]
  have hxrNat :=
    addX_val_37 (PadicInt.toZMod A)
      (PadicInt.toZMod x) (PadicInt.toZMod X)
      (PadicInt.toZMod slopeInt)
  have hxrRed :
      PadicInt.toZMod xrInt =
        PadicInt.toZMod slopeInt ^ 2 -
          PadicInt.toZMod A - PadicInt.toZMod x -
            PadicInt.toZMod X := by
    simp only [xrInt, map_sub, map_pow]
  rw [hxrNat, ← hxrRed]
  have hyrNat :=
    addY_val_37 (PadicInt.toZMod x) (PadicInt.toZMod y)
      (PadicInt.toZMod slopeInt) (PadicInt.toZMod xrInt)
  have hyrRed :
      PadicInt.toZMod yrInt =
        PadicInt.toZMod slopeInt *
            (PadicInt.toZMod x - PadicInt.toZMod xrInt) -
          PadicInt.toZMod y := by
    simp only [yrInt, map_sub, map_mul]
  rw [hyrNat, ← hyrRed]
  simp

/-- The tangent formula commutes with reduction away from residue
two-torsion. -/
theorem finiteReducePoint_add_self_of_integral_residue_y_ne_zero
    (A B x y : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (hP :
      (localPadicCurve A B).toAffine.Nonsingular
        (x : ℚ_[37]) (y : ℚ_[37]))
    (hyRed : PadicInt.toZMod y ≠ 0) :
    finiteReducePoint A B
        ((.some (x : ℚ_[37]) (y : ℚ_[37]) hP :
            (localPadicCurve A B).toAffine.Point) +
          .some (x : ℚ_[37]) (y : ℚ_[37]) hP) =
      finiteAdd 37 (PadicInt.toZMod A).val
        (PadicInt.toZMod B).val
        (finiteReducePoint A B (.some (x : ℚ_[37]) (y : ℚ_[37]) hP))
        (finiteReducePoint A B (.some (x : ℚ_[37]) (y : ℚ_[37]) hP)) := by
  let num : ℤ_[37] := 3 * x ^ 2 + 2 * A * x + B
  let den : ℤ_[37] := 2 * y
  have htwo : (2 : ZMod 37) ≠ 0 := by native_decide
  have hdenRed : PadicInt.toZMod den ≠ 0 := by
    simpa only [den, map_mul, map_ofNat] using mul_ne_zero htwo hyRed
  let slopeInt : ℤ_[37] :=
    ⟨(num : ℚ_[37]) / (den : ℚ_[37]), by
      rw [norm_div,
        norm_coe_eq_one_of_toZMod_ne_zero den hdenRed, div_one]
      exact num.property⟩
  have hslopeRed :
      PadicInt.toZMod slopeInt =
        (3 * PadicInt.toZMod x ^ 2 +
              2 * PadicInt.toZMod A * PadicInt.toZMod x +
              PadicInt.toZMod B) /
          (2 * PadicInt.toZMod y) := by
    have h :=
      toZMod_integral_quotient num den hdenRed
    simpa only [slopeInt, num, den, map_add, map_mul, map_pow,
      map_ofNat] using h
  let xrInt : ℤ_[37] := slopeInt ^ 2 - A - x - x
  let yrInt : ℤ_[37] := slopeInt * (x - xrInt) - y
  have hyNot :
      (y : ℚ_[37]) ≠
        (localPadicCurve A B).toAffine.negY
          (x : ℚ_[37]) (y : ℚ_[37]) := by
    simp only [localPadicCurve, localCurve,
      WeierstrassCurve.map, WeierstrassCurve.Affine.negY,
      map_zero, zero_mul, sub_zero]
    intro h
    have hyZero : (y : ℚ_[37]) = 0 := by
      have htwoY : (2 : ℚ_[37]) * (y : ℚ_[37]) = 0 := by
        linear_combination h
      exact (mul_eq_zero.mp htwoY).resolve_left (by norm_num)
    apply hyRed
    have hyIntZero : y = 0 := Subtype.ext hyZero
    rw [hyIntZero, map_zero]
  have hslope :
      (localPadicCurve A B).toAffine.slope
          (x : ℚ_[37]) (x : ℚ_[37])
          (y : ℚ_[37]) (y : ℚ_[37]) =
        (slopeInt : ℚ_[37]) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyNot]
    simp only [localPadicCurve, localCurve,
      WeierstrassCurve.map, WeierstrassCurve.Affine.negY,
      map_zero, zero_mul, sub_zero]
    change
      (3 * (x : ℚ_[37]) ^ 2 +
            2 * (A : ℚ_[37]) * (x : ℚ_[37]) +
            (B : ℚ_[37])) /
          ((y : ℚ_[37]) - -(y : ℚ_[37])) =
        (slopeInt : ℚ_[37])
    simp only [slopeInt, num, den, PadicInt.coe_add,
      PadicInt.coe_mul, PadicInt.coe_pow]
    rw [show ((3 : ℤ_[37]) : ℚ_[37]) = 3 from
      PadicInt.coe_natCast 3]
    rw [show ((2 : ℤ_[37]) : ℚ_[37]) = 2 from
      PadicInt.coe_natCast 2]
    congr 1 <;> ring
  have hxCoord :
      (localPadicCurve A B).toAffine.addX
          (x : ℚ_[37]) (x : ℚ_[37]) (slopeInt : ℚ_[37]) =
        (xrInt : ℚ_[37]) := by
    simp only [localPadicCurve, localCurve,
      WeierstrassCurve.map, WeierstrassCurve.Affine.addX,
      map_zero, zero_mul, add_zero, xrInt, PadicInt.coe_sub,
      PadicInt.coe_pow]
    rw [show PadicInt.Coe.ringHom A = (A : ℚ_[37]) by rfl]
  have hyCoord :
      (localPadicCurve A B).toAffine.addY
          (x : ℚ_[37]) (x : ℚ_[37])
          (y : ℚ_[37]) (slopeInt : ℚ_[37]) =
        (yrInt : ℚ_[37]) := by
    rw [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, hxCoord]
    simp only [localPadicCurve, localCurve,
      WeierstrassCurve.map, WeierstrassCurve.Affine.negY,
      map_zero, zero_mul, sub_zero, yrInt, PadicInt.coe_sub,
      PadicInt.coe_mul]
    ring
  have hnot :
      ¬((x : ℚ_[37]) = (x : ℚ_[37]) ∧
        (y : ℚ_[37]) =
          (localPadicCurve A B).toAffine.negY
            (x : ℚ_[37]) (y : ℚ_[37])) :=
    fun h => hyNot h.2
  have hsumActual :=
    WeierstrassCurve.Affine.nonsingular_add hP hP hnot
  have hsum :
      (localPadicCurve A B).toAffine.Nonsingular
        (xrInt : ℚ_[37]) (yrInt : ℚ_[37]) := by
    have h := hsumActual
    rw [hslope] at h
    simpa only [hxCoord, hyCoord] using h
  rw [WeierstrassCurve.Affine.Point.add_some hnot]
  have hpointEq :
      (WeierstrassCurve.Affine.Point.some
          ((localPadicCurve A B).toAffine.addX
            (x : ℚ_[37]) (x : ℚ_[37])
            ((localPadicCurve A B).toAffine.slope
              (x : ℚ_[37]) (x : ℚ_[37])
              (y : ℚ_[37]) (y : ℚ_[37])))
          ((localPadicCurve A B).toAffine.addY
            (x : ℚ_[37]) (x : ℚ_[37]) (y : ℚ_[37])
            ((localPadicCurve A B).toAffine.slope
              (x : ℚ_[37]) (x : ℚ_[37])
              (y : ℚ_[37]) (y : ℚ_[37]))) hsumActual :
          (localPadicCurve A B).toAffine.Point) =
        .some (xrInt : ℚ_[37]) (yrInt : ℚ_[37]) hsum := by
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · rw [hslope]
      exact hxCoord
    · rw [hslope]
      exact hyCoord
  rw [hpointEq,
    GaussianVisibleReduction.finiteReducePoint_some_coe]
  rw [GaussianVisibleReduction.finiteReducePoint_some_coe A B x y hP]
  have hySumNe :
      ((PadicInt.toZMod y).val + (PadicInt.toZMod y).val) % 37 ≠ 0 := by
    intro hsumVal
    apply hyRed
    have hsumZero : PadicInt.toZMod y + PadicInt.toZMod y = 0 := by
      apply ZMod.val_injective 37
      rw [ZMod.val_zero]
      simpa only [residueAdd_val_37] using hsumVal
    have htwoMul : (2 : ZMod 37) * PadicInt.toZMod y = 0 := by
      linear_combination hsumZero
    exact (mul_eq_zero.mp htwoMul).resolve_left htwo
  simp only [finiteAdd,
    Nat.mod_eq_of_lt (PadicInt.toZMod x).val_lt,
    hySumNe, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  have hslopeNat :
      ((3 * (PadicInt.toZMod x).val ^ 2 +
              2 * (PadicInt.toZMod A).val *
                (PadicInt.toZMod x).val +
              (PadicInt.toZMod B).val) *
            residueInv 37 (2 * (PadicInt.toZMod y).val % 37)) % 37 =
        (PadicInt.toZMod slopeInt).val := by
    rw [tangentSlope_val_37, hslopeRed]
  rw [hslopeNat]
  have hxrNat :=
    addX_val_37 (PadicInt.toZMod A)
      (PadicInt.toZMod x) (PadicInt.toZMod x)
      (PadicInt.toZMod slopeInt)
  have hxrRed :
      PadicInt.toZMod xrInt =
        PadicInt.toZMod slopeInt ^ 2 -
          PadicInt.toZMod A - PadicInt.toZMod x -
            PadicInt.toZMod x := by
    simp only [xrInt, map_sub, map_pow]
  rw [hxrNat, ← hxrRed]
  have hyrNat :=
    addY_val_37 (PadicInt.toZMod x) (PadicInt.toZMod y)
      (PadicInt.toZMod slopeInt) (PadicInt.toZMod xrInt)
  have hyrRed :
      PadicInt.toZMod yrInt =
        PadicInt.toZMod slopeInt *
            (PadicInt.toZMod x - PadicInt.toZMod xrInt) -
          PadicInt.toZMod y := by
    simp only [yrInt, map_sub, map_mul]
  rw [hyrNat, ← hyrRed]
  simp

/-! ## Arbitrary local points -/

/-- The explicit projective reduction is a group homomorphism for every
integral two-torsion model with smooth special fibre. -/
theorem finiteReducePoint_add
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P Q : (localPadicCurve A B).toAffine.Point) :
    finiteReducePoint A B (P + Q) =
      finiteAdd 37 (PadicInt.toZMod A).val
        (PadicInt.toZMod B).val
        (finiteReducePoint A B P) (finiteReducePoint A B Q) := by
  by_cases hredP : finiteReducePoint A B P = none
  · have htranslate :=
      finiteReducePoint_add_eq_left_of_right_eq_none
        A B Q P hredP
    rw [add_comm] at htranslate
    rw [htranslate, hredP]
    rfl
  by_cases hredQ : finiteReducePoint A B Q = none
  · have htranslate :=
      finiteReducePoint_add_eq_left_of_right_eq_none
        A B P Q hredQ
    rw [htranslate, hredQ]
    cases finiteReducePoint A B P <;> rfl
  rcases P with (_ | ⟨x, y, hP⟩)
  · exact (hredP (finiteReducePoint_zero A B)).elim
  · rcases Q with (_ | ⟨X, Y, hQ⟩)
    · exact (hredQ (finiteReducePoint_zero A B)).elim
    · have hx : ‖x‖ ≤ 1 := by
        by_contra h
        apply hredP
        exact finiteReducePoint_eq_none_of_norm_x_gt_one
          A B hP (lt_of_not_ge h)
      have hX : ‖X‖ ≤ 1 := by
        by_contra h
        apply hredQ
        exact finiteReducePoint_eq_none_of_norm_x_gt_one
          A B hQ (lt_of_not_ge h)
      have hy : ‖y‖ ≤ 1 :=
        norm_y_le_one_of_norm_x_le_one A B hP.1 hx
      have hY : ‖Y‖ ≤ 1 :=
        norm_y_le_one_of_norm_x_le_one A B hQ.1 hX
      let xInt : ℤ_[37] := ⟨x, hx⟩
      let yInt : ℤ_[37] := ⟨y, hy⟩
      let XInt : ℤ_[37] := ⟨X, hX⟩
      let YInt : ℤ_[37] := ⟨Y, hY⟩
      let RP : (localResidueCurve A B).toAffine.Point :=
        reducePoint A B (.some x y hP)
      let RQ : (localResidueCurve A B).toAffine.Point :=
        reducePoint A B (.some X Y hQ)
      have hRP :
          RP =
            .some (PadicInt.toZMod xInt) (PadicInt.toZMod yInt)
              (residue_nonsingular_of_integral_point
                A B hP hx) := by
        simpa only [RP, xInt, yInt] using
          reducePoint_some_coe A B xInt yInt hP
      have hRQ :
          RQ =
            .some (PadicInt.toZMod XInt) (PadicInt.toZMod YInt)
              (residue_nonsingular_of_integral_point
                A B hQ hX) := by
        simpa only [RQ, XInt, YInt] using
          reducePoint_some_coe A B XInt YInt hQ
      by_cases hinv : RP = -RQ
      · have hfinInv :
            finiteReducePoint A B (.some x y hP) =
              finiteReducePoint A B (-.some X Y hQ) := by
          change finitePointOfResidue RP =
            finitePointOfResidue (reducePoint A B (-.some X Y hQ))
          rw [reducePoint_neg]
          exact congrArg finitePointOfResidue hinv
        have hsumNone :
            finiteReducePoint A B
              ((.some x y hP :
                  (localPadicCurve A B).toAffine.Point) +
                .some X Y hQ) = none := by
          have h :=
            finiteReducePoint_sub_eq_none_of_eq
              A B (.some x y hP) (-.some X Y hQ) hfinInv
          simpa only [sub_neg_eq_add] using h
        rw [hsumNone]
        have hresidueSum : RP + RQ = 0 := by
          rw [hinv, neg_add_cancel]
        change
          none =
            finiteAdd 37 (PadicInt.toZMod A).val
              (PadicInt.toZMod B).val
              (finitePointOfResidue RP)
              (finitePointOfResidue RQ)
        rw [← finitePointOfResidue_add A B RP RQ,
          hresidueSum]
        rfl
      · by_cases heq : RP = RQ
        · have hfinEq :
              finiteReducePoint A B (.some x y hP) =
                finiteReducePoint A B (.some X Y hQ) :=
            congrArg finitePointOfResidue heq
          have hdiffKernel :
              finiteReducePoint A B
                ((.some X Y hQ :
                    (localPadicCurve A B).toAffine.Point) -
                  .some x y hP) = none :=
            finiteReducePoint_sub_eq_none_of_eq
              A B (.some X Y hQ) (.some x y hP) hfinEq.symm
          have hsumEq :
              finiteReducePoint A B
                  ((.some x y hP :
                      (localPadicCurve A B).toAffine.Point) +
                    .some X Y hQ) =
                finiteReducePoint A B
                  ((.some x y hP :
                      (localPadicCurve A B).toAffine.Point) +
                    .some x y hP) := by
            apply
              (finiteReducePoint_eq_iff_sub_mem_infinityKernel
                A B _ _).2
            have hgroup :
                ((.some x y hP :
                    (localPadicCurve A B).toAffine.Point) +
                    .some X Y hQ) -
                    ((.some x y hP :
                      (localPadicCurve A B).toAffine.Point) +
                      .some x y hP) =
                  (.some X Y hQ :
                    (localPadicCurve A B).toAffine.Point) -
                    .some x y hP := by
              abel
            rw [hgroup]
            exact hdiffKernel
          have hyRed :
              PadicInt.toZMod yInt ≠ 0 := by
            intro hyZero
            apply hinv
            calc
              RP = -RP := by
                apply finitePointOfResidue_injective
                rw [finitePointOfResidue_neg, hRP]
                simp [finitePointOfResidue, finiteNeg,
                  hyZero, residueSub]
              _ = -RQ := congrArg Neg.neg heq
          have htangent :=
            finiteReducePoint_add_self_of_integral_residue_y_ne_zero
              A B xInt yInt hP hyRed
          calc
            finiteReducePoint A B
                ((.some x y hP :
                    (localPadicCurve A B).toAffine.Point) +
                  .some X Y hQ) =
                finiteReducePoint A B
                  ((.some x y hP :
                      (localPadicCurve A B).toAffine.Point) +
                    .some x y hP) := hsumEq
            _ = finiteAdd 37 (PadicInt.toZMod A).val
                  (PadicInt.toZMod B).val
                  (finiteReducePoint A B (.some x y hP))
                  (finiteReducePoint A B (.some x y hP)) := by
              simpa only [xInt, yInt] using htangent
            _ = finiteAdd 37 (PadicInt.toZMod A).val
                  (PadicInt.toZMod B).val
                  (finiteReducePoint A B (.some x y hP))
                  (finiteReducePoint A B (.some X Y hQ)) := by
              rw [hfinEq]
        · have hxRed :
              PadicInt.toZMod xInt ≠ PadicInt.toZMod XInt := by
            intro hxResidue
            have hor : RP = RQ ∨ RP = -RQ := by
              rw [hRP, hRQ]
              exact
                (WeierstrassCurve.Affine.Point.X_eq_iff).mp
                  hxResidue
            exact hor.elim heq hinv
          have hsecant :=
            finiteReducePoint_add_of_integral_residue_x_ne
              A B xInt yInt XInt YInt hP hQ hxRed
          simpa only [xInt, yInt, XInt, YInt] using hsecant

/-! ## The two actual split maps and packaged interfaces -/

theorem plusA_residue_val :
    (PadicInt.toZMod plusA).val = plusCoefficients.1 := by
  have ha : PadicInt.toZMod plusA = (12 : ZMod 37) := by
    change (localResidueCurve plusA plusB).a₂ = 12
    rw [localResidueCurve_plus_eq]
    exact gaussianE0ResiduePlus_coefficients.2.1
  rw [ha, plusGroupRow.1]
  native_decide

theorem plusB_residue_val :
    (PadicInt.toZMod plusB).val = plusCoefficients.2 := by
  have hb : PadicInt.toZMod plusB = (11 : ZMod 37) := by
    change (localResidueCurve plusA plusB).a₄ = 11
    rw [localResidueCurve_plus_eq]
    exact gaussianE0ResiduePlus_coefficients.2.2.2.1
  rw [hb, plusGroupRow.1]
  native_decide

theorem minusA_residue_val :
    (PadicInt.toZMod minusA).val = minusCoefficients.1 := by
  have ha : PadicInt.toZMod minusA = (25 : ZMod 37) := by
    change (localResidueCurve minusA minusB).a₂ = 25
    rw [localResidueCurve_minus_eq]
    exact gaussianE0ResidueMinus_coefficients.2.1
  rw [ha, minusGroupRow.1]
  native_decide

theorem minusB_residue_val :
    (PadicInt.toZMod minusB).val = minusCoefficients.2 := by
  have hb : PadicInt.toZMod minusB = (22 : ZMod 37) := by
    change (localResidueCurve minusA minusB).a₄ = 22
    rw [localResidueCurve_minus_eq]
    exact gaussianE0ResidueMinus_coefficients.2.2.2.1
  rw [hb, minusGroupRow.1]
  native_decide

theorem reduceE0Plus_add (Q R : E0Point) :
    reduceE0Plus (Q + R) =
      finiteAdd 37 plusCoefficients.1 plusCoefficients.2
        (reduceE0Plus Q) (reduceE0Plus R) := by
  change
    finiteReducePoint plusA plusB (mapE0PointPlusLocal (Q + R)) =
      finiteAdd 37 plusCoefficients.1 plusCoefficients.2
        (finiteReducePoint plusA plusB (mapE0PointPlusLocal Q))
        (finiteReducePoint plusA plusB (mapE0PointPlusLocal R))
  rw [mapE0PointPlusLocal_add,
    finiteReducePoint_add, plusA_residue_val, plusB_residue_val]

theorem reduceE0Minus_add (Q R : E0Point) :
    reduceE0Minus (Q + R) =
      finiteAdd 37 minusCoefficients.1 minusCoefficients.2
        (reduceE0Minus Q) (reduceE0Minus R) := by
  change
    finiteReducePoint minusA minusB (mapE0PointMinusLocal (Q + R)) =
      finiteAdd 37 minusCoefficients.1 minusCoefficients.2
        (finiteReducePoint minusA minusB (mapE0PointMinusLocal Q))
        (finiteReducePoint minusA minusB (mapE0PointMinusLocal R))
  rw [mapE0PointMinusLocal_add,
    finiteReducePoint_add, minusA_residue_val, minusB_residue_val]

/-- The unconditional pair of actual split-37 good-reduction maps. -/
def split37GoodReductionActual : Split37GoodReduction where
  plus := reduceE0Plus
  minus := reduceE0Minus
  plus_zero := reduceE0Plus_zero
  minus_zero := reduceE0Minus_zero
  plus_add := reduceE0Plus_add
  minus_add := reduceE0Minus_add
  plus_neg := reduceE0Plus_neg
  minus_neg := reduceE0Minus_neg
  plus_P := reduceE0Plus_gaussianE0P
  minus_P := reduceE0Minus_gaussianE0P
  plus_T := reduceE0Plus_gaussianE0T
  minus_T := reduceE0Minus_gaussianE0T

/-- The unconditional projective split-37 reduction, including the common
reduced abscissa for points with rational Gaussian `x`. -/
def split37ProjectiveReductionActual : Split37ProjectiveReduction where
  toSplit37GoodReduction := split37GoodReductionActual
  commonX_of_rational := by
    intro Q hxRat
    rcases reduceE0_common_of_rational Q hxRat with
      hInfinity | ⟨x, yPlus, yMinus, hPlus, hMinus⟩
    · exact .infinity hInfinity.1 hInfinity.2
    · exact .affine x yPlus yMinus hPlus hMinus

/-- The actual cover valuation consequences, attached to the actual
projective reduction maps. -/
def split37CoverReductionActual : Split37CoverReduction where
  toSplit37ProjectiveReduction := split37ProjectiveReductionActual
  infinity_forces_leading_square :=
    infinity_forces_leading_square_actual
  torsion_forces_q0_square :=
    torsion_forces_q0_square_actual

/-! ## Membership in the exhaustive finite point tables -/

/-- Every proof-carrying special-fibre point occurs in the exhaustive
`finitePoints` table under its canonical representatives. -/
theorem finitePointOfResidue_mem_finitePoints
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (R : (localResidueCurve A B).toAffine.Point) :
    finitePointOfResidue R ∈
      finitePoints 37 (PadicInt.toZMod A).val
        (PadicInt.toZMod B).val := by
  rcases R with (_ | ⟨x, y, hR⟩)
  · simp [finitePointOfResidue, finitePoints]
  · have hEq := hR.1
    rw [WeierstrassCurve.Affine.equation_iff] at hEq
    simp only [localResidueCurve, localCurve,
      WeierstrassCurve.map, map_zero, zero_mul, add_zero] at hEq
    have hCurve :
        y.val ^ 2 % 37 =
          finiteCurveRhs 37 (PadicInt.toZMod A).val
            (PadicInt.toZMod B).val x.val := by
      calc
        y.val ^ 2 % 37 = (y ^ 2).val :=
          residuePowTwo_val_37 y
        _ =
            (x ^ 3 + PadicInt.toZMod A * x ^ 2 +
              PadicInt.toZMod B * x).val :=
          congrArg ZMod.val hEq
        _ =
            finiteCurveRhs 37 (PadicInt.toZMod A).val
              (PadicInt.toZMod B).val x.val :=
          (finiteCurveRhs_val_37
            (PadicInt.toZMod A) (PadicInt.toZMod B) x).symm
    simp only [finitePointOfResidue, finitePoints,
      List.mem_cons, Option.some.injEq, reduceCtorEq, false_or,
      List.mem_flatMap]
    refine ⟨x.val, List.mem_range.mpr x.val_lt, ?_⟩
    simp only [List.mem_filterMap]
    refine ⟨y.val, List.mem_range.mpr y.val_lt, ?_⟩
    rw [if_pos hCurve]

/-- Every executable reduction belongs to the exhaustive finite table. -/
theorem finiteReducePoint_mem_finitePoints
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : (localPadicCurve A B).toAffine.Point) :
    finiteReducePoint A B P ∈
      finitePoints 37 (PadicInt.toZMod A).val
        (PadicInt.toZMod B).val :=
  finitePointOfResidue_mem_finitePoints A B (reducePoint A B P)

theorem reduceE0Plus_mem_finitePoints (Q : E0Point) :
    reduceE0Plus Q ∈
      finitePoints 37 plusCoefficients.1 plusCoefficients.2 := by
  rw [← plusA_residue_val, ← plusB_residue_val]
  exact
    finiteReducePoint_mem_finitePoints
      plusA plusB (mapE0PointPlusLocal Q)

theorem reduceE0Minus_mem_finitePoints (Q : E0Point) :
    reduceE0Minus Q ∈
      finitePoints 37 minusCoefficients.1 minusCoefficients.2 := by
  rw [← minusA_residue_val, ← minusB_residue_val]
  exact
    finiteReducePoint_mem_finitePoints
      minusA minusB (mapE0PointMinusLocal Q)

end

end GaussianSplit37ReductionActual
end Cuboid2
