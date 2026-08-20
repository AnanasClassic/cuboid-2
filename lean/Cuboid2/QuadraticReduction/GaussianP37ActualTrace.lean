import Cuboid2.QuadraticReduction.GaussianFormalLocal
import Cuboid2.QuadraticReduction.GaussianP37

/-!
# The actual `37²` trace of the visible point

This module connects the closed projective computations modulo `37²` to
weighted coordinates over `ℤ_[37]`.  The latter represent actual points on
the two local elliptic curves, so the finite rows remain certificates rather
than hypotheses.
-/

namespace Cuboid2
namespace GaussianP37ActualTrace

noncomputable section

open GaussianGoodReduction GaussianProjectiveReduction GaussianP37

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

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

local instance : DecidableEq ℚ_[37] := Classical.decEq _

private theorem toZModPow_one_eq_toZMod :
    (@PadicInt.toZModPow 37 inferInstance 1) =
      (PadicInt.toZMod : ℤ_[37] →+* ZMod 37) := by
  apply ZMod.ringHom_eq_of_ker_eq
  rw [PadicInt.ker_toZModPow, pow_one, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p]

private theorem plus_root_lift_unique
    (z : ZMod 1369) (hsq : z ^ 2 = -1)
    (hres : ZMod.cast z = (6 : ZMod 37)) :
    z = 117 := by
  revert z
  native_decide

private theorem minus_root_lift_unique
    (z : ZMod 1369) (hsq : z ^ 2 = -1)
    (hres : ZMod.cast z = (31 : ZMod 37)) :
    z = 1252 := by
  revert z
  native_decide

/-- The Hensel root used by the actual plus embedding is the certified lift
`117` modulo `37²`. -/
theorem splitRootPlus_toZModPow_two :
    PadicInt.toZModPow 2 splitRootPlus = (117 : ZMod 1369) := by
  apply plus_root_lift_unique
  · rw [← map_pow, splitRootPlus_sq, map_neg, map_one]
  · rw [PadicInt.cast_toZModPow 1 2 (by omega),
      toZModPow_one_eq_toZMod, splitRootPlus_toZMod]

/-- The actual minus embedding uses the other certified lift `1252`. -/
theorem splitRootMinus_toZModPow_two :
    PadicInt.toZModPow 2 splitRootMinus = (1252 : ZMod 1369) := by
  apply minus_root_lift_unique
  · rw [← map_pow, splitRootMinus_sq, map_neg, map_one]
  · rw [PadicInt.cast_toZModPow 1 2 (by omega),
      toZModPow_one_eq_toZMod, splitRootMinus_toZMod]

/-- Weighted integral coordinates with affine chart
`x = X / Z²`, `y = Y / Z³`. -/
structure IntegralWeightedPoint where
  X : ℤ_[37]
  Y : ℤ_[37]
  Z : ℤ_[37]

/-- Denominator-free doubling on the integral two-torsion model. -/
def weightedDouble
    (A B : ℤ_[37]) (P : IntegralWeightedPoint) :
    IntegralWeightedPoint :=
  let M :=
    3 * P.X ^ 2 + 2 * A * P.X * P.Z ^ 2 + B * P.Z ^ 4
  let X :=
    M ^ 2 - (A * P.Z ^ 2 + 2 * P.X) * (2 * P.Y) ^ 2
  let Y :=
    M * (4 * P.Y ^ 2 * P.X - X) - 8 * P.Y ^ 4
  let Z := 2 * P.Y * P.Z
  ⟨X, Y, Z⟩

/-- Denominator-free mixed addition by `(2,2)`. -/
def weightedAddP
    (A _B : ℤ_[37]) (P : IntegralWeightedPoint) :
    IntegralWeightedPoint :=
  let E := P.X - 2 * P.Z ^ 2
  let N := P.Y - 2 * P.Z ^ 3
  let D := P.Z * E
  let X := N ^ 2 - (A + 2) * D ^ 2 - P.X * E ^ 2
  let Y := -N * (X - P.X * E ^ 2) - P.Y * E ^ 3
  ⟨X, Y, D⟩

/-- The fixed projective chain `P → 2P → 3P → 6P → 12P`. -/
def weightedP1 : IntegralWeightedPoint := ⟨2, 2, 1⟩

def weightedP2 (A B : ℤ_[37]) : IntegralWeightedPoint :=
  weightedDouble A B weightedP1

def weightedP3 (A B : ℤ_[37]) : IntegralWeightedPoint :=
  weightedAddP A B (weightedP2 A B)

def weightedP6 (A B : ℤ_[37]) : IntegralWeightedPoint :=
  weightedDouble A B (weightedP3 A B)

def weightedP12 (A B : ℤ_[37]) : IntegralWeightedPoint :=
  weightedDouble A B (weightedP6 A B)

/-- The affine formal parameter represented by weighted coordinates. -/
def weightedParameter (P : IntegralWeightedPoint) : ℚ_[37] :=
  -(P.X : ℚ_[37]) * (P.Z : ℚ_[37]) / (P.Y : ℚ_[37])

/-- Affine abscissa represented by a nonzero weighted denominator. -/
def weightedX (P : IntegralWeightedPoint) : ℚ_[37] :=
  (P.X : ℚ_[37]) / (P.Z : ℚ_[37]) ^ 2

/-- Affine ordinate represented by a nonzero weighted denominator. -/
def weightedY (P : IntegralWeightedPoint) : ℚ_[37] :=
  (P.Y : ℚ_[37]) / (P.Z : ℚ_[37]) ^ 3

private theorem weightedDouble_represents_double
    (A B : ℤ_[37]) (P : IntegralWeightedPoint)
    (hZ : (P.Z : ℚ_[37]) ≠ 0)
    (hY : (P.Y : ℚ_[37]) ≠ 0)
    (hpoint :
      (localPadicCurve A B).toAffine.Nonsingular
        (weightedX P) (weightedY P)) :
    ∃ hdouble :
        (localPadicCurve A B).toAffine.Nonsingular
          (weightedX (weightedDouble A B P))
          (weightedY (weightedDouble A B P)),
      2 •
          (WeierstrassCurve.Affine.Point.some
            (weightedX P) (weightedY P) hpoint) =
        .some
          (weightedX (weightedDouble A B P))
          (weightedY (weightedDouble A B P)) hdouble := by
  let W := (localPadicCurve A B).toAffine
  have hyAff : weightedY P ≠ 0 := by
    exact div_ne_zero hY (pow_ne_zero 3 hZ)
  have hyNeg :
      weightedY P ≠ W.negY (weightedX P) (weightedY P) := by
    dsimp [W, localPadicCurve, localCurve]
    simp only [WeierstrassCurve.map, map_zero, zero_mul, sub_zero]
    change weightedY P ≠ -weightedY P
    intro h
    have htwo : (2 : ℚ_[37]) * weightedY P = 0 := by
      linear_combination h
    exact hyAff ((mul_eq_zero.mp htwo).resolve_left (by norm_num))
  let slope :=
    W.slope (weightedX P) (weightedX P)
      (weightedY P) (weightedY P)
  have hslope :
      slope =
        (3 * weightedX P ^ 2 +
            2 * (A : ℚ_[37]) * weightedX P + (B : ℚ_[37])) /
          (2 * weightedY P) := by
    dsimp [slope]
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyNeg]
    simp only [W, localPadicCurve, localCurve, WeierstrassCurve.map,
      WeierstrassCurve.Affine.negY, map_zero, zero_mul, sub_zero]
    change
      (3 * weightedX P ^ 2 +
          2 * (A : ℚ_[37]) * weightedX P + (B : ℚ_[37])) /
          (weightedY P - -weightedY P) =
        (3 * weightedX P ^ 2 +
          2 * (A : ℚ_[37]) * weightedX P + (B : ℚ_[37])) /
          (2 * weightedY P)
    ring
  have hx :
      W.addX (weightedX P) (weightedX P) slope =
        weightedX (weightedDouble A B P) := by
    rw [hslope]
    simp only [W, localPadicCurve, localCurve, WeierstrassCurve.map,
      WeierstrassCurve.Affine.addX, weightedX, weightedY,
      weightedDouble, map_zero, zero_mul, add_zero]
    change
      ((3 * ((P.X : ℚ_[37]) / (P.Z : ℚ_[37]) ^ 2) ^ 2 +
              2 * (A : ℚ_[37]) *
                ((P.X : ℚ_[37]) / (P.Z : ℚ_[37]) ^ 2) +
              (B : ℚ_[37])) /
            (2 * ((P.Y : ℚ_[37]) / (P.Z : ℚ_[37]) ^ 3))) ^ 2 -
            (A : ℚ_[37]) -
            ((P.X : ℚ_[37]) / (P.Z : ℚ_[37]) ^ 2) -
          ((P.X : ℚ_[37]) / (P.Z : ℚ_[37]) ^ 2) =
        ((3 * (P.X : ℚ_[37]) ^ 2 +
                2 * (A : ℚ_[37]) * (P.X : ℚ_[37]) *
                  (P.Z : ℚ_[37]) ^ 2 +
                (B : ℚ_[37]) * (P.Z : ℚ_[37]) ^ 4) ^ 2 -
            ((A : ℚ_[37]) * (P.Z : ℚ_[37]) ^ 2 +
                2 * (P.X : ℚ_[37])) *
              (2 * (P.Y : ℚ_[37])) ^ 2) /
          (2 * (P.Y : ℚ_[37]) * (P.Z : ℚ_[37])) ^ 2
    field_simp [hZ, hY]
    ring
  have hy :
      W.addY (weightedX P) (weightedX P) (weightedY P) slope =
        weightedY (weightedDouble A B P) := by
    have haddY :
        W.addY (weightedX P) (weightedX P) (weightedY P) slope =
          -(slope *
              (W.addX (weightedX P) (weightedX P) slope -
                weightedX P) + weightedY P) := by
      simp [W, localPadicCurve, localCurve,
        WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.negAddY]
    rw [haddY, hx, hslope]
    change
      -(((3 * ((P.X : ℚ_[37]) / (P.Z : ℚ_[37]) ^ 2) ^ 2 +
                2 * (A : ℚ_[37]) *
                  ((P.X : ℚ_[37]) / (P.Z : ℚ_[37]) ^ 2) +
                (B : ℚ_[37])) /
              (2 * ((P.Y : ℚ_[37]) / (P.Z : ℚ_[37]) ^ 3))) *
            (((3 * (P.X : ℚ_[37]) ^ 2 +
                    2 * (A : ℚ_[37]) * (P.X : ℚ_[37]) *
                      (P.Z : ℚ_[37]) ^ 2 +
                    (B : ℚ_[37]) * (P.Z : ℚ_[37]) ^ 4) ^ 2 -
                ((A : ℚ_[37]) * (P.Z : ℚ_[37]) ^ 2 +
                    2 * (P.X : ℚ_[37])) *
                  (2 * (P.Y : ℚ_[37])) ^ 2) /
                (2 * (P.Y : ℚ_[37]) * (P.Z : ℚ_[37])) ^ 2 -
              (P.X : ℚ_[37]) / (P.Z : ℚ_[37]) ^ 2) +
          (P.Y : ℚ_[37]) / (P.Z : ℚ_[37]) ^ 3) =
        ((3 * (P.X : ℚ_[37]) ^ 2 +
                2 * (A : ℚ_[37]) * (P.X : ℚ_[37]) *
                  (P.Z : ℚ_[37]) ^ 2 +
                (B : ℚ_[37]) * (P.Z : ℚ_[37]) ^ 4) *
              (4 * (P.Y : ℚ_[37]) ^ 2 * (P.X : ℚ_[37]) -
                ((3 * (P.X : ℚ_[37]) ^ 2 +
                        2 * (A : ℚ_[37]) * (P.X : ℚ_[37]) *
                          (P.Z : ℚ_[37]) ^ 2 +
                        (B : ℚ_[37]) * (P.Z : ℚ_[37]) ^ 4) ^ 2 -
                  ((A : ℚ_[37]) * (P.Z : ℚ_[37]) ^ 2 +
                      2 * (P.X : ℚ_[37])) *
                    (2 * (P.Y : ℚ_[37])) ^ 2)) -
            8 * (P.Y : ℚ_[37]) ^ 4) /
          (2 * (P.Y : ℚ_[37]) * (P.Z : ℚ_[37])) ^ 3
    field_simp [hZ, hY]
    ring
  have hnew :
      W.Nonsingular
        (W.addX (weightedX P) (weightedX P) slope)
        (W.addY (weightedX P) (weightedX P) (weightedY P) slope) :=
    WeierstrassCurve.Affine.nonsingular_add
      hpoint hpoint (fun h => hyNeg h.right)
  have hdouble :
      W.Nonsingular
        (weightedX (weightedDouble A B P))
        (weightedY (weightedDouble A B P)) := by
    rwa [← hx, ← hy]
  refine ⟨hdouble, ?_⟩
  rw [two_nsmul,
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyNeg]
  simp only [slope, hx, hy]

private theorem weightedAddP_represents_add
    (A B : ℤ_[37]) (P : IntegralWeightedPoint)
    (hZ : (P.Z : ℚ_[37]) ≠ 0)
    (hE :
      (P.X : ℚ_[37]) -
          2 * (P.Z : ℚ_[37]) ^ 2 ≠ 0)
    (hpoint :
      (localPadicCurve A B).toAffine.Nonsingular
        (weightedX P) (weightedY P))
    (hP :
      (localPadicCurve A B).toAffine.Nonsingular 2 2) :
    ∃ hadd :
        (localPadicCurve A B).toAffine.Nonsingular
          (weightedX (weightedAddP A B P))
          (weightedY (weightedAddP A B P)),
      (WeierstrassCurve.Affine.Point.some
          (weightedX P) (weightedY P) hpoint) +
          (.some 2 2 hP) =
        .some
          (weightedX (weightedAddP A B P))
          (weightedY (weightedAddP A B P)) hadd := by
  let W := (localPadicCurve A B).toAffine
  have hxTwo : weightedX P ≠ 2 := by
    intro hx
    apply hE
    unfold weightedX at hx
    field_simp [hZ] at hx
    linear_combination hx
  let slope :=
    W.slope (weightedX P) 2 (weightedY P) 2
  have hslope :
      slope =
        ((P.Y : ℚ_[37]) -
            2 * (P.Z : ℚ_[37]) ^ 3) /
          ((P.Z : ℚ_[37]) *
            ((P.X : ℚ_[37]) -
              2 * (P.Z : ℚ_[37]) ^ 2)) := by
    dsimp [slope]
    rw [WeierstrassCurve.Affine.slope_of_X_ne hxTwo]
    unfold weightedX weightedY
    field_simp [hZ, hE]
  have hx :
      W.addX (weightedX P) 2 slope =
        weightedX (weightedAddP A B P) := by
    rw [hslope]
    simp only [W, localPadicCurve, localCurve, WeierstrassCurve.map,
      WeierstrassCurve.Affine.addX, weightedX, weightedAddP,
      map_zero, zero_mul, add_zero]
    change
      (((P.Y : ℚ_[37]) -
              2 * (P.Z : ℚ_[37]) ^ 3) /
            ((P.Z : ℚ_[37]) *
              ((P.X : ℚ_[37]) -
                2 * (P.Z : ℚ_[37]) ^ 2))) ^ 2 -
          (A : ℚ_[37]) -
          (P.X : ℚ_[37]) / (P.Z : ℚ_[37]) ^ 2 - 2 =
        (((P.Y : ℚ_[37]) -
                2 * (P.Z : ℚ_[37]) ^ 3) ^ 2 -
            ((A : ℚ_[37]) + 2) *
              ((P.Z : ℚ_[37]) *
                ((P.X : ℚ_[37]) -
                  2 * (P.Z : ℚ_[37]) ^ 2)) ^ 2 -
            (P.X : ℚ_[37]) *
              ((P.X : ℚ_[37]) -
                2 * (P.Z : ℚ_[37]) ^ 2) ^ 2) /
          ((P.Z : ℚ_[37]) *
            ((P.X : ℚ_[37]) -
              2 * (P.Z : ℚ_[37]) ^ 2)) ^ 2
    field_simp [hZ, hE]
    ring
  have hy :
      W.addY (weightedX P) 2 (weightedY P) slope =
        weightedY (weightedAddP A B P) := by
    have haddY :
        W.addY (weightedX P) 2 (weightedY P) slope =
          -(slope *
              (W.addX (weightedX P) 2 slope -
                weightedX P) + weightedY P) := by
      simp [W, localPadicCurve, localCurve,
        WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.negAddY]
    rw [haddY, hx, hslope]
    simp only [weightedX, weightedY, weightedAddP]
    let X : ℚ_[37] := P.X
    let Y : ℚ_[37] := P.Y
    let Z : ℚ_[37] := P.Z
    let a : ℚ_[37] := A
    let E : ℚ_[37] := X - 2 * Z ^ 2
    let N : ℚ_[37] := Y - 2 * Z ^ 3
    let D : ℚ_[37] := Z * E
    let X3 : ℚ_[37] :=
      N ^ 2 - (a + 2) * D ^ 2 - X * E ^ 2
    change
      -(N / D * (X3 / D ^ 2 - X / Z ^ 2) + Y / Z ^ 3) =
        (-N * (X3 - X * E ^ 2) - Y * E ^ 3) / D ^ 3
    have hZ' : Z ≠ 0 := hZ
    have hE' : E ≠ 0 := hE
    field_simp [D, hZ', hE']
    ring
  have hnew :
      W.Nonsingular
        (W.addX (weightedX P) 2 slope)
        (W.addY (weightedX P) 2 (weightedY P) slope) :=
    WeierstrassCurve.Affine.nonsingular_add
      hpoint hP (fun h => hxTwo h.left)
  have hadd :
      W.Nonsingular
        (weightedX (weightedAddP A B P))
        (weightedY (weightedAddP A B P)) := by
    rwa [← hx, ← hy]
  refine ⟨hadd, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxTwo]
  congr 1

private abbrev mod37Sq : ℤ_[37] →+* ZMod 1369 :=
  PadicInt.toZModPow 2

/-- The complete polynomial chain at the plus embedding, reduced modulo
`37²`.  The final triple is projectively equivalent to the one in
`plusFormalParameterTrace` and has the same parameter `629`. -/
theorem plus_weighted_chain_mod37Sq :
    mod37Sq
        ((weightedP2 plusA plusB).X -
          2 * (weightedP2 plusA plusB).Z ^ 2) = 128 ∧
      mod37Sq (weightedP3 plusA plusB).Y = 553 ∧
      mod37Sq (weightedP6 plusA plusB).Y = 296 ∧
      mod37Sq (weightedP12 plusA plusB).X = 860 ∧
      mod37Sq (weightedP12 plusA plusB).Y = 935 ∧
      mod37Sq (weightedP12 plusA plusB).Z = 518 := by
  simp only [mod37Sq, weightedP12, weightedP6, weightedP3, weightedP2,
    weightedP1, weightedDouble, weightedAddP, plusA, plusB,
    gaussianE0IntegralPlus, map_one, map_add, map_sub,
    map_neg, map_mul, map_pow, map_ofNat]
  rw [splitRootPlus_toZModPow_two]
  native_decide

/-- The corresponding closed polynomial chain at the minus embedding. -/
theorem minus_weighted_chain_mod37Sq :
    mod37Sq
        ((weightedP2 minusA minusB).X -
          2 * (weightedP2 minusA minusB).Z ^ 2) = 1217 ∧
      mod37Sq (weightedP3 minusA minusB).Y = 777 ∧
      mod37Sq (weightedP6 minusA minusB).Y = 1022 ∧
      mod37Sq (weightedP12 minusA minusB).X = 490 ∧
      mod37Sq (weightedP12 minusA minusB).Y = 1231 ∧
      mod37Sq (weightedP12 minusA minusB).Z = 740 := by
  simp only [mod37Sq, weightedP12, weightedP6, weightedP3, weightedP2,
    weightedP1, weightedDouble, weightedAddP, minusA, minusB,
    gaussianE0IntegralMinus, map_one, map_add, map_sub,
    map_neg, map_mul, map_pow, map_ofNat]
  rw [splitRootMinus_toZModPow_two]
  native_decide

private theorem ne_zero_of_mod37Sq_ne
    {z : ℤ_[37]} {a : ZMod 1369}
    (hz : mod37Sq z = a) (ha : a ≠ 0) :
    (z : ℚ_[37]) ≠ 0 := by
  intro hzero
  have hzZero : z = 0 := PadicInt.coe_eq_zero.mp hzero
  subst z
  simp only [map_zero] at hz
  exact ha hz.symm

private theorem toZMod_eq_cast_toZModPow_two (z : ℤ_[37]) :
    PadicInt.toZMod z = ZMod.cast (PadicInt.toZModPow 2 z) := by
  rw [← toZModPow_one_eq_toZMod]
  exact (PadicInt.cast_toZModPow 1 2 (by omega) z).symm

private theorem isUnit_of_toZMod_ne_zero
    {z : ℤ_[37]} (hz : PadicInt.toZMod z ≠ 0) :
    IsUnit z := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  rw [← PadicInt.ker_toZMod]
  simpa only [RingHom.mem_ker] using hz

private theorem integral_weighted_parameter_exists
    (P : IntegralWeightedPoint) (hY : IsUnit P.Y) :
    ∃ t : ℤ_[37],
      (t : ℚ_[37]) = weightedParameter P ∧
        t * P.Y = -P.X * P.Z := by
  let t : ℤ_[37] :=
    -P.X * P.Z * ((hY.unit⁻¹ : ℤ_[37]ˣ) : ℤ_[37])
  have htY : t * P.Y = -P.X * P.Z := by
    dsimp [t]
    rw [mul_assoc, hY.val_inv_mul, mul_one]
  have hY0 : (P.Y : ℚ_[37]) ≠ 0 :=
    PadicInt.coe_ne_zero.mpr hY.ne_zero
  refine ⟨t, ?_, htY⟩
  unfold weightedParameter
  apply (eq_div_iff hY0).2
  simpa only [PadicInt.coe_mul, PadicInt.coe_neg] using
    congrArg (fun z : ℤ_[37] => (z : ℚ_[37])) htY

private theorem weightedParameter_eq_neg_x_div_y
    (P : IntegralWeightedPoint)
    (hZ : (P.Z : ℚ_[37]) ≠ 0)
    (hY : (P.Y : ℚ_[37]) ≠ 0) :
    weightedParameter P = -weightedX P / weightedY P := by
  unfold weightedParameter weightedX weightedY
  field_simp [hZ, hY]

private theorem plus_parameter_mod37Sq_unique
    (t : ZMod 1369)
    (ht : t * 935 = -(860 : ZMod 1369) * 518) :
    t = 629 := by
  revert t
  native_decide

private theorem minus_parameter_mod37Sq_unique
    (t : ZMod 1369)
    (ht : t * 1231 = -(490 : ZMod 1369) * 740) :
    t = 703 := by
  revert t
  native_decide

private theorem plus_divided_parameter_residue_unique
    (q : ZMod 1369) (hq : 37 * q = 629) :
    ZMod.cast q = (17 : ZMod 37) := by
  revert q
  native_decide

private theorem minus_divided_parameter_residue_unique
    (q : ZMod 1369) (hq : 37 * q = 703) :
    ZMod.cast q = (19 : ZMod 37) := by
  revert q
  native_decide

private theorem weighted_chain_represents_twelve
    (A B : ℤ_[37])
    (hP : (localPadicCurve A B).toAffine.Nonsingular 2 2)
    (hE2 :
      ((weightedP2 A B).X : ℚ_[37]) -
          2 * ((weightedP2 A B).Z : ℚ_[37]) ^ 2 ≠ 0)
    (hY3 : ((weightedP3 A B).Y : ℚ_[37]) ≠ 0)
    (hY6 : ((weightedP6 A B).Y : ℚ_[37]) ≠ 0) :
    ∃ h12 :
        (localPadicCurve A B).toAffine.Nonsingular
          (weightedX (weightedP12 A B))
          (weightedY (weightedP12 A B)),
      12 • (WeierstrassCurve.Affine.Point.some 2 2 hP) =
        .some
          (weightedX (weightedP12 A B))
          (weightedY (weightedP12 A B)) h12 := by
  have hZ1 : ((weightedP1.Z : ℤ_[37]) : ℚ_[37]) ≠ 0 := by
    norm_num [weightedP1]
  have hY1 : ((weightedP1.Y : ℤ_[37]) : ℚ_[37]) ≠ 0 := by
    norm_num [weightedP1]
  have hX1 : weightedX weightedP1 = (2 : ℚ_[37]) := by
    change
      PadicInt.Coe.ringHom (2 : ℤ_[37]) /
          PadicInt.Coe.ringHom (1 : ℤ_[37]) ^ 2 = 2
    rw [map_ofNat, map_one]
    norm_num
  have hCoordY1 : weightedY weightedP1 = (2 : ℚ_[37]) := by
    change
      PadicInt.Coe.ringHom (2 : ℤ_[37]) /
          PadicInt.Coe.ringHom (1 : ℤ_[37]) ^ 3 = 2
    rw [map_ofNat, map_one]
    norm_num
  have hP1ns :
      (localPadicCurve A B).toAffine.Nonsingular
        (weightedX weightedP1) (weightedY weightedP1) := by
    rw [hX1, hCoordY1]
    exact hP
  have hP1 :
      (WeierstrassCurve.Affine.Point.some 2 2 hP) =
        .some (weightedX weightedP1) (weightedY weightedP1) hP1ns := by
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hX1.symm, hCoordY1.symm⟩
  obtain ⟨hP2, htwo⟩ :=
    weightedDouble_represents_double A B weightedP1 hZ1 hY1
      hP1ns
  have hZ2 : ((weightedP2 A B).Z : ℚ_[37]) ≠ 0 := by
    norm_num [weightedP2, weightedDouble, weightedP1]
  obtain ⟨hP3, hthreeAdd⟩ :=
    weightedAddP_represents_add A B (weightedP2 A B)
      hZ2 hE2 hP2 hP
  have hZ3 : ((weightedP3 A B).Z : ℚ_[37]) ≠ 0 := by
    simp only [weightedP3, weightedAddP, PadicInt.coe_mul,
      PadicInt.coe_sub, PadicInt.coe_pow]
    exact mul_ne_zero hZ2 hE2
  obtain ⟨hP6, hsixDouble⟩ :=
    weightedDouble_represents_double A B (weightedP3 A B)
      hZ3 hY3 hP3
  have hZ6 : ((weightedP6 A B).Z : ℚ_[37]) ≠ 0 := by
    simp only [weightedP6, weightedDouble, PadicInt.coe_mul]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hY3) hZ3
  obtain ⟨hP12, htwelveDouble⟩ :=
    weightedDouble_represents_double A B (weightedP6 A B)
      hZ6 hY6 hP6
  refine ⟨hP12, ?_⟩
  have htwo' :
      2 • (WeierstrassCurve.Affine.Point.some 2 2 hP) =
        .some (weightedX (weightedP2 A B))
          (weightedY (weightedP2 A B)) hP2 := by
    rw [hP1]
    exact htwo
  have hthree :
      3 • (WeierstrassCurve.Affine.Point.some 2 2 hP) =
        .some (weightedX (weightedP3 A B))
          (weightedY (weightedP3 A B)) hP3 := by
    rw [show
      3 • (WeierstrassCurve.Affine.Point.some 2 2 hP) =
        2 • (WeierstrassCurve.Affine.Point.some 2 2 hP) +
          (WeierstrassCurve.Affine.Point.some 2 2 hP) by
      simpa using
        (succ_nsmul
          (WeierstrassCurve.Affine.Point.some 2 2 hP) 2)]
    rw [htwo']
    exact hthreeAdd
  have hsix :
      6 • (WeierstrassCurve.Affine.Point.some 2 2 hP) =
        .some (weightedX (weightedP6 A B))
          (weightedY (weightedP6 A B)) hP6 := by
    rw [show
      6 • (WeierstrassCurve.Affine.Point.some 2 2 hP) =
        2 • (3 • (WeierstrassCurve.Affine.Point.some 2 2 hP)) by
      simpa using
        (mul_nsmul
          (WeierstrassCurve.Affine.Point.some 2 2 hP) 3 2)]
    rw [hthree]
    exact hsixDouble
  rw [show
    12 • (WeierstrassCurve.Affine.Point.some 2 2 hP) =
      2 • (6 • (WeierstrassCurve.Affine.Point.some 2 2 hP)) by
    simpa using
      (mul_nsmul
        (WeierstrassCurve.Affine.Point.some 2 2 hP) 6 2)]
  rw [hsix]
  exact htwelveDouble

private theorem castPoint_some_exists
    {W V : WeierstrassCurve ℚ_[37]} (h : W = V)
    {x y : ℚ_[37]} (hxy : W.toAffine.Nonsingular x y) :
    ∃ hxy' : V.toAffine.Nonsingular x y,
      castPoint h (.some x y hxy) = .some x y hxy' := by
  subst V
  exact ⟨hxy, rfl⟩

/-- The actual plus base change of `P` is `(2,2)` on the normalized model. -/
theorem mapE0PointPlusLocal_gaussianE0P_exists :
    ∃ hxy : (localPadicCurve plusA plusB).toAffine.Nonsingular 2 2,
      mapE0PointPlusLocal gaussianE0P = .some 2 2 hxy := by
  obtain ⟨hxy, hmap⟩ := mapE0PointPlus_gaussianE0P_exists
  obtain ⟨hxy', hcast⟩ :=
    castPoint_some_exists localPadicCurve_plus_eq.symm hxy
  exact ⟨hxy', by
    rw [mapE0PointPlusLocal, hmap, hcast]⟩

/-- The actual minus base change of `P` is `(2,2)` as well. -/
theorem mapE0PointMinusLocal_gaussianE0P_exists :
    ∃ hxy : (localPadicCurve minusA minusB).toAffine.Nonsingular 2 2,
      mapE0PointMinusLocal gaussianE0P = .some 2 2 hxy := by
  obtain ⟨hxy, hmap⟩ := mapE0PointMinus_gaussianE0P_exists
  obtain ⟨hxy', hcast⟩ :=
    castPoint_some_exists localPadicCurve_minus_eq.symm hxy
  exact ⟨hxy', by
    rw [mapE0PointMinusLocal, hmap, hcast]⟩

/-- The closed plus weighted chain represents the actual local point
`12P`, not merely a finite projective trace. -/
theorem plus_twelve_multiple_weighted :
    ∃ h12 :
        (localPadicCurve plusA plusB).toAffine.Nonsingular
          (weightedX (weightedP12 plusA plusB))
          (weightedY (weightedP12 plusA plusB)),
      12 • mapE0PointPlusLocal gaussianE0P =
        .some
          (weightedX (weightedP12 plusA plusB))
          (weightedY (weightedP12 plusA plusB)) h12 := by
  obtain ⟨hP, hmap⟩ := mapE0PointPlusLocal_gaussianE0P_exists
  have hE2 :
      ((weightedP2 plusA plusB).X : ℚ_[37]) -
          2 * ((weightedP2 plusA plusB).Z : ℚ_[37]) ^ 2 ≠ 0 := by
    have h :=
      ne_zero_of_mod37Sq_ne plus_weighted_chain_mod37Sq.1
        (by native_decide : (128 : ZMod 1369) ≠ 0)
    norm_num at h ⊢
    exact h
  have hY3 : ((weightedP3 plusA plusB).Y : ℚ_[37]) ≠ 0 :=
    ne_zero_of_mod37Sq_ne plus_weighted_chain_mod37Sq.2.1
      (by native_decide)
  have hY6 : ((weightedP6 plusA plusB).Y : ℚ_[37]) ≠ 0 :=
    ne_zero_of_mod37Sq_ne plus_weighted_chain_mod37Sq.2.2.1
      (by native_decide)
  obtain ⟨h12, htwelve⟩ :=
    weighted_chain_represents_twelve plusA plusB hP hE2 hY3 hY6
  refine ⟨h12, ?_⟩
  rw [hmap]
  exact htwelve

/-- The minus closed weighted chain likewise represents the actual local
point `12P`. -/
theorem minus_twelve_multiple_weighted :
    ∃ h12 :
        (localPadicCurve minusA minusB).toAffine.Nonsingular
          (weightedX (weightedP12 minusA minusB))
          (weightedY (weightedP12 minusA minusB)),
      12 • mapE0PointMinusLocal gaussianE0P =
        .some
          (weightedX (weightedP12 minusA minusB))
          (weightedY (weightedP12 minusA minusB)) h12 := by
  obtain ⟨hP, hmap⟩ := mapE0PointMinusLocal_gaussianE0P_exists
  have hE2 :
      ((weightedP2 minusA minusB).X : ℚ_[37]) -
          2 * ((weightedP2 minusA minusB).Z : ℚ_[37]) ^ 2 ≠ 0 := by
    have h :=
      ne_zero_of_mod37Sq_ne minus_weighted_chain_mod37Sq.1
        (by native_decide : (1217 : ZMod 1369) ≠ 0)
    norm_num at h ⊢
    exact h
  have hY3 : ((weightedP3 minusA minusB).Y : ℚ_[37]) ≠ 0 :=
    ne_zero_of_mod37Sq_ne minus_weighted_chain_mod37Sq.2.1
      (by native_decide)
  have hY6 : ((weightedP6 minusA minusB).Y : ℚ_[37]) ≠ 0 :=
    ne_zero_of_mod37Sq_ne minus_weighted_chain_mod37Sq.2.2.1
      (by native_decide)
  obtain ⟨h12, htwelve⟩ :=
    weighted_chain_represents_twelve minusA minusB hP hE2 hY3 hY6
  refine ⟨h12, ?_⟩
  rw [hmap]
  exact htwelve

/-- For the actual plus local point `12P`, the formal parameter `t = -x/y`
is divisible by `37`, and its quotient has first residue `17`. -/
theorem plus_actual_formal_parameter_first_layer :
    ∃ (h12 :
        (localPadicCurve plusA plusB).toAffine.Nonsingular
          (weightedX (weightedP12 plusA plusB))
          (weightedY (weightedP12 plusA plusB)))
      (t q : ℤ_[37]),
      12 • mapE0PointPlusLocal gaussianE0P =
          .some
            (weightedX (weightedP12 plusA plusB))
            (weightedY (weightedP12 plusA plusB)) h12 ∧
        (t : ℚ_[37]) =
          -weightedX (weightedP12 plusA plusB) /
            weightedY (weightedP12 plusA plusB) ∧
        PadicInt.toZModPow 2 t =
          (projectiveParameter 1369
            (projectiveDoubleTrace 1369 234 899 655 370) :
              ZMod 1369) ∧
        t = 37 * q ∧
        PadicInt.toZMod q = (17 : ZMod 37) := by
  obtain ⟨h12, hpoint⟩ := plus_twelve_multiple_weighted
  rcases plus_weighted_chain_mod37Sq with
    ⟨_hE2, _hY3, _hY6, hX, hY, hZ⟩
  have hYres :
      PadicInt.toZMod (weightedP12 plusA plusB).Y =
        (10 : ZMod 37) := by
    rw [toZMod_eq_cast_toZModPow_two, hY]
    native_decide
  have hYunit : IsUnit (weightedP12 plusA plusB).Y :=
    isUnit_of_toZMod_ne_zero (by
      rw [hYres]
      native_decide)
  have hY0 : ((weightedP12 plusA plusB).Y : ℚ_[37]) ≠ 0 :=
    PadicInt.coe_ne_zero.mpr hYunit.ne_zero
  have hZ0 : ((weightedP12 plusA plusB).Z : ℚ_[37]) ≠ 0 :=
    ne_zero_of_mod37Sq_ne hZ (by native_decide)
  obtain ⟨t, htParameter, htProduct⟩ :=
    integral_weighted_parameter_exists
      (weightedP12 plusA plusB) hYunit
  have htMod : mod37Sq t = (629 : ZMod 1369) := by
    apply plus_parameter_mod37Sq_unique
    calc
      mod37Sq t * 935 =
          mod37Sq t * mod37Sq (weightedP12 plusA plusB).Y := by
            rw [hY]
      _ = mod37Sq (t * (weightedP12 plusA plusB).Y) := by
            rw [map_mul]
      _ = mod37Sq
          (-((weightedP12 plusA plusB).X) *
            (weightedP12 plusA plusB).Z) := by
              rw [htProduct]
      _ = -(860 : ZMod 1369) * 518 := by
            rw [map_mul, map_neg, hX, hZ]
  have htRes : PadicInt.toZMod t = (0 : ZMod 37) := by
    rw [toZMod_eq_cast_toZModPow_two, htMod]
    native_decide
  have htDvd : (37 : ℤ_[37]) ∣ t := by
    have htKer :
        t ∈ RingHom.ker
          (PadicInt.toZMod : ℤ_[37] →+* ZMod 37) :=
      RingHom.mem_ker.mpr htRes
    have htSpan :
        t ∈
          (Ideal.span {(↑(37 : ℕ) : ℤ_[37])} :
            Ideal ℤ_[37]) := by
      rw [← PadicInt.maximalIdeal_eq_span_p,
        ← PadicInt.ker_toZMod]
      exact htKer
    exact Ideal.mem_span_singleton.mp htSpan
  obtain ⟨q, hq⟩ := htDvd
  have hqMod :
      (37 : ZMod 1369) * mod37Sq q = 629 := by
    calc
      (37 : ZMod 1369) * mod37Sq q =
          mod37Sq ((37 : ℤ_[37]) * q) := by
            rw [map_mul, map_ofNat]
      _ = mod37Sq t := by rw [hq]
      _ = 629 := htMod
  have hqRes : PadicInt.toZMod q = (17 : ZMod 37) := by
    rw [toZMod_eq_cast_toZModPow_two]
    exact plus_divided_parameter_residue_unique _ hqMod
  have htCertificate :
      PadicInt.toZModPow 2 t =
        (projectiveParameter 1369
          (projectiveDoubleTrace 1369 234 899 655 370) :
            ZMod 1369) := by
    have hCertificate :
        projectiveParameter 1369
          (projectiveDoubleTrace 1369 234 899 655 370) = 629 :=
      plusFormalParameterTrace.2.2.2.2.2.1
    simpa only [hCertificate, Nat.cast_ofNat] using htMod
  refine ⟨h12, t, q, hpoint, ?_, htCertificate, hq, hqRes⟩
  exact
    htParameter.trans
      (weightedParameter_eq_neg_x_div_y _ hZ0 hY0)

/-- For the actual minus local point `12P`, the corresponding first formal
parameter quotient has residue `19`. -/
theorem minus_actual_formal_parameter_first_layer :
    ∃ (h12 :
        (localPadicCurve minusA minusB).toAffine.Nonsingular
          (weightedX (weightedP12 minusA minusB))
          (weightedY (weightedP12 minusA minusB)))
      (t q : ℤ_[37]),
      12 • mapE0PointMinusLocal gaussianE0P =
          .some
            (weightedX (weightedP12 minusA minusB))
            (weightedY (weightedP12 minusA minusB)) h12 ∧
        (t : ℚ_[37]) =
          -weightedX (weightedP12 minusA minusB) /
            weightedY (weightedP12 minusA minusB) ∧
        PadicInt.toZModPow 2 t =
          (weightedProjectiveParameter 1369
            (projectiveDouble 1369 1135 466
              (projectiveDoubleTrace 1369 1135 466 0 444).toWeightedPoint) :
                ZMod 1369) ∧
        t = 37 * q ∧
        PadicInt.toZMod q = (19 : ZMod 37) := by
  obtain ⟨h12, hpoint⟩ := minus_twelve_multiple_weighted
  rcases minus_weighted_chain_mod37Sq with
    ⟨_hE2, _hY3, _hY6, hX, hY, hZ⟩
  have hYres :
      PadicInt.toZMod (weightedP12 minusA minusB).Y =
        (10 : ZMod 37) := by
    rw [toZMod_eq_cast_toZModPow_two, hY]
    native_decide
  have hYunit : IsUnit (weightedP12 minusA minusB).Y :=
    isUnit_of_toZMod_ne_zero (by
      rw [hYres]
      native_decide)
  have hY0 : ((weightedP12 minusA minusB).Y : ℚ_[37]) ≠ 0 :=
    PadicInt.coe_ne_zero.mpr hYunit.ne_zero
  have hZ0 : ((weightedP12 minusA minusB).Z : ℚ_[37]) ≠ 0 :=
    ne_zero_of_mod37Sq_ne hZ (by native_decide)
  obtain ⟨t, htParameter, htProduct⟩ :=
    integral_weighted_parameter_exists
      (weightedP12 minusA minusB) hYunit
  have htMod : mod37Sq t = (703 : ZMod 1369) := by
    apply minus_parameter_mod37Sq_unique
    calc
      mod37Sq t * 1231 =
          mod37Sq t * mod37Sq (weightedP12 minusA minusB).Y := by
            rw [hY]
      _ = mod37Sq (t * (weightedP12 minusA minusB).Y) := by
            rw [map_mul]
      _ = mod37Sq
          (-((weightedP12 minusA minusB).X) *
            (weightedP12 minusA minusB).Z) := by
              rw [htProduct]
      _ = -(490 : ZMod 1369) * 740 := by
            rw [map_mul, map_neg, hX, hZ]
  have htRes : PadicInt.toZMod t = (0 : ZMod 37) := by
    rw [toZMod_eq_cast_toZModPow_two, htMod]
    native_decide
  have htDvd : (37 : ℤ_[37]) ∣ t := by
    have htKer :
        t ∈ RingHom.ker
          (PadicInt.toZMod : ℤ_[37] →+* ZMod 37) :=
      RingHom.mem_ker.mpr htRes
    have htSpan :
        t ∈
          (Ideal.span {(↑(37 : ℕ) : ℤ_[37])} :
            Ideal ℤ_[37]) := by
      rw [← PadicInt.maximalIdeal_eq_span_p,
        ← PadicInt.ker_toZMod]
      exact htKer
    exact Ideal.mem_span_singleton.mp htSpan
  obtain ⟨q, hq⟩ := htDvd
  have hqMod :
      (37 : ZMod 1369) * mod37Sq q = 703 := by
    calc
      (37 : ZMod 1369) * mod37Sq q =
          mod37Sq ((37 : ℤ_[37]) * q) := by
            rw [map_mul, map_ofNat]
      _ = mod37Sq t := by rw [hq]
      _ = 703 := htMod
  have hqRes : PadicInt.toZMod q = (19 : ZMod 37) := by
    rw [toZMod_eq_cast_toZModPow_two]
    exact minus_divided_parameter_residue_unique _ hqMod
  have htCertificate :
      PadicInt.toZModPow 2 t =
        (weightedProjectiveParameter 1369
          (projectiveDouble 1369 1135 466
            (projectiveDoubleTrace 1369 1135 466 0 444).toWeightedPoint) :
              ZMod 1369) := by
    have hCertificate :
        weightedProjectiveParameter 1369
          (projectiveDouble 1369 1135 466
            (projectiveDoubleTrace 1369 1135 466 0 444).toWeightedPoint) =
              703 :=
      minusFormalParameterTrace.2.2.2.2.2.2.2.2.2.1
    simpa only [hCertificate, Nat.cast_ofNat] using htMod
  refine ⟨h12, t, q, hpoint, ?_, htCertificate, hq, hqRes⟩
  exact
    htParameter.trans
      (weightedParameter_eq_neg_x_div_y _ hZ0 hY0)

end

end GaussianP37ActualTrace
end Cuboid2
