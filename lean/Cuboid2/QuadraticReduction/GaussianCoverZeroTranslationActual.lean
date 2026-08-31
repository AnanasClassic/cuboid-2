import Cuboid2.QuadraticReduction.GaussianTranslationSeparation
import Cuboid2.QuadraticReduction.GaussianPairedFormalNorm

/-!
# Actual translated-coordinate separation for the untwisted cover

For an actual point of the untwisted Gaussian cover, the two split
embeddings have the same projective abscissa.  Translating the corresponding
local points back by `P=(2,2)` (or by `-P=(2,-2)`) identifies that common
abscissa with the first-order expressions supplied by the formal
infinity-chart calculation.  Paired formal-parameter separation therefore
makes either translated disk impossible.
-/

namespace Cuboid2
namespace GaussianCoverZeroTranslationActual

noncomputable section

set_option maxHeartbeats 800000

open GaussianFormalKernelDisk
open GaussianFormalKernelTorsion
open GaussianFormalLocal
open GaussianGoodReduction
open GaussianP37ActualTrace
open GaussianP37Bridge
open GaussianProjectiveReduction
open GaussianProjectiveReductionHom
open GaussianPairedFormalNorm
open GaussianTranslationSeparation

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : DecidableEq ℚ_[37] := Classical.decEq _

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have hxnonneg : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance :
    Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

private theorem affine_kernel_x_ne_two
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hmem :
      (.some x y hpoint :
        (localPadicCurve A B).toAffine.Point) ∈
          infinityKernel A B) :
    x ≠ 2 := by
  have hxNorm :
      1 < ‖x‖ :=
    norm_x_gt_one_of_finiteReducePoint_eq_none A B hpoint hmem
  intro hx
  subst x
  have hnormTwo : ‖(2 : ℚ_[37])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [hnormTwo] at hxNorm
  exact (lt_irrefl 1 hxNorm).elim

private theorem translated_xRep_at_P
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hmem :
      (.some x y hpoint :
        (localPadicCurve A B).toAffine.Point) ∈
          infinityKernel A B)
    (hP :
      (localPadicCurve A B).toAffine.Nonsingular 2 2) :
    ((.some x y hpoint + .some 2 2 hP :
        (localPadicCurve A B).toAffine.Point).xRep) 0 =
      ((2 - y) / (2 - x)) ^ 2 - (A : ℚ_[37]) - 2 - x := by
  have hx : x ≠ 2 :=
    affine_kernel_x_ne_two A B hpoint hmem
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx,
    WeierstrassCurve.Affine.Point.xRep_some]
  simp only [Matrix.cons_val_zero]
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp [localPadicCurve, localCurve]
  rw [show PadicInt.Coe.ringHom A = (A : ℚ_[37]) by rfl]
  field_simp [sub_ne_zero.mpr hx, sub_ne_zero.mpr hx.symm]
  all_goals ring

private theorem translated_xRep_at_negP
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hmem :
      (.some x y hpoint :
        (localPadicCurve A B).toAffine.Point) ∈
          infinityKernel A B)
    (hP :
      (localPadicCurve A B).toAffine.Nonsingular 2 (-2)) :
    ((.some x y hpoint + .some 2 (-2) hP :
        (localPadicCurve A B).toAffine.Point).xRep) 0 =
      ((-2 - y) / (2 - x)) ^ 2 - (A : ℚ_[37]) - 2 - x := by
  have hx : x ≠ 2 :=
    affine_kernel_x_ne_two A B hpoint hmem
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx,
    WeierstrassCurve.Affine.Point.xRep_some]
  simp only [Matrix.cons_val_zero]
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp [localPadicCurve, localCurve]
  rw [show PadicInt.Coe.ringHom A = (A : ℚ_[37]) by rfl]
  field_simp [sub_ne_zero.mpr hx, sub_ne_zero.mpr hx.symm]
  all_goals ring

/-- An actual `C₀` point cannot give a paired-separated pair after
translation by `-P`; adding `P` back recovers the same rational-abscissa
global point in both split embeddings. -/
theorem no_pairedKernelSeparated_sub_P
    (C : GaussianCoverZeroPoint) :
    ¬ PairedKernelSeparated
        (mapE0PointPlusLocal (C.toE0 - gaussianE0P))
        (mapE0PointMinusLocal (C.toE0 - gaussianE0P)) := by
  intro H
  cases hPlus :
      mapE0PointPlusLocal (C.toE0 - gaussianE0P) with
  | zero =>
      have hpos := H.norm_pos
      rw [hPlus] at hpos
      simp [parameter] at hpos
  | some xPlus yPlus hpointPlus =>
      cases hMinus :
          mapE0PointMinusLocal (C.toE0 - gaussianE0P) with
      | zero =>
          have hnorm := H.norm_eq
          rw [hMinus] at hnorm
          have hzero :
              ‖parameter plusA plusB
                  (mapE0PointPlusLocal
                    (C.toE0 - gaussianE0P))‖ = 0 := by
            simpa [parameter] using hnorm
          exact (not_lt_of_ge hzero.le) H.norm_pos
      | some xMinus yMinus hpointMinus =>
          have hmemPlus :
              (.some xPlus yPlus hpointPlus :
                  (localPadicCurve plusA plusB).toAffine.Point) ∈
                infinityKernel plusA plusB := by
            rw [← hPlus]
            exact H.plus_mem
          have hmemMinus :
              (.some xMinus yMinus hpointMinus :
                  (localPadicCurve minusA minusB).toAffine.Point) ∈
                infinityKernel minusA minusB := by
            rw [← hMinus]
            exact H.minus_mem
          obtain ⟨hPPlus, hmapPPlus⟩ :=
            mapE0PointPlusLocal_gaussianE0P_exists
          obtain ⟨hPMinus, hmapPMinus⟩ :=
            mapE0PointMinusLocal_gaussianE0P_exists
          obtain
              ⟨tPlus, rPlus, tailPlus, htPlus, _hrPlus,
                htPlusRed, _hrPlusRed, _hformalPlus,
                htranslationPlus⟩ :=
            exists_integral_translation_at_P
              plusA plusB hpointPlus hmemPlus
          obtain
              ⟨tMinus, rMinus, tailMinus, htMinus, _hrMinus,
                htMinusRed, _hrMinusRed, _hformalMinus,
                htranslationMinus⟩ :=
            exists_integral_translation_at_P
              minusA minusB hpointMinus hmemMinus
          have hrecoverPlus :
              (.some xPlus yPlus hpointPlus +
                  .some 2 2 hPPlus :
                (localPadicCurve plusA plusB).toAffine.Point) =
                mapE0PointPlusLocal C.toE0 := by
            calc
              (.some xPlus yPlus hpointPlus +
                    .some 2 2 hPPlus :
                  (localPadicCurve plusA plusB).toAffine.Point) =
                  mapE0PointPlusLocal
                      (C.toE0 - gaussianE0P) +
                    mapE0PointPlusLocal gaussianE0P := by
                rw [hPlus, hmapPPlus]
              _ =
                  mapE0PointPlusLocal
                    ((C.toE0 - gaussianE0P) + gaussianE0P) :=
                (mapE0PointPlusLocal_add _ _).symm
              _ = mapE0PointPlusLocal C.toE0 := by
                rw [sub_add_cancel]
          have hrecoverMinus :
              (.some xMinus yMinus hpointMinus +
                  .some 2 2 hPMinus :
                (localPadicCurve minusA minusB).toAffine.Point) =
                mapE0PointMinusLocal C.toE0 := by
            calc
              (.some xMinus yMinus hpointMinus +
                    .some 2 2 hPMinus :
                  (localPadicCurve minusA minusB).toAffine.Point) =
                  mapE0PointMinusLocal
                      (C.toE0 - gaussianE0P) +
                    mapE0PointMinusLocal gaussianE0P := by
                rw [hMinus, hmapPMinus]
              _ =
                  mapE0PointMinusLocal
                    ((C.toE0 - gaussianE0P) + gaussianE0P) :=
                (mapE0PointMinusLocal_add _ _).symm
              _ = mapE0PointMinusLocal C.toE0 := by
                rw [sub_add_cancel]
          have hxRep :
              ((.some xPlus yPlus hpointPlus +
                    .some 2 2 hPPlus :
                  (localPadicCurve plusA plusB).toAffine.Point).xRep) =
                ((.some xMinus yMinus hpointMinus +
                    .some 2 2 hPMinus :
                  (localPadicCurve minusA minusB).toAffine.Point).xRep) := by
            rw [hrecoverPlus, hrecoverMinus]
            exact
              mapE0PointLocal_xRep_eq_of_rational C.toE0
                (coverZero_toE0_hasRationalAffineX C)
          have htranslatedEq :
              ((2 - yPlus) / (2 - xPlus)) ^ 2 -
                    (plusA : ℚ_[37]) - 2 - xPlus =
                ((2 - yMinus) / (2 - xMinus)) ^ 2 -
                    (minusA : ℚ_[37]) - 2 - xMinus := by
            rw [← translated_xRep_at_P
                plusA plusB hpointPlus hmemPlus hPPlus,
              ← translated_xRep_at_P
                minusA minusB hpointMinus hmemMinus hPMinus]
            exact congrFun hxRep 0
          have hfirstOrderEq :
              2 + 4 * (tPlus : ℚ_[37]) +
                    (tPlus : ℚ_[37]) ^ 2 * (tailPlus : ℚ_[37]) =
                2 + 4 * (tMinus : ℚ_[37]) +
                    (tMinus : ℚ_[37]) ^ 2 * (tailMinus : ℚ_[37]) := by
            rw [← htranslationPlus, ← htranslationMinus]
            exact htranslatedEq
          have htPlusNorm :
              ‖(tPlus : ℚ_[37])‖ =
                ‖parameter plusA plusB
                    (mapE0PointPlusLocal
                      (C.toE0 - gaussianE0P))‖ := by
            rw [hPlus, parameter_some, ← htPlus]
          have htMinusNorm :
              ‖(tMinus : ℚ_[37])‖ =
                ‖parameter plusA plusB
                    (mapE0PointPlusLocal
                      (C.toE0 - gaussianE0P))‖ := by
            rw [H.norm_eq, hMinus, parameter_some, ← htMinus]
          have htSubNorm :
              ‖(tPlus : ℚ_[37]) - (tMinus : ℚ_[37])‖ =
                ‖parameter plusA plusB
                    (mapE0PointPlusLocal
                      (C.toE0 - gaussianE0P))‖ := by
            have hsep := H.norm_sub_eq
            rw [hPlus, hMinus, parameter_some, parameter_some,
              ← htPlus, ← htMinus] at hsep
            exact hsep.trans htPlusNorm
          exact
            (plusFirstOrderTranslations_ne
              tPlus tMinus tailPlus tailMinus
              ‖parameter plusA plusB
                (mapE0PointPlusLocal
                  (C.toE0 - gaussianE0P))‖
              htPlusRed htMinusRed htPlusNorm htMinusNorm htSubNorm
              H.norm_pos) hfirstOrderEq

/-- An actual `C₀` point cannot give a paired-separated pair after
translation by `P`; adding `-P` back again recovers the common
rational-abscissa global point. -/
theorem no_pairedKernelSeparated_add_P
    (C : GaussianCoverZeroPoint) :
    ¬ PairedKernelSeparated
        (mapE0PointPlusLocal (C.toE0 + gaussianE0P))
        (mapE0PointMinusLocal (C.toE0 + gaussianE0P)) := by
  intro H
  cases hPlus :
      mapE0PointPlusLocal (C.toE0 + gaussianE0P) with
  | zero =>
      have hpos := H.norm_pos
      rw [hPlus] at hpos
      simp [parameter] at hpos
  | some xPlus yPlus hpointPlus =>
      cases hMinus :
          mapE0PointMinusLocal (C.toE0 + gaussianE0P) with
      | zero =>
          have hnorm := H.norm_eq
          rw [hMinus] at hnorm
          have hzero :
              ‖parameter plusA plusB
                  (mapE0PointPlusLocal
                    (C.toE0 + gaussianE0P))‖ = 0 := by
            simpa [parameter] using hnorm
          exact (not_lt_of_ge hzero.le) H.norm_pos
      | some xMinus yMinus hpointMinus =>
          have hmemPlus :
              (.some xPlus yPlus hpointPlus :
                  (localPadicCurve plusA plusB).toAffine.Point) ∈
                infinityKernel plusA plusB := by
            rw [← hPlus]
            exact H.plus_mem
          have hmemMinus :
              (.some xMinus yMinus hpointMinus :
                  (localPadicCurve minusA minusB).toAffine.Point) ∈
                infinityKernel minusA minusB := by
            rw [← hMinus]
            exact H.minus_mem
          obtain ⟨hPPlus, hmapPPlus⟩ :=
            mapE0PointPlusLocal_gaussianE0P_exists
          obtain ⟨hPMinus, hmapPMinus⟩ :=
            mapE0PointMinusLocal_gaussianE0P_exists
          have hnegYPlus :
              (localPadicCurve plusA plusB).toAffine.negY 2 2 =
                (-2 : ℚ_[37]) := by
            simp [localPadicCurve, localCurve]
          have hnegYMinus :
              (localPadicCurve minusA minusB).toAffine.negY 2 2 =
                (-2 : ℚ_[37]) := by
            simp [localPadicCurve, localCurve]
          have hPPlusNeg :
              (localPadicCurve plusA plusB).toAffine.Nonsingular
                2 (-2) := by
            rw [← hnegYPlus]
            exact
              ((localPadicCurve plusA plusB).toAffine.nonsingular_neg
                2 2).mpr hPPlus
          have hPMinusNeg :
              (localPadicCurve minusA minusB).toAffine.Nonsingular
                2 (-2) := by
            rw [← hnegYMinus]
            exact
              ((localPadicCurve minusA minusB).toAffine.nonsingular_neg
                2 2).mpr hPMinus
          have hnegPPlus :
              mapE0PointPlusLocal (-gaussianE0P) =
                .some 2 (-2) hPPlusNeg := by
            rw [mapE0PointPlusLocal_neg, hmapPPlus,
              WeierstrassCurve.Affine.Point.neg_some]
            congr 1
          have hnegPMinus :
              mapE0PointMinusLocal (-gaussianE0P) =
                .some 2 (-2) hPMinusNeg := by
            rw [mapE0PointMinusLocal_neg, hmapPMinus,
              WeierstrassCurve.Affine.Point.neg_some]
            congr 1
          obtain
              ⟨tPlus, rPlus, tailPlus, htPlus, _hrPlus,
                htPlusRed, _hrPlusRed, _hformalPlus,
                htranslationPlus⟩ :=
            exists_integral_translation_at_negP
              plusA plusB hpointPlus hmemPlus
          obtain
              ⟨tMinus, rMinus, tailMinus, htMinus, _hrMinus,
                htMinusRed, _hrMinusRed, _hformalMinus,
                htranslationMinus⟩ :=
            exists_integral_translation_at_negP
              minusA minusB hpointMinus hmemMinus
          have hrecoverPlus :
              (.some xPlus yPlus hpointPlus +
                  .some 2 (-2) hPPlusNeg :
                (localPadicCurve plusA plusB).toAffine.Point) =
                mapE0PointPlusLocal C.toE0 := by
            calc
              (.some xPlus yPlus hpointPlus +
                    .some 2 (-2) hPPlusNeg :
                  (localPadicCurve plusA plusB).toAffine.Point) =
                  mapE0PointPlusLocal
                      (C.toE0 + gaussianE0P) +
                    mapE0PointPlusLocal (-gaussianE0P) := by
                rw [hPlus, hnegPPlus]
              _ =
                  mapE0PointPlusLocal
                    ((C.toE0 + gaussianE0P) + (-gaussianE0P)) :=
                (mapE0PointPlusLocal_add _ _).symm
              _ = mapE0PointPlusLocal C.toE0 := by
                rw [add_neg_cancel_right]
          have hrecoverMinus :
              (.some xMinus yMinus hpointMinus +
                  .some 2 (-2) hPMinusNeg :
                (localPadicCurve minusA minusB).toAffine.Point) =
                mapE0PointMinusLocal C.toE0 := by
            calc
              (.some xMinus yMinus hpointMinus +
                    .some 2 (-2) hPMinusNeg :
                  (localPadicCurve minusA minusB).toAffine.Point) =
                  mapE0PointMinusLocal
                      (C.toE0 + gaussianE0P) +
                    mapE0PointMinusLocal (-gaussianE0P) := by
                rw [hMinus, hnegPMinus]
              _ =
                  mapE0PointMinusLocal
                    ((C.toE0 + gaussianE0P) + (-gaussianE0P)) :=
                (mapE0PointMinusLocal_add _ _).symm
              _ = mapE0PointMinusLocal C.toE0 := by
                rw [add_neg_cancel_right]
          have hxRep :
              ((.some xPlus yPlus hpointPlus +
                    .some 2 (-2) hPPlusNeg :
                  (localPadicCurve plusA plusB).toAffine.Point).xRep) =
                ((.some xMinus yMinus hpointMinus +
                    .some 2 (-2) hPMinusNeg :
                  (localPadicCurve minusA minusB).toAffine.Point).xRep) := by
            rw [hrecoverPlus, hrecoverMinus]
            exact
              mapE0PointLocal_xRep_eq_of_rational C.toE0
                (coverZero_toE0_hasRationalAffineX C)
          have htranslatedEq :
              ((-2 - yPlus) / (2 - xPlus)) ^ 2 -
                    (plusA : ℚ_[37]) - 2 - xPlus =
                ((-2 - yMinus) / (2 - xMinus)) ^ 2 -
                    (minusA : ℚ_[37]) - 2 - xMinus := by
            rw [← translated_xRep_at_negP
                plusA plusB hpointPlus hmemPlus hPPlusNeg,
              ← translated_xRep_at_negP
                minusA minusB hpointMinus hmemMinus hPMinusNeg]
            exact congrFun hxRep 0
          have hfirstOrderEq :
              2 - 4 * (tPlus : ℚ_[37]) +
                    (tPlus : ℚ_[37]) ^ 2 * (tailPlus : ℚ_[37]) =
                2 - 4 * (tMinus : ℚ_[37]) +
                    (tMinus : ℚ_[37]) ^ 2 * (tailMinus : ℚ_[37]) := by
            rw [← htranslationPlus, ← htranslationMinus]
            exact htranslatedEq
          have htPlusNorm :
              ‖(tPlus : ℚ_[37])‖ =
                ‖parameter plusA plusB
                    (mapE0PointPlusLocal
                      (C.toE0 + gaussianE0P))‖ := by
            rw [hPlus, parameter_some, ← htPlus]
          have htMinusNorm :
              ‖(tMinus : ℚ_[37])‖ =
                ‖parameter plusA plusB
                    (mapE0PointPlusLocal
                      (C.toE0 + gaussianE0P))‖ := by
            rw [H.norm_eq, hMinus, parameter_some, ← htMinus]
          have htSubNorm :
              ‖(tPlus : ℚ_[37]) - (tMinus : ℚ_[37])‖ =
                ‖parameter plusA plusB
                    (mapE0PointPlusLocal
                      (C.toE0 + gaussianE0P))‖ := by
            have hsep := H.norm_sub_eq
            rw [hPlus, hMinus, parameter_some, parameter_some,
              ← htPlus, ← htMinus] at hsep
            exact hsep.trans htPlusNorm
          exact
            (minusFirstOrderTranslations_ne
              tPlus tMinus tailPlus tailMinus
              ‖parameter plusA plusB
                (mapE0PointPlusLocal
                  (C.toE0 + gaussianE0P))‖
              htPlusRed htMinusRed htPlusNorm htMinusNorm htSubNorm
              H.norm_pos) hfirstOrderEq

/-- Syntactic wrapper matching subtraction of the negative visible point. -/
theorem no_pairedKernelSeparated_sub_negP
    (C : GaussianCoverZeroPoint) :
    ¬ PairedKernelSeparated
        (mapE0PointPlusLocal (C.toE0 - (-gaussianE0P)))
        (mapE0PointMinusLocal (C.toE0 - (-gaussianE0P))) := by
  simpa only [sub_neg_eq_add] using no_pairedKernelSeparated_add_P C

end

end GaussianCoverZeroTranslationActual
end Cuboid2
