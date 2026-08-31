import Cuboid2.QuadraticReduction.GaussianProjectiveReduction
import Cuboid2.QuadraticReduction.GaussianP37Bridge

/-!
# Actual split-37 valuation consequences for the untwisted cover

This module derives the two elementary residue-square conclusions attached to
the infinity and two-torsion disks directly from an actual `C₀` point and the
executable plus reduction.
-/

namespace Cuboid2
namespace GaussianCoverReductionActual

noncomputable section

open GaussianGoodReduction GaussianProjectiveReduction

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : DecidableEq ℚ_[37] := Classical.decEq _

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

private abbrev uPadic (C : GaussianCoverZeroPoint) : ℚ_[37] :=
  (C.u : ℚ_[37])

private abbrev vPadic (C : GaussianCoverZeroPoint) : ℚ_[37] :=
  gaussianToPadicPlus C.v

private theorem mapE0PointPlus_xRep_some
    {x y : GaussianRat} (h : gaussianE0.toAffine.Nonsingular x y) :
    (mapE0PointPlus
      (WeierstrassCurve.Affine.Point.some x y h)).xRep =
        ![gaussianToPadicPlus x, 1] := by
  rfl

private theorem map_cover_xRep (C : GaussianCoverZeroPoint) :
    (mapE0PointPlusLocal C.toE0).xRep =
      ![2 * uPadic C ^ 2, 1] := by
  rw [mapE0PointPlusLocal_xRep]
  simp only [GaussianCoverZeroPoint.toE0,
    WeierstrassCurve.Affine.Point.mk]
  rw [mapE0PointPlus_xRep_some]
  simp [uPadic, gaussianOfRat]

private theorem vPadic_sq (C : GaussianCoverZeroPoint) :
    vPadic C ^ 2 =
      2 * uPadic C ^ 4 - 1 +
        (splitRootPlus : ℚ_[37]) *
          (2 * uPadic C ^ 2 - 2) := by
  have h := congrArg gaussianToPadicPlus C.onCurve
  simpa [vPadic, uPadic, gaussianQuartic, gaussianOfRat] using h

private theorem toZMod_eq_zero_of_norm_lt_one
    (z : ℚ_[37]) (hz : ‖z‖ < 1) :
    PadicInt.toZMod (⟨z, hz.le⟩ : ℤ_[37]) = 0 := by
  let zInt : ℤ_[37] := ⟨z, hz.le⟩
  change PadicInt.toZMod zInt = 0
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
  apply (PadicInt.norm_lt_one_iff_dvd zInt).mp
  exact hz

private theorem residue_square_witness
    (z : ℤ_[37]) (c : ℕ) (hc : c < 37)
    (hz : PadicInt.toZMod z ^ 2 = (c : ZMod 37)) :
    ∃ a : Fin 37, a.val ^ 2 % 37 = c := by
  refine ⟨⟨(PadicInt.toZMod z).val,
    (PadicInt.toZMod z).val_lt⟩, ?_⟩
  have hval := congrArg ZMod.val hz
  simpa [pow_two, ZMod.val_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hc]
    using hval

private theorem norm_two_u_sq_not_le_one_of_reduce_none
    (C : GaussianCoverZeroPoint)
    (hred : reduceE0Plus C.toE0 = none) :
    ¬ ‖2 * uPadic C ^ 2‖ ≤ 1 := by
  cases hP : mapE0PointPlusLocal C.toE0 with
  | zero =>
      have hxrep := map_cover_xRep C
      rw [hP] at hxrep
      change ![1, 0] = ![2 * uPadic C ^ 2, 1] at hxrep
      have hbad := congrFun hxrep 1
      norm_num at hbad
  | some x y hpoint =>
      have hxrep := map_cover_xRep C
      rw [hP, WeierstrassCurve.Affine.Point.xRep_some] at hxrep
      have hx : x = 2 * uPadic C ^ 2 := by
        simpa using congrFun hxrep 0
      subst x
      intro hxInt
      have hred' := hred
      unfold reduceE0Plus finiteReducePoint at hred'
      rw [hP] at hred'
      simp only [reducePoint, hxInt, ↓reduceDIte] at hred'
      simp [finitePointOfResidue,
        WeierstrassCurve.Affine.Point.mk] at hred'

private theorem norm_u_gt_one_of_reduce_none
    (C : GaussianCoverZeroPoint)
    (hred : reduceE0Plus C.toE0 = none) :
    1 < ‖uPadic C‖ := by
  have hnot :=
    norm_two_u_sq_not_le_one_of_reduce_none C hred
  have hnormTwo : ‖(2 : ℚ_[37])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [norm_mul, norm_pow, hnormTwo, one_mul] at hnot
  by_contra h
  apply hnot
  have hu : ‖uPadic C‖ ≤ 1 := le_of_not_gt h
  nlinarith [norm_nonneg (uPadic C)]

private theorem norm_le_one_of_sq_eq_int
    (z : ℚ_[37]) (q : ℤ_[37]) (h : z ^ 2 = (q : ℚ_[37])) :
    ‖z‖ ≤ 1 := by
  have hzsq : ‖z‖ ^ 2 ≤ 1 := by
    rw [← norm_pow, h]
    exact q.property
  nlinarith [norm_nonneg z]

private theorem scaled_v_sq
    (C : GaussianCoverZeroPoint) (hu : uPadic C ≠ 0) :
    (vPadic C / uPadic C ^ 2) ^ 2 =
      2 - (uPadic C)⁻¹ ^ 4 +
        (splitRootPlus : ℚ_[37]) *
          (2 * (uPadic C)⁻¹ ^ 2 - 2 * (uPadic C)⁻¹ ^ 4) := by
  rw [div_pow, vPadic_sq]
  field_simp [hu]

/-- If the quotient point reduces to infinity at the plus split prime, the
scaled cover coordinate `v/u²` would reduce to a square root of `2`. -/
theorem infinity_forces_leading_square_actual
    (C : GaussianCoverZeroPoint)
    (hred : reduceE0Plus C.toE0 = none) :
    ∃ a : Fin 37, a.val ^ 2 % 37 = 2 := by
  have huNorm : 1 < ‖uPadic C‖ :=
    norm_u_gt_one_of_reduce_none C hred
  have hu : uPadic C ≠ 0 := by
    intro h
    rw [h, norm_zero] at huNorm
    norm_num at huNorm
  let t : ℚ_[37] := (uPadic C)⁻¹
  have htNorm : ‖t‖ < 1 := by
    dsimp only [t]
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ huNorm
  let tInt : ℤ_[37] := ⟨t, htNorm.le⟩
  let qInt : ℤ_[37] :=
    2 - tInt ^ 4 +
      splitRootPlus * (2 * tInt ^ 2 - 2 * tInt ^ 4)
  let w : ℚ_[37] := vPadic C / uPadic C ^ 2
  have hwSq : w ^ 2 = (qInt : ℚ_[37]) := by
    have h := scaled_v_sq C hu
    calc
      w ^ 2 =
          2 - t ^ 4 +
            (splitRootPlus : ℚ_[37]) *
              (2 * t ^ 2 - 2 * t ^ 4) := by
        simpa only [w, t] using h
      _ = (qInt : ℚ_[37]) := by
        rfl
  have hwNorm : ‖w‖ ≤ 1 :=
    norm_le_one_of_sq_eq_int w qInt hwSq
  let wInt : ℤ_[37] := ⟨w, hwNorm⟩
  have hInt : wInt ^ 2 = qInt := by
    apply Subtype.val_injective
    exact hwSq
  have htRes : PadicInt.toZMod tInt = 0 := by
    exact toZMod_eq_zero_of_norm_lt_one t htNorm
  have hres := congrArg PadicInt.toZMod hInt
  have hres' :
      PadicInt.toZMod wInt ^ 2 = (2 : ZMod 37) := by
    simpa [qInt, htRes, splitRootPlus_toZMod, map_ofNat] using hres
  exact residue_square_witness wInt 2 (by norm_num) hres'

private theorem integral_u_residue_zero_of_reduce_torsion
    (C : GaussianCoverZeroPoint)
    (hred : reduceE0Plus C.toE0 = some (0, 0)) :
    ∃ hu : ‖uPadic C‖ ≤ 1,
      PadicInt.toZMod (⟨uPadic C, hu⟩ : ℤ_[37]) = 0 := by
  cases hP : mapE0PointPlusLocal C.toE0 with
  | zero =>
      have hxrep := map_cover_xRep C
      rw [hP] at hxrep
      change ![1, 0] = ![2 * uPadic C ^ 2, 1] at hxrep
      have hbad := congrFun hxrep 1
      norm_num at hbad
  | some x y hpoint =>
      have hxrep := map_cover_xRep C
      rw [hP, WeierstrassCurve.Affine.Point.xRep_some] at hxrep
      have hx : x = 2 * uPadic C ^ 2 := by
        simpa using congrFun hxrep 0
      subst x
      by_cases hxInt : ‖2 * uPadic C ^ 2‖ ≤ 1
      · have hred' := hred
        unfold reduceE0Plus finiteReducePoint at hred'
        rw [hP] at hred'
        simp only [reducePoint, hxInt, ↓reduceDIte] at hred'
        simp only [finitePointOfResidue,
          WeierstrassCurve.Affine.Point.mk] at hred'
        have hcoords := Option.some.inj hred'
        have hxVal :
            (PadicInt.toZMod
              (⟨2 * uPadic C ^ 2, hxInt⟩ : ℤ_[37])).val = 0 := by
          exact congrArg Prod.fst hcoords
        have hnormTwo : ‖(2 : ℚ_[37])‖ = 1 :=
          Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
        have hu : ‖uPadic C‖ ≤ 1 := by
          rw [norm_mul, norm_pow, hnormTwo, one_mul] at hxInt
          nlinarith [norm_nonneg (uPadic C)]
        let uInt : ℤ_[37] := ⟨uPadic C, hu⟩
        have hxRes :
            PadicInt.toZMod
              (⟨2 * uPadic C ^ 2, hxInt⟩ : ℤ_[37]) = 0 :=
          (ZMod.val_eq_zero _).mp hxVal
        have hxIntEq :
            (⟨2 * uPadic C ^ 2, hxInt⟩ : ℤ_[37]) =
              2 * uInt ^ 2 := by
          apply Subtype.val_injective
          rfl
        have hxMap :
            PadicInt.toZMod
                (⟨2 * uPadic C ^ 2, hxInt⟩ : ℤ_[37]) =
              (2 : ZMod 37) * PadicInt.toZMod uInt ^ 2 := by
          calc
            _ = PadicInt.toZMod (2 * uInt ^ 2) :=
              congrArg PadicInt.toZMod hxIntEq
            _ =
                PadicInt.toZMod (2 : ℤ_[37]) *
                  PadicInt.toZMod (uInt ^ 2) :=
              map_mul PadicInt.toZMod _ _
            _ = (2 : ZMod 37) * PadicInt.toZMod uInt ^ 2 := by
              rw [map_pow]
              exact congrArg (fun z : ZMod 37 =>
                z * PadicInt.toZMod uInt ^ 2)
                (map_ofNat PadicInt.toZMod 2)
        rw [hxMap] at hxRes
        have huSq : PadicInt.toZMod uInt ^ 2 = 0 :=
          (mul_eq_zero.mp hxRes).resolve_left (by native_decide)
        have huRes : PadicInt.toZMod uInt = 0 :=
          sq_eq_zero_iff.mp huSq
        exact ⟨hu, huRes⟩
      · have hred' := hred
        unfold reduceE0Plus finiteReducePoint at hred'
        rw [hP] at hred'
        simp only [reducePoint, hxInt, ↓reduceDIte] at hred'
        simp [finitePointOfResidue] at hred'

/-- If the quotient point reduces to `(0,0)` at the plus split prime, the
integral cover coordinate `v` would reduce to a square root of
`q(0) = 24`. -/
theorem torsion_forces_q0_square_actual
    (C : GaussianCoverZeroPoint)
    (hred : reduceE0Plus C.toE0 = some (0, 0)) :
    ∃ a : Fin 37, a.val ^ 2 % 37 = 24 := by
  obtain ⟨hu, huRes⟩ :=
    integral_u_residue_zero_of_reduce_torsion C hred
  let uInt : ℤ_[37] := ⟨uPadic C, hu⟩
  let qInt : ℤ_[37] :=
    2 * uInt ^ 4 - 1 +
      splitRootPlus * (2 * uInt ^ 2 - 2)
  have hvSq : vPadic C ^ 2 = (qInt : ℚ_[37]) := by
    calc
      vPadic C ^ 2 =
          2 * uPadic C ^ 4 - 1 +
            (splitRootPlus : ℚ_[37]) *
              (2 * uPadic C ^ 2 - 2) :=
        vPadic_sq C
      _ = (qInt : ℚ_[37]) := by
        rfl
  have hvNorm : ‖vPadic C‖ ≤ 1 :=
    norm_le_one_of_sq_eq_int (vPadic C) qInt hvSq
  let vInt : ℤ_[37] := ⟨vPadic C, hvNorm⟩
  have hInt : vInt ^ 2 = qInt := by
    apply Subtype.val_injective
    exact hvSq
  have hres := congrArg PadicInt.toZMod hInt
  have huRes' : PadicInt.toZMod uInt = 0 := by
    exact huRes
  have huPowTwo : PadicInt.toZMod (uInt ^ 2) = 0 := by
    rw [map_pow, huRes']
    norm_num
  have huPowFour : PadicInt.toZMod (uInt ^ 4) = 0 := by
    rw [map_pow, huRes']
    norm_num
  have hres0 :
      PadicInt.toZMod vInt ^ 2 =
        (-1 + -(6 * 2) : ZMod 37) := by
    simpa [qInt, huPowTwo, huPowFour, splitRootPlus_toZMod,
      map_ofNat] using hres
  have hres' :
      PadicInt.toZMod vInt ^ 2 = (24 : ZMod 37) := by
    calc
      _ = (-1 + -(6 * 2) : ZMod 37) := hres0
      _ = 24 := by native_decide
  exact residue_square_witness vInt 24 (by norm_num) hres'

end

end GaussianCoverReductionActual
end Cuboid2
