import Cuboid2.QuadraticReduction.GaussianFormalKernelTorsion
import Cuboid2.QuadraticReduction.GaussianP37ActualTrace
import Cuboid2.QuadraticReduction.GaussianFiniteExponent
import Cuboid2.QuadraticReduction.GaussianSplit37ReductionActual

/-!
# Norm separation for the two split formal kernels

This module replaces an abstract all-level comparison by a concrete
nonarchimedean invariant.  Two points in the plus and minus infinity kernels
are paired-separated when their formal parameters have the same positive
norm and their difference has exactly that norm.
-/

namespace Cuboid2
namespace GaussianPairedFormalNorm

noncomputable section

open GaussianFinite
open GaussianFiniteExponent
open GaussianP37
open GaussianP37ActualTrace
open GaussianProjectiveReduction
open GaussianProjectiveReductionHom
open GaussianFormalKernelDisk
open GaussianFormalKernelTorsion
open GaussianSplit37ReductionActual

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : DecidableEq ℚ_[37] := Classical.decEq _

abbrev PlusLocalPoint :=
  (localPadicCurve plusA plusB).toAffine.Point

abbrev MinusLocalPoint :=
  (localPadicCurve minusA minusB).toAffine.Point

/-- The paired norm invariant on the two actual split formal kernels. -/
structure PairedKernelSeparated
    (PPlus : PlusLocalPoint) (PMinus : MinusLocalPoint) : Prop where
  plus_mem : PPlus ∈ infinityKernel plusA plusB
  minus_mem : PMinus ∈ infinityKernel minusA minusB
  norm_eq :
    ‖parameter plusA plusB PPlus‖ =
      ‖parameter minusA minusB PMinus‖
  norm_pos : 0 < ‖parameter plusA plusB PPlus‖
  norm_sub_eq :
    ‖parameter plusA plusB PPlus -
        parameter minusA minusB PMinus‖ =
      ‖parameter plusA plusB PPlus‖

private theorem norm_sub_le_of_le
    {x y : ℚ_[37]} {r : ℝ}
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖x - y‖ ≤ r := by
  have h :=
    IsUltrametricDist.norm_add_le_max x (-y)
  rw [norm_neg] at h
  simpa only [sub_eq_add_neg] using h.trans (max_le hx hy)

/-- Multiplication by a natural number prime to `37` preserves paired norm
separation. -/
theorem PairedKernelSeparated.nsmul_of_not_dvd
    {PPlus : PlusLocalPoint} {PMinus : MinusLocalPoint}
    (H : PairedKernelSeparated PPlus PMinus)
    (n : ℕ) (hn : ¬37 ∣ n) :
    PairedKernelSeparated (n • PPlus) (n • PMinus) := by
  let tPlus := parameter plusA plusB PPlus
  let tMinus := parameter minusA minusB PMinus
  let sPlus := parameter plusA plusB (n • PPlus)
  let sMinus := parameter minusA minusB (n • PMinus)
  have htLt : ‖tPlus‖ < 1 := by
    simpa [tPlus] using
      norm_parameter_lt_one_of_mem_kernel_point
        plusA plusB PPlus H.plus_mem
  have htCubeLt : ‖tPlus‖ ^ 3 < ‖tPlus‖ := by
    nlinarith [H.norm_pos, mul_self_nonneg ‖tPlus‖]
  have hplusApprox :
      ‖sPlus - (n : ℚ_[37]) * tPlus‖ ≤ ‖tPlus‖ ^ 3 := by
    simpa [sPlus, tPlus] using
      norm_parameter_nsmul_sub_le_cube
        plusA plusB PPlus H.plus_mem n
  have hminusApprox :
      ‖sMinus - (n : ℚ_[37]) * tMinus‖ ≤ ‖tPlus‖ ^ 3 := by
    have h :=
      norm_parameter_nsmul_sub_le_cube
        minusA minusB PMinus H.minus_mem n
    calc
      ‖sMinus - (n : ℚ_[37]) * tMinus‖ ≤ ‖tMinus‖ ^ 3 := by
        simpa [sMinus, tMinus] using h
      _ = ‖tPlus‖ ^ 3 := by
        rw [show ‖tMinus‖ = ‖tPlus‖ by
          simpa [tPlus, tMinus] using H.norm_eq.symm]
  have herror :
      ‖(sPlus - (n : ℚ_[37]) * tPlus) -
          (sMinus - (n : ℚ_[37]) * tMinus)‖ <
        ‖tPlus‖ :=
    (norm_sub_le_of_le hplusApprox hminusApprox).trans_lt htCubeLt
  have hnNorm : ‖(n : ℚ_[37])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr
      ((show Nat.Prime 37 by norm_num).coprime_iff_not_dvd.mpr hn)
  have hlinearNorm :
      ‖(n : ℚ_[37]) * (tPlus - tMinus)‖ = ‖tPlus‖ := by
    rw [norm_mul, hnNorm, one_mul]
    simpa [tPlus, tMinus] using H.norm_sub_eq
  have hdiffError :
      (sPlus - sMinus) -
          (n : ℚ_[37]) * (tPlus - tMinus) =
        (sPlus - (n : ℚ_[37]) * tPlus) -
          (sMinus - (n : ℚ_[37]) * tMinus) := by
    ring
  have hdiff :
      ‖sPlus - sMinus‖ = ‖tPlus‖ := by
    have hsmall :
        ‖(sPlus - sMinus) -
            (n : ℚ_[37]) * (tPlus - tMinus)‖ <
          ‖(n : ℚ_[37]) * (tPlus - tMinus)‖ := by
      rw [hdiffError, hlinearNorm]
      exact herror
    exact
      (Padic.norm_eq_of_norm_sub_lt_right hsmall).trans hlinearNorm
  refine
    { plus_mem := (infinityKernel plusA plusB).nsmul_mem H.plus_mem n
      minus_mem := (infinityKernel minusA minusB).nsmul_mem H.minus_mem n
      norm_eq := ?_
      norm_pos := ?_
      norm_sub_eq := ?_ }
  · calc
      ‖parameter plusA plusB (n • PPlus)‖ =
          ‖parameter plusA plusB PPlus‖ :=
        norm_parameter_nsmul_eq_of_not_dvd
          plusA plusB PPlus H.plus_mem n hn
      _ = ‖parameter minusA minusB PMinus‖ := H.norm_eq
      _ = ‖parameter minusA minusB (n • PMinus)‖ :=
        (norm_parameter_nsmul_eq_of_not_dvd
          minusA minusB PMinus H.minus_mem n hn).symm
  · rw [norm_parameter_nsmul_eq_of_not_dvd
      plusA plusB PPlus H.plus_mem n hn]
    exact H.norm_pos
  · calc
      ‖parameter plusA plusB (n • PPlus) -
          parameter minusA minusB (n • PMinus)‖ =
          ‖parameter plusA plusB PPlus‖ := by
        simpa [sPlus, sMinus, tPlus] using hdiff
      _ = ‖parameter plusA plusB (n • PPlus)‖ :=
        (norm_parameter_nsmul_eq_of_not_dvd
          plusA plusB PPlus H.plus_mem n hn).symm

/-- Multiplication by `37` preserves paired norm separation while scaling
the common norm by `37⁻¹`. -/
theorem PairedKernelSeparated.thirtySeven_nsmul
    {PPlus : PlusLocalPoint} {PMinus : MinusLocalPoint}
    (H : PairedKernelSeparated PPlus PMinus) :
    PairedKernelSeparated (37 • PPlus) (37 • PMinus) := by
  let tPlus := parameter plusA plusB PPlus
  let tMinus := parameter minusA minusB PMinus
  let sPlus := parameter plusA plusB (37 • PPlus)
  let sMinus := parameter minusA minusB (37 • PMinus)
  have htLt : ‖tPlus‖ < 1 := by
    simpa [tPlus] using
      norm_parameter_lt_one_of_mem_kernel_point
        plusA plusB PPlus H.plus_mem
  have htLe : ‖tPlus‖ ≤ (37 : ℝ)⁻¹ :=
    norm_le_inv_37_of_lt_one tPlus htLt
  have htSqLt : ‖tPlus‖ ^ 2 < (37 : ℝ)⁻¹ := by
    calc
      ‖tPlus‖ ^ 2 ≤ ((37 : ℝ)⁻¹) ^ 2 := by
        gcongr
      _ < (37 : ℝ)⁻¹ := by norm_num
  have htCubeLt :
      ‖tPlus‖ ^ 3 < (37 : ℝ)⁻¹ * ‖tPlus‖ := by
    calc
      ‖tPlus‖ ^ 3 = ‖tPlus‖ ^ 2 * ‖tPlus‖ := by ring
      _ < (37 : ℝ)⁻¹ * ‖tPlus‖ :=
        mul_lt_mul_of_pos_right htSqLt H.norm_pos
  have hplusApprox :
      ‖sPlus - (37 : ℚ_[37]) * tPlus‖ ≤ ‖tPlus‖ ^ 3 := by
    simpa [sPlus, tPlus] using
      norm_parameter_nsmul_sub_le_cube
        plusA plusB PPlus H.plus_mem 37
  have hminusApprox :
      ‖sMinus - (37 : ℚ_[37]) * tMinus‖ ≤ ‖tPlus‖ ^ 3 := by
    have h :=
      norm_parameter_nsmul_sub_le_cube
        minusA minusB PMinus H.minus_mem 37
    calc
      ‖sMinus - (37 : ℚ_[37]) * tMinus‖ ≤ ‖tMinus‖ ^ 3 := by
        simpa [sMinus, tMinus] using h
      _ = ‖tPlus‖ ^ 3 := by
        rw [show ‖tMinus‖ = ‖tPlus‖ by
          simpa [tPlus, tMinus] using H.norm_eq.symm]
  have herror :
      ‖(sPlus - (37 : ℚ_[37]) * tPlus) -
          (sMinus - (37 : ℚ_[37]) * tMinus)‖ <
        (37 : ℝ)⁻¹ * ‖tPlus‖ :=
    (norm_sub_le_of_le hplusApprox hminusApprox).trans_lt htCubeLt
  have h37Norm : ‖(37 : ℚ_[37])‖ = (37 : ℝ)⁻¹ := by
    simpa using (Padic.norm_p (p := 37))
  have hlinearNorm :
      ‖(37 : ℚ_[37]) * (tPlus - tMinus)‖ =
        (37 : ℝ)⁻¹ * ‖tPlus‖ := by
    rw [norm_mul, h37Norm]
    simpa [tPlus, tMinus] using congrArg ((37 : ℝ)⁻¹ * ·) H.norm_sub_eq
  have hdiffError :
      (sPlus - sMinus) -
          (37 : ℚ_[37]) * (tPlus - tMinus) =
        (sPlus - (37 : ℚ_[37]) * tPlus) -
          (sMinus - (37 : ℚ_[37]) * tMinus) := by
    ring
  have hdiff :
      ‖sPlus - sMinus‖ =
        (37 : ℝ)⁻¹ * ‖tPlus‖ := by
    have hsmall :
        ‖(sPlus - sMinus) -
            (37 : ℚ_[37]) * (tPlus - tMinus)‖ <
          ‖(37 : ℚ_[37]) * (tPlus - tMinus)‖ := by
      rw [hdiffError, hlinearNorm]
      exact herror
    exact
      (Padic.norm_eq_of_norm_sub_lt_right hsmall).trans hlinearNorm
  refine
    { plus_mem :=
        (infinityKernel plusA plusB).nsmul_mem H.plus_mem 37
      minus_mem :=
        (infinityKernel minusA minusB).nsmul_mem H.minus_mem 37
      norm_eq := ?_
      norm_pos := ?_
      norm_sub_eq := ?_ }
  · calc
      ‖parameter plusA plusB (37 • PPlus)‖ =
          (37 : ℝ)⁻¹ * ‖parameter plusA plusB PPlus‖ :=
        norm_parameter_37_nsmul_eq
          plusA plusB PPlus H.plus_mem
      _ =
          (37 : ℝ)⁻¹ * ‖parameter minusA minusB PMinus‖ := by
        rw [H.norm_eq]
      _ = ‖parameter minusA minusB (37 • PMinus)‖ :=
        (norm_parameter_37_nsmul_eq
          minusA minusB PMinus H.minus_mem).symm
  · rw [norm_parameter_37_nsmul_eq
      plusA plusB PPlus H.plus_mem]
    exact mul_pos (by positivity) H.norm_pos
  · calc
      ‖parameter plusA plusB (37 • PPlus) -
          parameter minusA minusB (37 • PMinus)‖ =
          (37 : ℝ)⁻¹ * ‖parameter plusA plusB PPlus‖ := by
        simpa [sPlus, sMinus, tPlus] using hdiff
      _ = ‖parameter plusA plusB (37 • PPlus)‖ :=
        (norm_parameter_37_nsmul_eq
          plusA plusB PPlus H.plus_mem).symm

/-- Every nonzero natural multiple preserves paired norm separation.  The
proof removes factors of `37` by strong induction and uses the prime-to-37
and 37-step lemmas above. -/
theorem PairedKernelSeparated.nsmul
    {PPlus : PlusLocalPoint} {PMinus : MinusLocalPoint}
    (H : PairedKernelSeparated PPlus PMinus)
    (n : ℕ) (hn : n ≠ 0) :
    PairedKernelSeparated (n • PPlus) (n • PMinus) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hdiv : 37 ∣ n
      · obtain ⟨k, rfl⟩ := hdiv
        have hk : k ≠ 0 := by
          intro hk
          subst k
          simp at hn
        have hklt : k < 37 * k := by omega
        have Hk := ih k hklt hk
        have H37 := Hk.thirtySeven_nsmul
        simpa only [smul_smul, Nat.mul_comm] using H37
      · exact H.nsmul_of_not_dvd n hdiv

/-- Simultaneous negation preserves paired norm separation. -/
theorem PairedKernelSeparated.neg
    {PPlus : PlusLocalPoint} {PMinus : MinusLocalPoint}
    (H : PairedKernelSeparated PPlus PMinus) :
    PairedKernelSeparated (-PPlus) (-PMinus) := by
  refine
    { plus_mem := (infinityKernel plusA plusB).neg_mem H.plus_mem
      minus_mem := (infinityKernel minusA minusB).neg_mem H.minus_mem
      norm_eq := ?_
      norm_pos := ?_
      norm_sub_eq := ?_ }
  · simp only [parameter_neg, norm_neg]
    exact H.norm_eq
  · simpa only [parameter_neg, norm_neg] using H.norm_pos
  · rw [parameter_neg, parameter_neg]
    have hneg :
        -parameter plusA plusB PPlus -
            -parameter minusA minusB PMinus =
          -(parameter plusA plusB PPlus -
            parameter minusA minusB PMinus) := by
      ring
    rw [hneg, norm_neg, H.norm_sub_eq, norm_neg]

/-- Signed nonzero multiples preserve paired norm separation. -/
theorem PairedKernelSeparated.zsmul
    {PPlus : PlusLocalPoint} {PMinus : MinusLocalPoint}
    (H : PairedKernelSeparated PPlus PMinus)
    (z : ℤ) (hz : z ≠ 0) :
    PairedKernelSeparated (z • PPlus) (z • PMinus) := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · have hn : n ≠ 0 := by
      exact_mod_cast hz
    simpa only [natCast_zsmul] using H.nsmul n hn
  · have hn : n ≠ 0 := by
      intro hn
      subst n
      simp at hz
    simpa only [neg_zsmul, natCast_zsmul] using (H.nsmul n hn).neg

/-! ## Prime-to-37 reflection -/

/-- Paired separation reflects through multiplication by a natural number
prime to `37`.  Membership of the two original points in their formal
kernels is stated explicitly; no divisibility or formal-group interface is
assumed. -/
theorem pairedKernelSeparated_of_nsmul_of_not_dvd
    {PPlus : PlusLocalPoint} {PMinus : MinusLocalPoint}
    (hPlus : PPlus ∈ infinityKernel plusA plusB)
    (hMinus : PMinus ∈ infinityKernel minusA minusB)
    (n : ℕ) (hn : ¬37 ∣ n)
    (Hn : PairedKernelSeparated (n • PPlus) (n • PMinus)) :
    PairedKernelSeparated PPlus PMinus := by
  let tPlus := parameter plusA plusB PPlus
  let tMinus := parameter minusA minusB PMinus
  let sPlus := parameter plusA plusB (n • PPlus)
  let sMinus := parameter minusA minusB (n • PMinus)
  have hplusNorm :
      ‖sPlus‖ = ‖tPlus‖ := by
    simpa [sPlus, tPlus] using
      norm_parameter_nsmul_eq_of_not_dvd
        plusA plusB PPlus hPlus n hn
  have hminusNorm :
      ‖sMinus‖ = ‖tMinus‖ := by
    simpa [sMinus, tMinus] using
      norm_parameter_nsmul_eq_of_not_dvd
        minusA minusB PMinus hMinus n hn
  have hnormEq : ‖tPlus‖ = ‖tMinus‖ := by
    calc
      ‖tPlus‖ = ‖sPlus‖ := hplusNorm.symm
      _ = ‖sMinus‖ := by
        simpa [sPlus, sMinus] using Hn.norm_eq
      _ = ‖tMinus‖ := hminusNorm
  have hnormPos : 0 < ‖tPlus‖ := by
    rw [← hplusNorm]
    simpa [sPlus] using Hn.norm_pos
  have htLt : ‖tPlus‖ < 1 := by
    simpa [tPlus] using
      norm_parameter_lt_one_of_mem_kernel_point
        plusA plusB PPlus hPlus
  have htCubeLt : ‖tPlus‖ ^ 3 < ‖tPlus‖ := by
    nlinarith [hnormPos, mul_self_nonneg ‖tPlus‖]
  have hplusApprox :
      ‖sPlus - (n : ℚ_[37]) * tPlus‖ ≤ ‖tPlus‖ ^ 3 := by
    simpa [sPlus, tPlus] using
      norm_parameter_nsmul_sub_le_cube
        plusA plusB PPlus hPlus n
  have hminusApprox :
      ‖sMinus - (n : ℚ_[37]) * tMinus‖ ≤ ‖tPlus‖ ^ 3 := by
    have h :=
      norm_parameter_nsmul_sub_le_cube
        minusA minusB PMinus hMinus n
    calc
      ‖sMinus - (n : ℚ_[37]) * tMinus‖ ≤ ‖tMinus‖ ^ 3 := by
        simpa [sMinus, tMinus] using h
      _ = ‖tPlus‖ ^ 3 := by rw [← hnormEq]
  have herror :
      ‖(sPlus - (n : ℚ_[37]) * tPlus) -
          (sMinus - (n : ℚ_[37]) * tMinus)‖ <
        ‖tPlus‖ :=
    (norm_sub_le_of_le hplusApprox hminusApprox).trans_lt htCubeLt
  have hnNorm : ‖(n : ℚ_[37])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr
      ((show Nat.Prime 37 by norm_num).coprime_iff_not_dvd.mpr hn)
  have hlinearNorm :
      ‖(n : ℚ_[37]) * (tPlus - tMinus)‖ =
        ‖tPlus - tMinus‖ := by
    rw [norm_mul, hnNorm, one_mul]
  have hdiffError :
      (sPlus - sMinus) -
          (n : ℚ_[37]) * (tPlus - tMinus) =
        (sPlus - (n : ℚ_[37]) * tPlus) -
          (sMinus - (n : ℚ_[37]) * tMinus) := by
    ring
  have hsdiffNorm : ‖sPlus - sMinus‖ = ‖tPlus‖ := by
    calc
      ‖sPlus - sMinus‖ = ‖sPlus‖ := by
        simpa [sPlus, sMinus] using Hn.norm_sub_eq
      _ = ‖tPlus‖ := hplusNorm
  have hsmall :
      ‖(sPlus - sMinus) -
          (n : ℚ_[37]) * (tPlus - tMinus)‖ <
        ‖sPlus - sMinus‖ := by
    rw [hdiffError, hsdiffNorm]
    exact herror
  have hbaseDiff : ‖tPlus - tMinus‖ = ‖tPlus‖ := by
    calc
      ‖tPlus - tMinus‖ =
          ‖(n : ℚ_[37]) * (tPlus - tMinus)‖ :=
        hlinearNorm.symm
      _ = ‖sPlus - sMinus‖ :=
        (Padic.norm_eq_of_norm_sub_lt_left hsmall).symm
      _ = ‖tPlus‖ := hsdiffNorm
  exact
    { plus_mem := hPlus
      minus_mem := hMinus
      norm_eq := by simpa [tPlus, tMinus] using hnormEq
      norm_pos := by simpa [tPlus] using hnormPos
      norm_sub_eq := by
        simpa [tPlus, tMinus] using hbaseDiff }

/-! ## The actual pair `12P₊, 12P₋` -/

/-- The plus formal-kernel point supplied by the actual twelve-multiple
trace. -/
def actualBasePlus : PlusLocalPoint :=
  12 • mapE0PointPlusLocal gaussianE0P

/-- The minus formal-kernel point supplied by the actual twelve-multiple
trace. -/
def actualBaseMinus : MinusLocalPoint :=
  12 • mapE0PointMinusLocal gaussianE0P

theorem actualBasePlus_mem :
    actualBasePlus ∈ infinityKernel plusA plusB := by
  change
    finiteReducePoint plusA plusB
        (12 • mapE0PointPlusLocal gaussianE0P) =
      none
  rw [map_nsmul_finite
    37 (PadicInt.toZMod plusA).val (PadicInt.toZMod plusB).val
    (finiteReducePoint plusA plusB)
    (finiteReducePoint_zero plusA plusB)
    (finiteReducePoint_add plusA plusB)]
  rw [plusA_residue_val, plusB_residue_val]
  apply plus_twelve_eq_none_of_mem
  have hmem :=
    finiteReducePoint_mem_finitePoints
      plusA plusB (mapE0PointPlusLocal gaussianE0P)
  simpa only [plusA_residue_val, plusB_residue_val] using hmem

theorem actualBaseMinus_mem :
    actualBaseMinus ∈ infinityKernel minusA minusB := by
  change
    finiteReducePoint minusA minusB
        (12 • mapE0PointMinusLocal gaussianE0P) =
      none
  rw [map_nsmul_finite
    37 (PadicInt.toZMod minusA).val (PadicInt.toZMod minusB).val
    (finiteReducePoint minusA minusB)
    (finiteReducePoint_zero minusA minusB)
    (finiteReducePoint_add minusA minusB)]
  rw [minusA_residue_val, minusB_residue_val]
  rw [show
    finiteReducePoint minusA minusB
        (mapE0PointMinusLocal gaussianE0P) =
      some (2, 2) from
    GaussianVisibleReduction.reduceE0Minus_gaussianE0P]
  native_decide

private theorem padicInt_norm_eq_one_of_toZMod_ne_zero
    (z : ℤ_[37]) (hz : PadicInt.toZMod z ≠ 0) :
    ‖z‖ = 1 := by
  apply le_antisymm z.property
  apply le_of_not_gt
  intro hlt
  apply hz
  have hdvd : (37 : ℤ_[37]) ∣ z :=
    (PadicInt.norm_lt_one_iff_dvd z).mp hlt
  have hspan :
      z ∈
        (Ideal.span {(↑(37 : ℕ) : ℤ_[37])} :
          Ideal ℤ_[37]) :=
    Ideal.mem_span_singleton.mpr hdvd
  have hker :
      z ∈ RingHom.ker
        (PadicInt.toZMod : ℤ_[37] →+* ZMod 37) := by
    rw [PadicInt.ker_toZMod,
      PadicInt.maximalIdeal_eq_span_p]
    exact hspan
  exact RingHom.mem_ker.mp hker

/-- The actual trace pair `12P₊,12P₋` is paired-separated.  The residues
`17` and `19` show that each divided parameter, and their difference, is a
37-adic unit. -/
theorem actualBase_pairSeparated :
    PairedKernelSeparated actualBasePlus actualBaseMinus := by
  obtain
    ⟨h12Plus, tPlus, qPlus, hpointPlus, htPlus,
      _hcertificatePlus, hfactorPlus, hqPlusResidue⟩ :=
    plus_actual_formal_parameter_first_layer
  obtain
    ⟨h12Minus, tMinus, qMinus, hpointMinus, htMinus,
      _hcertificateMinus, hfactorMinus, hqMinusResidue⟩ :=
    minus_actual_formal_parameter_first_layer
  have hparameterPlus :
      parameter plusA plusB actualBasePlus =
        (tPlus : ℚ_[37]) := by
    unfold actualBasePlus
    rw [hpointPlus, parameter_some]
    exact htPlus.symm
  have hparameterMinus :
      parameter minusA minusB actualBaseMinus =
        (tMinus : ℚ_[37]) := by
    unfold actualBaseMinus
    rw [hpointMinus, parameter_some]
    exact htMinus.symm
  have hqPlusNe :
      PadicInt.toZMod qPlus ≠ (0 : ZMod 37) := by
    rw [hqPlusResidue]
    native_decide
  have hqMinusNe :
      PadicInt.toZMod qMinus ≠ (0 : ZMod 37) := by
    rw [hqMinusResidue]
    native_decide
  have hqPlusNorm : ‖qPlus‖ = 1 :=
    padicInt_norm_eq_one_of_toZMod_ne_zero qPlus hqPlusNe
  have hqMinusNorm : ‖qMinus‖ = 1 :=
    padicInt_norm_eq_one_of_toZMod_ne_zero qMinus hqMinusNe
  have hqPlusNorm' : ‖(qPlus : ℚ_[37])‖ = 1 :=
    hqPlusNorm
  have hqMinusNorm' : ‖(qMinus : ℚ_[37])‖ = 1 :=
    hqMinusNorm
  have h37Norm :
      ‖(37 : ℚ_[37])‖ = (37 : ℝ)⁻¹ := by
    simpa using (Padic.norm_p (p := 37))
  have hcoe37 :
      ((37 : ℤ_[37]) : ℚ_[37]) = (37 : ℚ_[37]) :=
    PadicInt.coe_natCast 37
  have hfactorPlus' :
      (tPlus : ℚ_[37]) =
        (37 : ℚ_[37]) * (qPlus : ℚ_[37]) := by
    simpa only [PadicInt.coe_mul, hcoe37] using
      congrArg (fun z : ℤ_[37] => (z : ℚ_[37])) hfactorPlus
  have hfactorMinus' :
      (tMinus : ℚ_[37]) =
        (37 : ℚ_[37]) * (qMinus : ℚ_[37]) := by
    simpa only [PadicInt.coe_mul, hcoe37] using
      congrArg (fun z : ℤ_[37] => (z : ℚ_[37])) hfactorMinus
  have htPlusNorm :
      ‖(tPlus : ℚ_[37])‖ = (37 : ℝ)⁻¹ := by
    rw [hfactorPlus', norm_mul, h37Norm, hqPlusNorm', mul_one]
  have htMinusNorm :
      ‖(tMinus : ℚ_[37])‖ = (37 : ℝ)⁻¹ := by
    rw [hfactorMinus', norm_mul, h37Norm, hqMinusNorm', mul_one]
  let qDiff : ℤ_[37] := qPlus - qMinus
  have hqDiffResidue :
      PadicInt.toZMod qDiff = (17 : ZMod 37) - 19 := by
    simp only [qDiff, map_sub, hqPlusResidue, hqMinusResidue]
  have hqDiffNe :
      PadicInt.toZMod qDiff ≠ (0 : ZMod 37) := by
    rw [hqDiffResidue]
    native_decide
  have hqDiffNorm : ‖qDiff‖ = 1 :=
    padicInt_norm_eq_one_of_toZMod_ne_zero qDiff hqDiffNe
  have hqDiffNorm' : ‖(qDiff : ℚ_[37])‖ = 1 :=
    hqDiffNorm
  have htDiffNorm :
      ‖(tPlus : ℚ_[37]) - (tMinus : ℚ_[37])‖ =
        (37 : ℝ)⁻¹ := by
    rw [hfactorPlus', hfactorMinus', ← mul_sub,
      norm_mul, h37Norm]
    change
      (37 : ℝ)⁻¹ * ‖(qDiff : ℚ_[37])‖ =
        (37 : ℝ)⁻¹
    rw [hqDiffNorm', mul_one]
  refine
    { plus_mem := actualBasePlus_mem
      minus_mem := actualBaseMinus_mem
      norm_eq := ?_
      norm_pos := ?_
      norm_sub_eq := ?_ }
  · rw [hparameterPlus, hparameterMinus,
      htPlusNorm, htMinusNorm]
  · rw [hparameterPlus, htPlusNorm]
    positivity
  · rw [hparameterPlus, hparameterMinus,
      htDiffNorm, htPlusNorm]

/-- Integer-coefficient wrapper for prime-to-`37` reflection through
`m.natAbs`, as used when the visible point has unknown signed free
coefficient `m`. -/
theorem pairedKernelSeparated_of_natAbs_nsmul_of_not_dvd
    {PPlus : PlusLocalPoint} {PMinus : MinusLocalPoint}
    (hPlus : PPlus ∈ infinityKernel plusA plusB)
    (hMinus : PMinus ∈ infinityKernel minusA minusB)
    (m : ℤ) (hm : ¬(37 : ℤ) ∣ m)
    (H :
      PairedKernelSeparated
        (m.natAbs • PPlus) (m.natAbs • PMinus)) :
    PairedKernelSeparated PPlus PMinus := by
  apply pairedKernelSeparated_of_nsmul_of_not_dvd
    hPlus hMinus m.natAbs
  · intro hdiv
    exact hm (Int.natCast_dvd.mpr hdiv)
  · exact H

end

end GaussianPairedFormalNorm
end Cuboid2
