import Cuboid2.QuadraticReduction.GaussianIndexIndependentReduction
import Cuboid2.QuadraticReduction.GaussianIndexCoprime
import Cuboid2.QuadraticReduction.GaussianLocalMapInjective
import Cuboid2.QuadraticReduction.GaussianPairedFormalNorm

/-!
# Index-cleared paired formal points on the untwisted cover

The visible point need not be primitive.  This file combines the reindexed
finite rows with the exact characteristic-zero identity
`m • Q = k • P`.  If the corresponding rational numerator is nonzero, the
two local points centered at `P` (or `-P`) inherit the proved paired formal
separation of `12P` after clearing the unknown signed index `m`.
-/

namespace Cuboid2
namespace GaussianCoverZeroIndexPair

noncomputable section

open GaussianFormalKernelDisk
open GaussianIndexIndependent
open GaussianIndexIndependentReduction
open GaussianLocalMapInjective
open GaussianP37
open GaussianPairedFormalNorm
open GaussianProjectiveReduction
open GaussianProjectiveReductionHom

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have hxnonneg : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : DecidableEq ℚ_[37] := Classical.decEq _

@[simp] private theorem mapE0PointPlusLocalHom_apply (Q : E0Point) :
    mapE0PointPlusLocalHom Q = mapE0PointPlusLocal Q :=
  rfl

@[simp] private theorem mapE0PointMinusLocalHom_apply (Q : E0Point) :
    mapE0PointMinusLocalHom Q = mapE0PointMinusLocal Q :=
  rfl

private theorem paired_of_signed_multiple
    {PPlus : PlusLocalPoint} {PMinus : MinusLocalPoint}
    (hPlus : PPlus ∈ infinityKernel plusA plusB)
    (hMinus : PMinus ∈ infinityKernel minusA minusB)
    (m a : ℤ)
    (hm37 : ¬(37 : ℤ) ∣ m)
    (ha : a ≠ 0)
    (hPlusMul : m • PPlus = a • actualBasePlus)
    (hMinusMul : m • PMinus = a • actualBaseMinus) :
    PairedKernelSeparated PPlus PMinus := by
  have Hm :
      PairedKernelSeparated (m • PPlus) (m • PMinus) := by
    rw [hPlusMul, hMinusMul]
    exact actualBase_pairSeparated.zsmul a ha
  have Habs :
      PairedKernelSeparated
        (m.natAbs • PPlus) (m.natAbs • PMinus) := by
    cases m with
    | ofNat n =>
        change PairedKernelSeparated (n • PPlus) (n • PMinus)
        simpa only [Int.ofNat_eq_natCast, natCast_zsmul] using Hm
    | negSucc n =>
        change
          PairedKernelSeparated ((n + 1) • PPlus) ((n + 1) • PMinus)
        simpa only [negSucc_zsmul, neg_neg] using Hm.neg
  exact
    pairedKernelSeparated_of_natAbs_nsmul_of_not_dvd
      hPlus hMinus m hm37 Habs

/-- A surviving `+P` row with nonzero index-cleared numerator produces an
actual paired-separated point in the two infinity kernels. -/
theorem pairSeparated_sub_visible_of_row_one
    (e : E0Point ≃+ ℤ × ZMod 2)
    {Q : E0Point} {m k : ℤ} {δ ε : ℕ}
    (hP :
      visiblePoint = m • freeGenerator e + δ • twoTorsionPoint)
    (hQ :
      Q = k • freeGenerator e + ε • twoTorsionPoint)
    (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : ¬(37 : ℤ) ∣ m)
    (hrow : rowResidue k (inverseMod84 m) = 1)
    (hplain :
      rowTwist k (inverseMod84 m) δ ε = .plain)
    (ha : (k - m) / 12 ≠ 0) :
    PairedKernelSeparated
      (mapE0PointPlusLocal (Q - visiblePoint))
      (mapE0PointMinusLocal (Q - visiblePoint)) := by
  have hrows :=
    actual_reductions_eq_reindexed_rows e hP hQ hm84
  have hredPlus :
      reduceE0Plus Q = reduceE0Plus visiblePoint := by
    rw [hrows.1, hplain, hrow,
      GaussianVisibleReduction.reduceE0Plus_gaussianE0P]
    native_decide
  have hredMinus :
      reduceE0Minus Q = reduceE0Minus visiblePoint := by
    rw [hrows.2, hplain, hrow,
      GaussianVisibleReduction.reduceE0Minus_gaussianE0P]
    native_decide
  have hPlus :
      mapE0PointPlusLocal (Q - visiblePoint) ∈
        infinityKernel plusA plusB := by
    rw [show
      mapE0PointPlusLocal (Q - visiblePoint) =
        mapE0PointPlusLocal Q - mapE0PointPlusLocal visiblePoint from
      mapE0PointPlusLocalHom.map_sub Q visiblePoint]
    exact
      finiteReducePoint_sub_eq_none_of_eq
        plusA plusB _ _ hredPlus
  have hMinus :
      mapE0PointMinusLocal (Q - visiblePoint) ∈
        infinityKernel minusA minusB := by
    rw [show
      mapE0PointMinusLocal (Q - visiblePoint) =
        mapE0PointMinusLocal Q - mapE0PointMinusLocal visiblePoint from
      mapE0PointMinusLocalHom.map_sub Q visiblePoint]
    exact
      finiteReducePoint_sub_eq_none_of_eq
        minusA minusB _ _ hredMinus
  have hindex :=
    (indexIndependent_row_one e hP hQ hm84 hrow hplain).2
  have haTwelve : ((k - m) / 12) * 12 = k - m := by
    simpa using
      parameterAtP_numerator_mul_twelve
        hm84 (GaussianIndexCoprime.isCoprime_37_of_not_dvd hm37)
          (coefficient_modEq_of_inverseMod84_row_one hm84 hrow)
  have hglobal :
      m • (Q - visiblePoint) =
        ((k - m) / 12) • (12 • visiblePoint) := by
    calc
      m • (Q - visiblePoint) =
          m • Q - m • visiblePoint := zsmul_sub _ _ _
      _ = k • visiblePoint - m • visiblePoint := by rw [hindex]
      _ = (k - m) • visiblePoint := (sub_zsmul _ _ _).symm
      _ = (((k - m) / 12) * 12) • visiblePoint := by rw [haTwelve]
      _ = ((k - m) / 12) • (12 • visiblePoint) := by
        simp only [mul_zsmul]
        rfl
  have hPlusMul :
      m • mapE0PointPlusLocal (Q - visiblePoint) =
        ((k - m) / 12) • actualBasePlus := by
    simpa only [map_zsmul, map_nsmul, actualBasePlus,
      mapE0PointPlusLocalHom_apply, visiblePoint] using
      congrArg mapE0PointPlusLocalHom hglobal
  have hMinusMul :
      m • mapE0PointMinusLocal (Q - visiblePoint) =
        ((k - m) / 12) • actualBaseMinus := by
    simpa only [map_zsmul, map_nsmul, actualBaseMinus,
      mapE0PointMinusLocalHom_apply, visiblePoint] using
      congrArg mapE0PointMinusLocalHom hglobal
  exact
    paired_of_signed_multiple hPlus hMinus m ((k - m) / 12)
      hm37 ha hPlusMul hMinusMul

/-- A surviving `-P` row with nonzero index-cleared numerator produces the
corresponding paired-separated point centered at `-P`. -/
theorem pairSeparated_sub_neg_visible_of_row_eleven
    (e : E0Point ≃+ ℤ × ZMod 2)
    {Q : E0Point} {m k : ℤ} {δ ε : ℕ}
    (hP :
      visiblePoint = m • freeGenerator e + δ • twoTorsionPoint)
    (hQ :
      Q = k • freeGenerator e + ε • twoTorsionPoint)
    (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : ¬(37 : ℤ) ∣ m)
    (hrow : rowResidue k (inverseMod84 m) = 11)
    (hplain :
      rowTwist k (inverseMod84 m) δ ε = .plain)
    (ha : (k + m) / 12 ≠ 0) :
    PairedKernelSeparated
      (mapE0PointPlusLocal (Q - -visiblePoint))
      (mapE0PointMinusLocal (Q - -visiblePoint)) := by
  have hrows :=
    actual_reductions_eq_reindexed_rows e hP hQ hm84
  have hredPlus :
      reduceE0Plus Q = reduceE0Plus (-visiblePoint) := by
    rw [hrows.1, hplain, hrow, reduceE0Plus_neg,
      GaussianVisibleReduction.reduceE0Plus_gaussianE0P]
    native_decide
  have hredMinus :
      reduceE0Minus Q = reduceE0Minus (-visiblePoint) := by
    rw [hrows.2, hplain, hrow, reduceE0Minus_neg,
      GaussianVisibleReduction.reduceE0Minus_gaussianE0P]
    native_decide
  have hPlus :
      mapE0PointPlusLocal (Q - -visiblePoint) ∈
        infinityKernel plusA plusB := by
    rw [show
      mapE0PointPlusLocal (Q - -visiblePoint) =
        mapE0PointPlusLocal Q - mapE0PointPlusLocal (-visiblePoint) from
      mapE0PointPlusLocalHom.map_sub Q (-visiblePoint)]
    exact
      finiteReducePoint_sub_eq_none_of_eq
        plusA plusB _ _ hredPlus
  have hMinus :
      mapE0PointMinusLocal (Q - -visiblePoint) ∈
        infinityKernel minusA minusB := by
    rw [show
      mapE0PointMinusLocal (Q - -visiblePoint) =
        mapE0PointMinusLocal Q - mapE0PointMinusLocal (-visiblePoint) from
      mapE0PointMinusLocalHom.map_sub Q (-visiblePoint)]
    exact
      finiteReducePoint_sub_eq_none_of_eq
        minusA minusB _ _ hredMinus
  have hindex :=
    (indexIndependent_row_eleven e hP hQ hm84 hrow hplain).2
  have haTwelve : ((k + m) / 12) * 12 = k + m := by
    simpa using
      parameterAtNegP_numerator_mul_twelve
        hm84 (GaussianIndexCoprime.isCoprime_37_of_not_dvd hm37)
          (coefficient_modEq_of_inverseMod84_row_eleven hm84 hrow)
  have hglobal :
      m • (Q - -visiblePoint) =
        ((k + m) / 12) • (12 • visiblePoint) := by
    calc
      m • (Q - -visiblePoint) =
          m • Q - m • (-visiblePoint) := zsmul_sub _ _ _
      _ = k • visiblePoint - m • (-visiblePoint) := by rw [hindex]
      _ = (k + m) • visiblePoint := by
        rw [zsmul_neg]
        exact (sub_neg_eq_add _ _).trans (add_zsmul _ _ _).symm
      _ = (((k + m) / 12) * 12) • visiblePoint := by rw [haTwelve]
      _ = ((k + m) / 12) • (12 • visiblePoint) := by
        simp only [mul_zsmul]
        rfl
  have hPlusMul :
      m • mapE0PointPlusLocal (Q - -visiblePoint) =
        ((k + m) / 12) • actualBasePlus := by
    simpa only [map_zsmul, map_nsmul, actualBasePlus,
      mapE0PointPlusLocalHom_apply, visiblePoint] using
      congrArg mapE0PointPlusLocalHom hglobal
  have hMinusMul :
      m • mapE0PointMinusLocal (Q - -visiblePoint) =
        ((k + m) / 12) • actualBaseMinus := by
    simpa only [map_zsmul, map_nsmul, actualBaseMinus,
      mapE0PointMinusLocalHom_apply, visiblePoint] using
      congrArg mapE0PointMinusLocalHom hglobal
  exact
    paired_of_signed_multiple hPlus hMinus m ((k + m) / 12)
      hm37 ha hPlusMul hMinusMul

end

end GaussianCoverZeroIndexPair
end Cuboid2
