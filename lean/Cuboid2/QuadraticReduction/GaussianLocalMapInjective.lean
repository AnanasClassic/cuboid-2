import Cuboid2.QuadraticReduction.GaussianProjectiveReductionHom
import Cuboid2.QuadraticReduction.GaussianE1LocalReduction

/-!
# Injectivity of the actual Gaussian split base changes

The two embeddings `ℚ(i) → ℚ_37` are field embeddings.  Mathlib's affine
point base-change homomorphism is therefore injective, and transport across
the displayed equalities of local Weierstrass models preserves that
injectivity.  This file packages those facts for both `E₀` and `E₁`.
-/

namespace Cuboid2
namespace GaussianLocalMapInjective

noncomputable section

open GaussianGoodReduction
open GaussianProjectiveReduction
open GaussianProjectiveReductionHom
open GaussianP37Bridge

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : DecidableEq ℚ_[37] := Classical.decEq _

/-- Transport across an equality of Weierstrass models is injective on
proof-carrying affine points. -/
theorem castPoint_injective
    {W V : WeierstrassCurve ℚ_[37]} (h : W = V) :
    Function.Injective (castPoint h) := by
  subst V
  intro P Q hPQ
  exact hPQ

/-- The plus base change on `E₀` is injective. -/
theorem mapE0PointPlus_injective :
    Function.Injective mapE0PointPlus := by
  letI : Algebra GaussianRat ℚ_[37] :=
    gaussianToPadicPlus.toRingHom.toAlgebra
  change
    Function.Injective
      (WeierstrassCurve.Affine.Point.map
        (W' := gaussianE0.toAffine)
        (R := GaussianRat) (S := GaussianRat)
        (F := GaussianRat) (K := ℚ_[37])
        (Algebra.ofId GaussianRat ℚ_[37]))
  exact
    WeierstrassCurve.Affine.Point.map_injective
      (W' := gaussianE0.toAffine)
      (R := GaussianRat) (S := GaussianRat)
      (F := GaussianRat) (K := ℚ_[37])
      (f := Algebra.ofId GaussianRat ℚ_[37])

/-- The minus base change on `E₀` is injective. -/
theorem mapE0PointMinus_injective :
    Function.Injective mapE0PointMinus := by
  letI : Algebra GaussianRat ℚ_[37] :=
    gaussianToPadicMinus.toRingHom.toAlgebra
  change
    Function.Injective
      (WeierstrassCurve.Affine.Point.map
        (W' := gaussianE0.toAffine)
        (R := GaussianRat) (S := GaussianRat)
        (F := GaussianRat) (K := ℚ_[37])
        (Algebra.ofId GaussianRat ℚ_[37]))
  exact
    WeierstrassCurve.Affine.Point.map_injective
      (W' := gaussianE0.toAffine)
      (R := GaussianRat) (S := GaussianRat)
      (F := GaussianRat) (K := ℚ_[37])
      (f := Algebra.ofId GaussianRat ℚ_[37])

/-- The transported plus local map on `E₀` is injective. -/
theorem mapE0PointPlusLocal_injective :
    Function.Injective mapE0PointPlusLocal :=
  (castPoint_injective localPadicCurve_plus_eq.symm).comp
    mapE0PointPlus_injective

/-- The transported minus local map on `E₀` is injective. -/
theorem mapE0PointMinusLocal_injective :
    Function.Injective mapE0PointMinusLocal :=
  (castPoint_injective localPadicCurve_minus_eq.symm).comp
    mapE0PointMinus_injective

/-- The plus local map on `E₀`, packaged as an additive homomorphism. -/
def mapE0PointPlusLocalHom :
    E0Point →+
      (localPadicCurve plusA plusB).toAffine.Point where
  toFun := mapE0PointPlusLocal
  map_zero' := mapE0PointPlusLocal_zero
  map_add' := mapE0PointPlusLocal_add

/-- The minus local map on `E₀`, packaged as an additive homomorphism. -/
def mapE0PointMinusLocalHom :
    E0Point →+
      (localPadicCurve minusA minusB).toAffine.Point where
  toFun := mapE0PointMinusLocal
  map_zero' := mapE0PointMinusLocal_zero
  map_add' := mapE0PointMinusLocal_add

theorem mapE0PointPlusLocalHom_injective :
    Function.Injective mapE0PointPlusLocalHom :=
  mapE0PointPlusLocal_injective

theorem mapE0PointMinusLocalHom_injective :
    Function.Injective mapE0PointMinusLocalHom :=
  mapE0PointMinusLocal_injective

/-! ## The rank-zero curve `E₁` -/

/-- The plus base change on `E₁` is injective. -/
theorem mapE1PointPlus_injective :
    Function.Injective
      GaussianE1LocalReduction.mapE1PointPlus := by
  letI : Algebra GaussianRat ℚ_[37] :=
    gaussianToPadicPlus.toRingHom.toAlgebra
  change
    Function.Injective
      (WeierstrassCurve.Affine.Point.map
        (W' := gaussianE1.toAffine)
        (R := GaussianRat) (S := GaussianRat)
        (F := GaussianRat) (K := ℚ_[37])
        (Algebra.ofId GaussianRat ℚ_[37]))
  exact
    WeierstrassCurve.Affine.Point.map_injective
      (W' := gaussianE1.toAffine)
      (R := GaussianRat) (S := GaussianRat)
      (F := GaussianRat) (K := ℚ_[37])
      (f := Algebra.ofId GaussianRat ℚ_[37])

/-- The minus base change on `E₁` is injective. -/
theorem mapE1PointMinus_injective :
    Function.Injective
      GaussianE1LocalReduction.mapE1PointMinus := by
  letI : Algebra GaussianRat ℚ_[37] :=
    gaussianToPadicMinus.toRingHom.toAlgebra
  change
    Function.Injective
      (WeierstrassCurve.Affine.Point.map
        (W' := gaussianE1.toAffine)
        (R := GaussianRat) (S := GaussianRat)
        (F := GaussianRat) (K := ℚ_[37])
        (Algebra.ofId GaussianRat ℚ_[37]))
  exact
    WeierstrassCurve.Affine.Point.map_injective
      (W' := gaussianE1.toAffine)
      (R := GaussianRat) (S := GaussianRat)
      (F := GaussianRat) (K := ℚ_[37])
      (f := Algebra.ofId GaussianRat ℚ_[37])

/-- The transported plus local map on `E₁` is injective. -/
theorem mapE1PointPlusLocal_injective :
    Function.Injective
      GaussianE1LocalReduction.mapE1PointPlusLocal :=
  (castPoint_injective
      GaussianE1LocalReduction.gaussianE1PadicPlus_eq_local).comp
    mapE1PointPlus_injective

/-- The transported minus local map on `E₁` is injective. -/
theorem mapE1PointMinusLocal_injective :
    Function.Injective
      GaussianE1LocalReduction.mapE1PointMinusLocal :=
  (castPoint_injective
      GaussianE1LocalReduction.gaussianE1PadicMinus_eq_local).comp
    mapE1PointMinus_injective

/-- The plus local map on `E₁`, packaged as an additive homomorphism. -/
def mapE1PointPlusLocalHom :
    gaussianE1.toAffine.Point →+
      (localPadicCurve
        GaussianE1LocalReduction.plusA
        GaussianE1LocalReduction.plusB).toAffine.Point where
  toFun := GaussianE1LocalReduction.mapE1PointPlusLocal
  map_zero' := GaussianE1LocalReduction.mapE1PointPlusLocal_zero
  map_add' := GaussianE1LocalReduction.mapE1PointPlusLocal_add

/-- The minus local map on `E₁`, packaged as an additive homomorphism. -/
def mapE1PointMinusLocalHom :
    gaussianE1.toAffine.Point →+
      (localPadicCurve
        GaussianE1LocalReduction.minusA
        GaussianE1LocalReduction.minusB).toAffine.Point where
  toFun := GaussianE1LocalReduction.mapE1PointMinusLocal
  map_zero' := GaussianE1LocalReduction.mapE1PointMinusLocal_zero
  map_add' := GaussianE1LocalReduction.mapE1PointMinusLocal_add

theorem mapE1PointPlusLocalHom_injective :
    Function.Injective mapE1PointPlusLocalHom :=
  mapE1PointPlusLocal_injective

theorem mapE1PointMinusLocalHom_injective :
    Function.Injective mapE1PointMinusLocalHom :=
  mapE1PointMinusLocal_injective

end

end GaussianLocalMapInjective
end Cuboid2
