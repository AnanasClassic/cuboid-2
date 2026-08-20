import Cuboid2.QuadraticReduction.GaussianE1Split37ReductionActual
import Cuboid2.QuadraticReduction.GaussianCoverOneCompletion
import Cuboid2.QuadraticReduction.GaussianFiniteExponent
import Cuboid2.QuadraticReduction.GaussianFormalKernelTorsion
import Cuboid2.QuadraticReduction.GaussianLocalMapInjective
import Cuboid2.QuadraticReduction.GaussianSplit37ReductionActual
import Cuboid2.QuadraticReduction.GaussianTorsionNormalForm

/-!
# Actual Gaussian torsion from the two split fibres at 37

Both projective reduction maps are genuine homomorphisms.  The exhaustive
finite tables put suitable multiples of every torsion point in the
infinity kernel, whose actual formal parameter is torsion-free.  Injectivity
of base change then transports the resulting equalities back to
`ℚ(i)`.
-/

namespace Cuboid2
namespace GaussianActualTorsion

noncomputable section

open GaussianE1LocalReduction
open GaussianE1Split37ReductionActual
open GaussianFinite
open GaussianFiniteExponent
open GaussianFormalKernelDisk
open GaussianFormalKernelTorsion
open GaussianLocalMapInjective
open GaussianProjectiveReduction
open GaussianProjectiveReductionHom
open GaussianP37
open GaussianSplit37ReductionActual
open GaussianTorsionNormalForm

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have hxnonneg : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : DecidableEq ℚ_[37] := Classical.decEq _

/-- A torsion point whose injective local image belongs to the actual
infinity kernel is zero. -/
theorem eq_zero_of_torsion_map_mem_infinityKernel
    {G : Type*} [AddCommGroup G]
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (f : G →+ (localPadicCurve A B).toAffine.Point)
    (hf : Function.Injective f)
    (P : G)
    (hP : IsOfFinAddOrder P)
    (hmem : f P ∈ infinityKernel A B) :
    P = 0 := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero] at hP
  obtain ⟨n, hn, hnP⟩ := hP
  let V : infinityKernel A B := ⟨f P, hmem⟩
  have hnV : n • V = 0 := by
    apply Subtype.ext
    change n • f P = 0
    rw [← map_nsmul, hnP, map_zero]
  have hV : V = 0 := by
    apply infinityKernel_nsmul_right_injective A B n hn.ne'
    simpa only [nsmul_zero] using hnV
  apply hf
  rw [map_zero]
  change (V : (localPadicCurve A B).toAffine.Point) = 0
  exact congrArg Subtype.val hV

/-- Natural multiples of a torsion point are torsion. -/
theorem isOfFinAddOrder_nsmul
    {G : Type*} [AddCommGroup G]
    (P : G) (hP : IsOfFinAddOrder P) (c : ℕ) :
    IsOfFinAddOrder (c • P) := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero] at hP ⊢
  obtain ⟨n, hn, hnP⟩ := hP
  refine ⟨n, hn, ?_⟩
  rw [nsmul_left_comm, hnP, nsmul_zero]

/-! ## The rank-one curve -/

/-- Every actual `E₀` torsion point is killed by twelve, using the plus
split fibre. -/
theorem gaussianE0_torsion_twelve
    (P : gaussianE0.toAffine.Point)
    (hP : IsOfFinAddOrder P) :
    12 • P = 0 := by
  have hred :
      reduceE0Plus (12 • P) = none := by
    calc
      reduceE0Plus (12 • P) =
          finiteMul 37 plusCoefficients.1 plusCoefficients.2
            (reduceE0Plus P) 12 :=
        map_nsmul_finite
          37 plusCoefficients.1 plusCoefficients.2
          reduceE0Plus reduceE0Plus_zero reduceE0Plus_add P 12
      _ = none :=
        plus_twelve_eq_none_of_mem
          (reduceE0Plus_mem_finitePoints P)
  apply
    eq_zero_of_torsion_map_mem_infinityKernel
      GaussianProjectiveReduction.plusA
      GaussianProjectiveReduction.plusB
      mapE0PointPlusLocalHom mapE0PointPlusLocalHom_injective
      (12 • P) (isOfFinAddOrder_nsmul P hP 12)
  exact hred

/-- Every actual `E₀` torsion point is killed by forty-two, using the minus
split fibre. -/
theorem gaussianE0_torsion_fortyTwo
    (P : gaussianE0.toAffine.Point)
    (hP : IsOfFinAddOrder P) :
    42 • P = 0 := by
  have hred :
      reduceE0Minus (42 • P) = none := by
    calc
      reduceE0Minus (42 • P) =
          finiteMul 37 minusCoefficients.1 minusCoefficients.2
            (reduceE0Minus P) 42 :=
        map_nsmul_finite
          37 minusCoefficients.1 minusCoefficients.2
          reduceE0Minus reduceE0Minus_zero reduceE0Minus_add P 42
      _ = none :=
        minus_fortyTwo_eq_none_of_mem
          (reduceE0Minus_mem_finitePoints P)
  apply
    eq_zero_of_torsion_map_mem_infinityKernel
      GaussianProjectiveReduction.minusA
      GaussianProjectiveReduction.minusB
      mapE0PointMinusLocalHom mapE0PointMinusLocalHom_injective
      (42 • P) (isOfFinAddOrder_nsmul P hP 42)
  exact hred

/-- The two actual split fibres give the exact six-torsion bound needed by
the algebraic torsion classification. -/
theorem gaussianE0_torsion_six
    (P : gaussianE0.toAffine.Point)
    (hP : IsOfFinAddOrder P) :
    6 • P = 0 :=
  six_nsmul_eq_zero_of_twelve_and_fortyTwo P
    (gaussianE0_torsion_twelve P hP)
    (gaussianE0_torsion_fortyTwo P hP)

/-- Unconditional exact normal form of the rank-one Gaussian curve. -/
theorem gaussianE0_equiv :
    Nonempty (gaussianE0.toAffine.Point ≃+ ℤ × ZMod 2) :=
  gaussianE0_equiv_of_torsion_six gaussianE0_torsion_six

/-! ## The rank-zero curve -/

/-- Every actual `E₁` torsion point is killed by twenty-eight on the plus
split fibre. -/
theorem gaussianE1_torsion_twentyEight
    (P : gaussianE1.toAffine.Point)
    (hP : IsOfFinAddOrder P) :
    28 • P = 0 := by
  have hred :
      reduceE1Plus (28 • P) = none := by
    calc
      reduceE1Plus (28 • P) =
          finiteMul 37 e1PlusCoefficients.1 e1PlusCoefficients.2
            (reduceE1Plus P) 28 :=
        map_nsmul_finite
          37 e1PlusCoefficients.1 e1PlusCoefficients.2
          reduceE1Plus reduceE1Plus_zero reduceE1Plus_add P 28
      _ = none :=
        e1Plus_twentyEight_eq_none_of_mem
          (reduceE1Plus_mem_finitePoints P)
  apply
    eq_zero_of_torsion_map_mem_infinityKernel
      GaussianE1LocalReduction.plusA
      GaussianE1LocalReduction.plusB
      mapE1PointPlusLocalHom mapE1PointPlusLocalHom_injective
      (28 • P) (isOfFinAddOrder_nsmul P hP 28)
  exact hred

/-- Every actual `E₁` torsion point is killed by thirty-four on the minus
split fibre. -/
theorem gaussianE1_torsion_thirtyFour
    (P : gaussianE1.toAffine.Point)
    (hP : IsOfFinAddOrder P) :
    34 • P = 0 := by
  have hred :
      reduceE1Minus (34 • P) = none := by
    calc
      reduceE1Minus (34 • P) =
          finiteMul 37 e1MinusCoefficients.1 e1MinusCoefficients.2
            (reduceE1Minus P) 34 :=
        map_nsmul_finite
          37 e1MinusCoefficients.1 e1MinusCoefficients.2
          reduceE1Minus reduceE1Minus_zero reduceE1Minus_add P 34
      _ = none :=
        e1Minus_thirtyFour_eq_none_of_mem
          (reduceE1Minus_mem_finitePoints P)
  apply
    eq_zero_of_torsion_map_mem_infinityKernel
      GaussianE1LocalReduction.minusA
      GaussianE1LocalReduction.minusB
      mapE1PointMinusLocalHom mapE1PointMinusLocalHom_injective
      (34 • P) (isOfFinAddOrder_nsmul P hP 34)
  exact hred

/-- The two split fibres leave only actual two-torsion on `E₁`. -/
theorem gaussianE1_torsion_two
    (P : gaussianE1.toAffine.Point)
    (hP : IsOfFinAddOrder P) :
    2 • P = 0 :=
  two_nsmul_eq_zero_of_twentyEight_and_thirtyFour P
    (gaussianE1_torsion_twentyEight P hP)
    (gaussianE1_torsion_thirtyFour P hP)

/-- Every point on the actual rank-zero Gaussian curve is infinity or its
named nonzero two-torsion point. -/
theorem gaussianE1_point_classified
    (P : gaussianE1.toAffine.Point) :
    P = 0 ∨ P = gaussianE1T :=
  gaussianE1_point_classified_of_torsion_two gaussianE1_torsion_two P

/-- Unconditional elliptic classification consumed by the twisted cover. -/
theorem gaussianCoverOneEllipticClassified :
    GaussianCoverOneEllipticClassified := by
  intro C
  exact gaussianE1_point_classified C.toE1

end

end GaussianActualTorsion
end Cuboid2
