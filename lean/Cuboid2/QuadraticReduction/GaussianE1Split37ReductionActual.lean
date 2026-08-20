import Cuboid2.QuadraticReduction.GaussianE1LocalReduction
import Cuboid2.QuadraticReduction.GaussianSplit37ReductionActual

/-!
# Actual split-37 reduction homomorphisms for the rank-zero curve

This module specializes the generic projective reduction theorem to the two
integral `37`-adic models of `E₁`.  It also connects both reductions to the
closed exhaustive finite-point tables used by the torsion certificates.
-/

namespace Cuboid2
namespace GaussianE1Split37ReductionActual

noncomputable section

open GaussianE1LocalReduction
open GaussianFinite
open GaussianFiniteExponent
open GaussianSplit37ReductionActual

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have hxnonneg : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : DecidableEq ℚ_[37] := Classical.decEq _

abbrev E1Point := gaussianE1.toAffine.Point

/-- The plus specialization is an actual homomorphism into the executable
finite group law. -/
theorem reduceE1Plus_add (Q R : E1Point) :
    reduceE1Plus (Q + R) =
      finiteAdd 37 e1PlusCoefficients.1 e1PlusCoefficients.2
        (reduceE1Plus Q) (reduceE1Plus R) := by
  change
    GaussianProjectiveReduction.finiteReducePoint
        GaussianE1LocalReduction.plusA
        GaussianE1LocalReduction.plusB
        (mapE1PointPlusLocal (Q + R)) =
      finiteAdd 37 e1PlusCoefficients.1 e1PlusCoefficients.2
        (GaussianProjectiveReduction.finiteReducePoint
          GaussianE1LocalReduction.plusA
          GaussianE1LocalReduction.plusB (mapE1PointPlusLocal Q))
        (GaussianProjectiveReduction.finiteReducePoint
          GaussianE1LocalReduction.plusA
          GaussianE1LocalReduction.plusB (mapE1PointPlusLocal R))
  rw [mapE1PointPlusLocal_add,
    GaussianSplit37ReductionActual.finiteReducePoint_add,
    plus_coefficients.1, plus_coefficients.2]

/-- The minus specialization is an actual homomorphism into the executable
finite group law. -/
theorem reduceE1Minus_add (Q R : E1Point) :
    reduceE1Minus (Q + R) =
      finiteAdd 37 e1MinusCoefficients.1 e1MinusCoefficients.2
        (reduceE1Minus Q) (reduceE1Minus R) := by
  change
    GaussianProjectiveReduction.finiteReducePoint
        GaussianE1LocalReduction.minusA
        GaussianE1LocalReduction.minusB
        (mapE1PointMinusLocal (Q + R)) =
      finiteAdd 37 e1MinusCoefficients.1 e1MinusCoefficients.2
        (GaussianProjectiveReduction.finiteReducePoint
          GaussianE1LocalReduction.minusA
          GaussianE1LocalReduction.minusB (mapE1PointMinusLocal Q))
        (GaussianProjectiveReduction.finiteReducePoint
          GaussianE1LocalReduction.minusA
          GaussianE1LocalReduction.minusB (mapE1PointMinusLocal R))
  rw [mapE1PointMinusLocal_add,
    GaussianSplit37ReductionActual.finiteReducePoint_add,
    minus_coefficients.1, minus_coefficients.2]

/-- Every actual plus reduction occurs in the exhaustive table. -/
theorem reduceE1Plus_mem_finitePoints (Q : E1Point) :
    reduceE1Plus Q ∈
      finitePoints 37 e1PlusCoefficients.1 e1PlusCoefficients.2 := by
  rw [← plus_coefficients.1, ← plus_coefficients.2]
  exact
    finiteReducePoint_mem_finitePoints
      GaussianE1LocalReduction.plusA
      GaussianE1LocalReduction.plusB (mapE1PointPlusLocal Q)

/-- Every actual minus reduction occurs in the exhaustive table. -/
theorem reduceE1Minus_mem_finitePoints (Q : E1Point) :
    reduceE1Minus Q ∈
      finitePoints 37 e1MinusCoefficients.1 e1MinusCoefficients.2 := by
  rw [← minus_coefficients.1, ← minus_coefficients.2]
  exact
    finiteReducePoint_mem_finitePoints
      GaussianE1LocalReduction.minusA
      GaussianE1LocalReduction.minusB (mapE1PointMinusLocal Q)

end

end GaussianE1Split37ReductionActual
end Cuboid2
