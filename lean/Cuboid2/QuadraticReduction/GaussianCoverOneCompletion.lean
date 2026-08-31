import Cuboid2.QuadraticReduction.GaussianClassification
import Cuboid2.QuadraticReduction.GaussianTorsionNormalForm

/-!
# Rank-zero Gaussian cover completion

The only local input retained here is the actual two-torsion bound that will
be supplied by the two split reductions at 37.  The unconditional rank-zero
Mordell--Weil theorem then classifies every point on `E₁`, and hence every
elliptic image of the twisted quartic cover.
-/

namespace Cuboid2
namespace GaussianCoverOneCompletion

noncomputable section

open GaussianTorsionNormalForm

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have hxnonneg : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

/-- An actual two-torsion bound on the rank-zero curve supplies the exact
elliptic classification consumed by `GaussianClassification`. -/
theorem classified_of_torsion_two
    (hTwo :
      ∀ P : gaussianE1.toAffine.Point,
        IsOfFinAddOrder P → 2 • P = 0) :
    GaussianCoverOneEllipticClassified := by
  intro C
  exact gaussianE1_point_classified_of_torsion_two hTwo C.toE1

end

end GaussianCoverOneCompletion
end Cuboid2
