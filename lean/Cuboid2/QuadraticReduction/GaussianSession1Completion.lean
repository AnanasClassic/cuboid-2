import Cuboid2.QuadraticReduction.GaussianActualTorsion
import Cuboid2.QuadraticReduction.GaussianClassification
import Cuboid2.QuadraticReduction.GaussianCompletion
import Cuboid2.QuadraticReduction.GaussianCoverZeroRowCompletion
import Cuboid2.QuadraticReduction.GaussianP29PolynomialRootBridge

/-!
# Unconditional completion of the quadratic--cubic branch

This module closes the last global input of the Gaussian route.  The visible
rank-one point is not assumed to be primitive: its coefficient in an
arbitrary exact normal form is proved coprime to the indices used by the
finite and formal arguments.
-/

namespace Cuboid2
namespace GaussianSession1Completion

noncomputable section

/-- Every rational point on the untwisted Gaussian cover maps to one of the
two visible points on its elliptic quotient. -/
theorem gaussianCoverZeroClassified :
    GaussianCoverZeroClassified := by
  intro C
  obtain ⟨e⟩ := GaussianActualTorsion.gaussianE0_equiv
  obtain ⟨m, k, δ, ε, hδ, hε, hP, hC⟩ :=
    GaussianIndexIndependent.exists_visible_and_point_normalForms e C.toE0
  have hseven : ¬(7 : ℤ) ∣ m :=
    GaussianP29PolynomialRootBridge.seven_not_dvd_visiblePoint_coefficient
      e hP
  exact
    GaussianCoverZeroRowCompletion.coverZero_toE0_eq_visible_or_neg
      e C hδ hε hP hC hseven

/-- The Gaussian split and the two unconditional elliptic classifications
give the exact four rational points on the octic curve. -/
theorem octicRationalPointsClassified :
    OcticRationalPointsClassified :=
  octic_classified_of_gaussian_covers
    gaussianCoverZeroClassified
    GaussianActualTorsion.gaussianCoverOneEllipticClassified

/-- The specialized Sharipov `2+3` factorization case is impossible without
any additional mathematical hypothesis. -/
theorem quadratic_cubic_impossible_sharipov
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hcop : Nat.Coprime p q) (hne : p ≠ q) :
    ¬ QuadraticCubicCase (sharipovParameter p q) :=
  quadratic_cubic_impossible_sharipov_of_octic_classified
    octicRationalPointsClassified hp hq hcop hne

end

end GaussianSession1Completion
end Cuboid2
