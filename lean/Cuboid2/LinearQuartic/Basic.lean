import Mathlib

/-!
# The genus-two curve for the linear--quartic branch

This file contains only the exact affine model and its five known affine
rational points.  The unique point at infinity is treated separately by the
later projective rational-point classification.
-/

namespace Cuboid2

noncomputable section

/-- The right-hand side of the genus-two curve used to exclude a rational
root of the normalized Sharipov quintic. -/
def linearQuarticCurveRhs {R : Type*} [CommRing R] (t : R) : R :=
  t ^ 5 + 21 * t ^ 4 + 26 * t ^ 3 + 10 * t ^ 2 + 5 * t + 1

/-- An affine rational point on
`w² = t⁵ + 21t⁴ + 26t³ + 10t² + 5t + 1`. -/
structure LinearQuarticAffinePoint where
  t : ℚ
  w : ℚ
  onCurve : w ^ 2 = linearQuarticCurveRhs t

/-- The finite Weierstrass point `(-1, 0)`. -/
def linearQuarticNegOne : LinearQuarticAffinePoint where
  t := -1
  w := 0
  onCurve := by norm_num [linearQuarticCurveRhs]

/-- The known point `(0, 1)`. -/
def linearQuarticZeroPlus : LinearQuarticAffinePoint where
  t := 0
  w := 1
  onCurve := by norm_num [linearQuarticCurveRhs]

/-- The known point `(0, -1)`. -/
def linearQuarticZeroMinus : LinearQuarticAffinePoint where
  t := 0
  w := -1
  onCurve := by norm_num [linearQuarticCurveRhs]

/-- The known point `(1, 8)`. -/
def linearQuarticOnePlus : LinearQuarticAffinePoint where
  t := 1
  w := 8
  onCurve := by norm_num [linearQuarticCurveRhs]

/-- The known point `(1, -8)`. -/
def linearQuarticOneMinus : LinearQuarticAffinePoint where
  t := 1
  w := -8
  onCurve := by norm_num [linearQuarticCurveRhs]

/-- The factorization used by the split-quintic descent. -/
theorem linearQuarticCurveRhs_factorization (t : ℚ) :
    linearQuarticCurveRhs t =
      (t + 1) * (t ^ 4 + 20 * t ^ 3 + 6 * t ^ 2 + 4 * t + 1) := by
  simp [linearQuarticCurveRhs]
  ring

end

end Cuboid2
