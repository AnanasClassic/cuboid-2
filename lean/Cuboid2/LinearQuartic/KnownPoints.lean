import Cuboid2.LinearQuartic.Basic

/-!
# The six known rational points on the linear--quartic curve

The odd-degree model has one rational point at infinity.  Together with the
five affine points from `Basic.lean`, this gives the exact finite list used by
the linear-factor completion.

This file records only the points and the classification interface.  The
arithmetic-geometric proof that every rational point belongs to this list is
kept separate from the elementary inverse-image argument.
-/

namespace Cuboid2

noncomputable section

/-- A rational point on the smooth projective odd-degree model, represented
either by its unique point at infinity or by an affine point. -/
inductive LinearQuarticRationalPoint where
  | infinity
  | affine (point : LinearQuarticAffinePoint)

/-- The point at infinity on the odd-degree projective model. -/
def linearQuarticInfinity : LinearQuarticRationalPoint :=
  .infinity

/-- The affine Weierstrass point `(-1,0)`, viewed projectively. -/
def linearQuarticProjectiveNegOne : LinearQuarticRationalPoint :=
  .affine linearQuarticNegOne

/-- The affine point `(0,1)`, viewed projectively. -/
def linearQuarticProjectiveZeroPlus : LinearQuarticRationalPoint :=
  .affine linearQuarticZeroPlus

/-- The affine point `(0,-1)`, viewed projectively. -/
def linearQuarticProjectiveZeroMinus : LinearQuarticRationalPoint :=
  .affine linearQuarticZeroMinus

/-- The affine point `(1,8)`, viewed projectively. -/
def linearQuarticProjectiveOnePlus : LinearQuarticRationalPoint :=
  .affine linearQuarticOnePlus

/-- The affine point `(1,-8)`, viewed projectively. -/
def linearQuarticProjectiveOneMinus : LinearQuarticRationalPoint :=
  .affine linearQuarticOneMinus

/-- The six rational points appearing in the exact Chabauty certificate. -/
def knownLinearQuarticRationalPoints : List LinearQuarticRationalPoint :=
  [ linearQuarticInfinity,
    linearQuarticProjectiveNegOne,
    linearQuarticProjectiveZeroPlus,
    linearQuarticProjectiveZeroMinus,
    linearQuarticProjectiveOnePlus,
    linearQuarticProjectiveOneMinus ]

/--
The precise arithmetic-geometry interface needed by the elementary lift
argument: every rational point on the projective curve is one of the six
explicit points above.
-/
def LinearQuarticRationalPointClassification : Prop :=
  ∀ point : LinearQuarticRationalPoint,
    point ∈ knownLinearQuarticRationalPoints

/-- Membership in the known-point list, expanded as six explicit cases. -/
theorem mem_knownLinearQuarticRationalPoints_iff
    (point : LinearQuarticRationalPoint) :
    point ∈ knownLinearQuarticRationalPoints ↔
      point = linearQuarticInfinity ∨
      point = linearQuarticProjectiveNegOne ∨
      point = linearQuarticProjectiveZeroPlus ∨
      point = linearQuarticProjectiveZeroMinus ∨
      point = linearQuarticProjectiveOnePlus ∨
      point = linearQuarticProjectiveOneMinus := by
  simp [knownLinearQuarticRationalPoints]

end

end Cuboid2
