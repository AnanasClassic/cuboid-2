import Cuboid2.QuadraticReduction.CompactModel
import Cuboid2.QuadraticReduction.ExceptionalFibers

/-!
# Compact projection certificate

Rather than trusting a CAS resultant, Lean checks a Bézout identity.  For the
positive physical sign, explicit polynomials `A(y)` and `B(y)` satisfy

`A*F1 + B*F0 = Q₊(z²,k²)`.

Thus every common zero of the two compact equations lies on the stored
71-term projection.  The certificate was generated externally, but its
validity is reduced to a polynomial identity in the Lean kernel.
-/

namespace Cuboid2

noncomputable section

private def projectionBezoutC1Positive (z k : ℚ) : ℚ :=
  k ^ 8 * z ^ 8 + 10 * k ^ 8 * z ^ 6 + 4 * k ^ 8 * z ^ 4 -
    14 * k ^ 8 * z ^ 2 + k ^ 8 +
    12 * k ^ 6 * z ^ 8 + 4 * k ^ 6 * z ^ 6 - 41 * k ^ 6 * z ^ 4 +
    4 * k ^ 6 * z ^ 2 + 12 * k ^ 6 +
    3 * k ^ 4 * z ^ 8 + 18 * k ^ 4 * z ^ 6 - 27 * k ^ 4 * z ^ 4 -
    22 * k ^ 4 * z ^ 2 + 35 * k ^ 4 -
    6 * k ^ 2 * z ^ 6 + k ^ 2 * z ^ 4 + 2 * k ^ 2 * z ^ 2 -
    2 * z ^ 6 - z ^ 4 + 6 * z ^ 2

private def projectionBezoutA0Positive (z k : ℚ) : ℚ :=
  k ^ 12 * z ^ 4 +
    12 * k ^ 8 * z ^ 6 - 2 * k ^ 8 * z ^ 4 - 4 * k ^ 8 * z ^ 2 +
    4 * k ^ 6 * z ^ 6 + 2 * k ^ 6 * z ^ 4 - 12 * k ^ 6 * z ^ 2 +
    35 * k ^ 4 * z ^ 8 - 22 * k ^ 4 * z ^ 6 - 27 * k ^ 4 * z ^ 4 +
    18 * k ^ 4 * z ^ 2 + 3 * k ^ 4 +
    12 * k ^ 2 * z ^ 8 + 4 * k ^ 2 * z ^ 6 - 42 * k ^ 2 * z ^ 4 +
    4 * k ^ 2 * z ^ 2 + 12 * k ^ 2 +
    z ^ 8 - 14 * z ^ 6 + 4 * z ^ 4 + 10 * z ^ 2 + 1

private def projectionBezoutB1Positive (z k : ℚ) : ℚ :=
  2 * k ^ 12 * z ^ 4 +
    18 * k ^ 8 * z ^ 6 - 3 * k ^ 8 * z ^ 4 - 6 * k ^ 8 * z ^ 2 +
    6 * k ^ 6 * z ^ 6 + 3 * k ^ 6 * z ^ 4 - 18 * k ^ 6 * z ^ 2 +
    35 * k ^ 4 * z ^ 8 - 22 * k ^ 4 * z ^ 6 - 27 * k ^ 4 * z ^ 4 +
    18 * k ^ 4 * z ^ 2 + 3 * k ^ 4 +
    12 * k ^ 2 * z ^ 8 + 4 * k ^ 2 * z ^ 6 - 43 * k ^ 2 * z ^ 4 +
    4 * k ^ 2 * z ^ 2 + 12 * k ^ 2 +
    z ^ 8 - 14 * z ^ 6 + 4 * z ^ 4 + 10 * z ^ 2 + 1

private def projectionBezoutB0Positive (z k : ℚ) : ℚ :=
  k ^ 12 * z ^ 8 + 10 * k ^ 12 * z ^ 6 + 4 * k ^ 12 * z ^ 4 -
    14 * k ^ 12 * z ^ 2 + k ^ 12 +
    12 * k ^ 10 * z ^ 8 + 4 * k ^ 10 * z ^ 6 - 42 * k ^ 10 * z ^ 4 +
    4 * k ^ 10 * z ^ 2 + 12 * k ^ 10 +
    3 * k ^ 8 * z ^ 8 + 18 * k ^ 8 * z ^ 6 - 27 * k ^ 8 * z ^ 4 -
    22 * k ^ 8 * z ^ 2 + 35 * k ^ 8 -
    12 * k ^ 6 * z ^ 6 + 2 * k ^ 6 * z ^ 4 + 4 * k ^ 6 * z ^ 2 -
    4 * k ^ 4 * z ^ 6 - 2 * k ^ 4 * z ^ 4 + 12 * k ^ 4 * z ^ 2 + z ^ 4

/-- Degree-two Bézout multiplier of `F1` on the positive branch. -/
def projectionBezoutAPositive (z k y : ℚ) : ℚ :=
  k ^ 6 * z ^ 2 * compactLiftDenominator PhysicalSign.positive z k * y ^ 2 +
    k ^ 5 * projectionBezoutC1Positive z k * y -
    k ^ 4 * projectionBezoutA0Positive z k

/-- Degree-three Bézout multiplier of `F0` on the positive branch. -/
def projectionBezoutBPositive (z k y : ℚ) : ℚ :=
  -k ^ 5 * z ^ 2 * compactLiftDenominator PhysicalSign.positive z k * y ^ 3 -
    k ^ 4 * projectionBezoutC1Positive z k * y ^ 2 +
    k ^ 3 * projectionBezoutB1Positive z k * y +
    projectionBezoutB0Positive z k

/-- Exact positive-branch Bézout identity replacing the external resultant call. -/
theorem compactProjectionPositive_bezout (z k y : ℚ) :
    projectionBezoutAPositive z k y * compactF1 PhysicalSign.positive z k y +
        projectionBezoutBPositive z k y * compactF0 PhysicalSign.positive z k y =
      compactProjectionPositive (z ^ 2) (k ^ 2) := by
  simp [projectionBezoutAPositive, projectionBezoutBPositive,
    projectionBezoutC1Positive, projectionBezoutA0Positive,
    projectionBezoutB1Positive, projectionBezoutB0Positive,
    compactLiftDenominator, compactF1, compactF0, PhysicalSign.value,
    compactProjectionPositive]
  ring

/-- Every positive compact solution reaches the stored projection curve. -/
theorem compactProjectionPositive_of_compact_equations
    {z k y : ℚ}
    (h1 : compactF1 PhysicalSign.positive z k y = 0)
    (h0 : compactF0 PhysicalSign.positive z k y = 0) :
    compactProjectionPositive (z ^ 2) (k ^ 2) = 0 := by
  rw [← compactProjectionPositive_bezout z k y, h1, h0]
  ring

end

end Cuboid2
