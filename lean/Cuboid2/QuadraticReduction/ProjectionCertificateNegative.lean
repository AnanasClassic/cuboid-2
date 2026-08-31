import Cuboid2.QuadraticReduction.ProjectionCertificate

/-!
# Negative compact projection certificate

This is the second physical sign.  As in the positive branch, the proof is an
explicit Bézout identity, so the implication from the two compact equations
to the 71-term projection does not trust a resultant implementation.
-/

namespace Cuboid2

noncomputable section

private def projectionBezoutC1Negative (z k : ℚ) : ℚ :=
  k ^ 8 * z ^ 8 + 10 * k ^ 8 * z ^ 6 + 4 * k ^ 8 * z ^ 4 -
    14 * k ^ 8 * z ^ 2 + k ^ 8 -
    12 * k ^ 6 * z ^ 8 - 4 * k ^ 6 * z ^ 6 + 41 * k ^ 6 * z ^ 4 -
    4 * k ^ 6 * z ^ 2 - 12 * k ^ 6 +
    3 * k ^ 4 * z ^ 8 + 18 * k ^ 4 * z ^ 6 - 27 * k ^ 4 * z ^ 4 -
    22 * k ^ 4 * z ^ 2 + 35 * k ^ 4 +
    6 * k ^ 2 * z ^ 6 - k ^ 2 * z ^ 4 - 2 * k ^ 2 * z ^ 2 -
    2 * z ^ 6 - z ^ 4 + 6 * z ^ 2

private def projectionBezoutA0Negative (z k : ℚ) : ℚ :=
  k ^ 12 * z ^ 4 +
    12 * k ^ 8 * z ^ 6 - 2 * k ^ 8 * z ^ 4 - 4 * k ^ 8 * z ^ 2 -
    4 * k ^ 6 * z ^ 6 - 2 * k ^ 6 * z ^ 4 + 12 * k ^ 6 * z ^ 2 +
    35 * k ^ 4 * z ^ 8 - 22 * k ^ 4 * z ^ 6 - 27 * k ^ 4 * z ^ 4 +
    18 * k ^ 4 * z ^ 2 + 3 * k ^ 4 -
    12 * k ^ 2 * z ^ 8 - 4 * k ^ 2 * z ^ 6 + 42 * k ^ 2 * z ^ 4 -
    4 * k ^ 2 * z ^ 2 - 12 * k ^ 2 +
    z ^ 8 - 14 * z ^ 6 + 4 * z ^ 4 + 10 * z ^ 2 + 1

private def projectionBezoutB1Negative (z k : ℚ) : ℚ :=
  2 * k ^ 12 * z ^ 4 +
    18 * k ^ 8 * z ^ 6 - 3 * k ^ 8 * z ^ 4 - 6 * k ^ 8 * z ^ 2 -
    6 * k ^ 6 * z ^ 6 - 3 * k ^ 6 * z ^ 4 + 18 * k ^ 6 * z ^ 2 +
    35 * k ^ 4 * z ^ 8 - 22 * k ^ 4 * z ^ 6 - 27 * k ^ 4 * z ^ 4 +
    18 * k ^ 4 * z ^ 2 + 3 * k ^ 4 -
    12 * k ^ 2 * z ^ 8 - 4 * k ^ 2 * z ^ 6 + 43 * k ^ 2 * z ^ 4 -
    4 * k ^ 2 * z ^ 2 - 12 * k ^ 2 +
    z ^ 8 - 14 * z ^ 6 + 4 * z ^ 4 + 10 * z ^ 2 + 1

private def projectionBezoutB0Negative (z k : ℚ) : ℚ :=
  -k ^ 12 * z ^ 8 - 10 * k ^ 12 * z ^ 6 - 4 * k ^ 12 * z ^ 4 +
    14 * k ^ 12 * z ^ 2 - k ^ 12 +
    12 * k ^ 10 * z ^ 8 + 4 * k ^ 10 * z ^ 6 - 42 * k ^ 10 * z ^ 4 +
    4 * k ^ 10 * z ^ 2 + 12 * k ^ 10 -
    3 * k ^ 8 * z ^ 8 - 18 * k ^ 8 * z ^ 6 + 27 * k ^ 8 * z ^ 4 +
    22 * k ^ 8 * z ^ 2 - 35 * k ^ 8 -
    12 * k ^ 6 * z ^ 6 + 2 * k ^ 6 * z ^ 4 + 4 * k ^ 6 * z ^ 2 +
    4 * k ^ 4 * z ^ 6 + 2 * k ^ 4 * z ^ 4 - 12 * k ^ 4 * z ^ 2 - z ^ 4

/-- Degree-two Bézout multiplier of `F1` on the negative branch. -/
def projectionBezoutANegative (z k y : ℚ) : ℚ :=
  k ^ 6 * z ^ 2 * compactLiftDenominator PhysicalSign.negative z k * y ^ 2 -
    k ^ 5 * projectionBezoutC1Negative z k * y +
    k ^ 4 * projectionBezoutA0Negative z k

/-- Degree-three Bézout multiplier of `F0` on the negative branch. -/
def projectionBezoutBNegative (z k y : ℚ) : ℚ :=
  k ^ 5 * z ^ 2 * compactLiftDenominator PhysicalSign.negative z k * y ^ 3 -
    k ^ 4 * projectionBezoutC1Negative z k * y ^ 2 +
    k ^ 3 * projectionBezoutB1Negative z k * y +
    projectionBezoutB0Negative z k

/-- Exact negative-branch Bézout identity replacing the external resultant call. -/
theorem compactProjectionNegative_bezout (z k y : ℚ) :
    projectionBezoutANegative z k y * compactF1 PhysicalSign.negative z k y +
        projectionBezoutBNegative z k y * compactF0 PhysicalSign.negative z k y =
      compactProjectionNegative (z ^ 2) (k ^ 2) := by
  simp [projectionBezoutANegative, projectionBezoutBNegative,
    projectionBezoutC1Negative, projectionBezoutA0Negative,
    projectionBezoutB1Negative, projectionBezoutB0Negative,
    compactLiftDenominator, compactF1, compactF0, PhysicalSign.value,
    compactProjectionNegative, compactProjectionPositive]
  ring

/-- Every negative compact solution reaches the stored projection curve. -/
theorem compactProjectionNegative_of_compact_equations
    {z k y : ℚ}
    (h1 : compactF1 PhysicalSign.negative z k y = 0)
    (h0 : compactF0 PhysicalSign.negative z k y = 0) :
    compactProjectionNegative (z ^ 2) (k ^ 2) = 0 := by
  rw [← compactProjectionNegative_bezout z k y, h1, h0]
  ring

end

end Cuboid2
