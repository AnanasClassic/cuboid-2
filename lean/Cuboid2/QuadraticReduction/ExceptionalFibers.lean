import Cuboid2.QuadraticReduction.Reciprocal

/-!
# Reciprocal-chart exceptional fibres

The positive 71-term projection is stored in a compact coefficient-by-`K`
form.  The negative projection is the exact twist `-Q₊(S,-K)`.  Lean checks
all six affine boundary fibres for both physical signs by polynomial
normalization.
-/

namespace Cuboid2

noncomputable section

/-- The relabelled positive compact projection `Q₊(S,K)`. -/
def compactProjectionPositive (S K : ℚ) : ℚ :=
  (-S ^ 4) * K ^ 10 +
    (S ^ 2 * (S ^ 4 - 14 * S ^ 3 + 4 * S ^ 2 + 10 * S + 1)) * K ^ 9 +
    (-S * (2 * S ^ 6 + 21 * S ^ 5 + 18 * S ^ 4 - 85 * S ^ 3 -
      38 * S ^ 2 + 85 * S - 6)) * K ^ 8 +
    (S ^ 8 + 8 * S ^ 7 - 82 * S ^ 6 + 272 * S ^ 5 - 38 * S ^ 4 -
      384 * S ^ 3 + 174 * S ^ 2 + 40 * S + 1) * K ^ 7 +
    (12 * S ^ 8 + 122 * S ^ 7 - 11 * S ^ 6 - 550 * S ^ 5 + 212 * S ^ 4 +
      498 * S ^ 3 - 331 * S ^ 2 + 34 * S + 12) * K ^ 6 +
    (2 * (19 * S ^ 8 - 232 * S ^ 7 + 305 * S ^ 6 + 202 * S ^ 5 -
      582 * S ^ 4 + 202 * S ^ 3 + 305 * S ^ 2 - 232 * S + 19)) * K ^ 5 +
    (12 * S ^ 8 + 34 * S ^ 7 - 331 * S ^ 6 + 498 * S ^ 5 + 212 * S ^ 4 -
      550 * S ^ 3 - 11 * S ^ 2 + 122 * S + 12) * K ^ 4 +
    (S ^ 8 + 40 * S ^ 7 + 174 * S ^ 6 - 384 * S ^ 5 - 38 * S ^ 4 +
      272 * S ^ 3 - 82 * S ^ 2 + 8 * S + 1) * K ^ 3 +
    (S * (6 * S ^ 6 - 85 * S ^ 5 + 38 * S ^ 4 + 85 * S ^ 3 -
      18 * S ^ 2 - 21 * S - 2)) * K ^ 2 +
    (S ^ 2 * (S ^ 4 + 10 * S ^ 3 + 4 * S ^ 2 - 14 * S + 1)) * K -
    S ^ 4

/-- The negative physical branch is the exact sign twist. -/
def compactProjectionNegative (S K : ℚ) : ℚ :=
  -compactProjectionPositive S (-K)

/-- The sole nontrivial rational-root-theorem fibre factor. -/
def reciprocalExceptionalQuartic (S : ℚ) : ℚ :=
  S ^ 4 - 32 * S ^ 3 - 62 * S ^ 2 - 32 * S + 1

/-- Positive branch, `K=1`. -/
theorem compactProjectionPositive_K_one (S : ℚ) :
    compactProjectionPositive S 1 = 64 * (S - 1) ^ 6 * (S + 1) ^ 2 := by
  simp [compactProjectionPositive]
  ring

/-- Positive branch, `K=-1`. -/
theorem compactProjectionPositive_K_neg_one (S : ℚ) :
    compactProjectionPositive S (-1) =
      -16 * (S - 1) ^ 4 * reciprocalExceptionalQuartic S := by
  simp [compactProjectionPositive, reciprocalExceptionalQuartic]
  ring

/-- Positive branch, `K=0`. -/
theorem compactProjectionPositive_K_zero (S : ℚ) :
    compactProjectionPositive S 0 = -S ^ 4 := by
  simp [compactProjectionPositive]

/-- Positive branch, `S=1`. -/
theorem compactProjectionPositive_S_one (K : ℚ) :
    compactProjectionPositive 1 K = -(K - 1) ^ 6 * (K + 1) ^ 4 := by
  simp [compactProjectionPositive]
  ring

/-- Positive branch, `S=0`. -/
theorem compactProjectionPositive_S_zero (K : ℚ) :
    compactProjectionPositive 0 K = K ^ 3 * (K ^ 2 + 6 * K + 1) ^ 2 := by
  simp [compactProjectionPositive]
  ring

/-- Positive branch, `S=-1`. -/
theorem compactProjectionPositive_S_neg_one (K : ℚ) :
    compactProjectionPositive (-1) K = -(K - 1) ^ 10 := by
  simp [compactProjectionPositive]
  ring

/-- Negative branch, `K=1`. -/
theorem compactProjectionNegative_K_one (S : ℚ) :
    compactProjectionNegative S 1 =
      16 * (S - 1) ^ 4 * reciprocalExceptionalQuartic S := by
  rw [compactProjectionNegative, compactProjectionPositive_K_neg_one]
  ring

/-- Negative branch, `K=-1`. -/
theorem compactProjectionNegative_K_neg_one (S : ℚ) :
    compactProjectionNegative S (-1) = -64 * (S - 1) ^ 6 * (S + 1) ^ 2 := by
  simp only [compactProjectionNegative, neg_neg]
  rw [compactProjectionPositive_K_one]
  ring

/-- Negative branch, `K=0`. -/
theorem compactProjectionNegative_K_zero (S : ℚ) :
    compactProjectionNegative S 0 = S ^ 4 := by
  simp only [compactProjectionNegative, neg_zero]
  rw [compactProjectionPositive_K_zero]
  ring

/-- Negative branch, `S=1`. -/
theorem compactProjectionNegative_S_one (K : ℚ) :
    compactProjectionNegative 1 K = (K + 1) ^ 6 * (K - 1) ^ 4 := by
  simp [compactProjectionNegative, compactProjectionPositive]
  ring

/-- Negative branch, `S=0`. -/
theorem compactProjectionNegative_S_zero (K : ℚ) :
    compactProjectionNegative 0 K = K ^ 3 * (K ^ 2 - 6 * K + 1) ^ 2 := by
  simp [compactProjectionNegative, compactProjectionPositive]
  ring

/-- Negative branch, `S=-1`. -/
theorem compactProjectionNegative_S_neg_one (K : ℚ) :
    compactProjectionNegative (-1) K = (K + 1) ^ 10 := by
  simp [compactProjectionNegative, compactProjectionPositive]
  ring

@[simp] theorem reciprocalExceptionalQuartic_one :
    reciprocalExceptionalQuartic 1 = -124 := by
  norm_num [reciprocalExceptionalQuartic]

@[simp] theorem reciprocalExceptionalQuartic_neg_one :
    reciprocalExceptionalQuartic (-1) = 4 := by
  norm_num [reciprocalExceptionalQuartic]

/-- The three quadratic chart factors have negative discriminant. -/
theorem reciprocal_chart_quadratic_discriminants :
    ((-1 : ℚ) ^ 2 - 4, (1 : ℚ) ^ 2 - 4, (0 : ℚ) ^ 2 - 4) = (-3, -3, -4) := by
  norm_num

end

end Cuboid2
