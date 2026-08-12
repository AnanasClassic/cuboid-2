import Cuboid2.FiveFive.DiscriminantRoots

/-!
# Exact rational brackets for the `5+5` discriminant cuts

The external replay isolates two positive roots of the degree-six factor and
three positive roots of the degree-twenty-eight factor.  This file checks all
ten endpoint signs and the placement of the seven sample parameters by exact
rational normalization.

These sign checks do not by themselves prove uniqueness of a root in each
bracket; that remaining Sturm obligation is tracked separately.
-/

namespace Cuboid2

noncomputable section

/-- Left endpoint of the first degree-six bracket has positive sign. -/
theorem fiveFiveDiscriminantP6_low_left_pos :
    0 < fiveFiveDiscriminantP6 (31 / 1000 : ℚ) := by
  norm_num [fiveFiveDiscriminantP6]

/-- Right endpoint of the first degree-six bracket has negative sign. -/
theorem fiveFiveDiscriminantP6_low_right_neg :
    fiveFiveDiscriminantP6 (32 / 1000 : ℚ) < 0 := by
  norm_num [fiveFiveDiscriminantP6]

/-- Left endpoint of the second degree-six bracket has negative sign. -/
theorem fiveFiveDiscriminantP6_high_left_neg :
    fiveFiveDiscriminantP6 (159 / 5 : ℚ) < 0 := by
  norm_num [fiveFiveDiscriminantP6]

/-- Right endpoint of the second degree-six bracket has positive sign. -/
theorem fiveFiveDiscriminantP6_high_right_pos :
    0 < fiveFiveDiscriminantP6 (319 / 10 : ℚ) := by
  norm_num [fiveFiveDiscriminantP6]

/-- Left endpoint of the first degree-twenty-eight bracket has negative sign. -/
theorem fiveFiveDiscriminantP28_first_left_neg :
    fiveFiveDiscriminantP28 (47 / 100 : ℚ) < 0 := by
  norm_num [fiveFiveDiscriminantP28]

/-- Right endpoint of the first degree-twenty-eight bracket has positive sign. -/
theorem fiveFiveDiscriminantP28_first_right_pos :
    0 < fiveFiveDiscriminantP28 (471 / 1000 : ℚ) := by
  norm_num [fiveFiveDiscriminantP28]

/-- Left endpoint of the second degree-twenty-eight bracket has positive sign. -/
theorem fiveFiveDiscriminantP28_second_left_pos :
    0 < fiveFiveDiscriminantP28 (786 / 25 : ℚ) := by
  norm_num [fiveFiveDiscriminantP28]

/-- Right endpoint of the second degree-twenty-eight bracket has negative sign. -/
theorem fiveFiveDiscriminantP28_second_right_neg :
    fiveFiveDiscriminantP28 (629 / 20 : ℚ) < 0 := by
  norm_num [fiveFiveDiscriminantP28]

/-- Left endpoint of the third degree-twenty-eight bracket has negative sign. -/
theorem fiveFiveDiscriminantP28_third_left_neg :
    fiveFiveDiscriminantP28 (1583 / 50 : ℚ) < 0 := by
  norm_num [fiveFiveDiscriminantP28]

/-- Right endpoint of the third degree-twenty-eight bracket has positive sign. -/
theorem fiveFiveDiscriminantP28_third_right_pos :
    0 < fiveFiveDiscriminantP28 (3167 / 100 : ℚ) := by
  norm_num [fiveFiveDiscriminantP28]

/-- Exact ordering of all rational bracket endpoints used by the replay. -/
theorem fiveFive_discriminant_bracket_order :
    (0 : ℚ) < 31 / 1000 ∧
    31 / 1000 < 32 / 1000 ∧
    32 / 1000 < 47 / 100 ∧
    47 / 100 < 471 / 1000 ∧
    471 / 1000 < 1 ∧
    1 < 786 / 25 ∧
    786 / 25 < 629 / 20 ∧
    629 / 20 < 1583 / 50 ∧
    1583 / 50 < 3167 / 100 ∧
    3167 / 100 < 159 / 5 ∧
    159 / 5 < 319 / 10 := by
  norm_num

/-- The seven exact sample parameters lie in the intended complementary intervals. -/
theorem fiveFive_sample_parameter_order :
    (0 : ℚ) < 1 / 100 ∧
    1 / 100 < 31 / 1000 ∧
    32 / 1000 < 1 / 5 ∧
    1 / 5 < 47 / 100 ∧
    471 / 1000 < 4 / 5 ∧
    4 / 5 < 1 ∧
    1 < 2 ∧
    2 < 786 / 25 ∧
    629 / 20 < 63 / 2 ∧
    63 / 2 < 1583 / 50 ∧
    3167 / 100 < 317 / 10 ∧
    317 / 10 < 159 / 5 ∧
    319 / 10 < 40 := by
  norm_num

end

end Cuboid2
