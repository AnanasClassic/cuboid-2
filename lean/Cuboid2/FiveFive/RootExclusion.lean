import Cuboid2.FiveFive.SamplePositivityReal
import Cuboid2.FiveFive.RootTransport

/-!
# Final real-root exclusion for the symmetric `5+5` case

Exact P6/P28 isolation splits the positive parameter line at five critical
roots and `1`. Projective first-contact transport carries strict positivity
from one exact SOS/LDL sample in each complementary cell.
-/

namespace Cuboid2

noncomputable section

/--
The explicit degree-sixteen resultant factor has no rational root at any
admissible positive rational parameter.
-/
theorem fiveFiveResultantFactor_ne_zero
    {s : ℚ} (hs : 0 < s) (hs1 : s ≠ 1) (y : ℚ) :
    fiveFiveResultantFactor s y ≠ 0 := by
  let sr : ℝ := (s : ℝ)
  have hsr : 0 < sr := by
    change (0 : ℝ) < (s : ℝ)
    exact_mod_cast hs
  have hsr1 : sr ≠ 1 := by
    change (s : ℝ) ≠ 1
    exact_mod_cast hs1
  have hp6 := fiveFiveDiscriminantP6PolyReal_ratCast_ne_zero s
  have hp28 := fiveFiveDiscriminantP28PolyReal_ratCast_ne_zero s
  have hlow : sr ≠ fiveFiveP6LowCut := by
    intro h
    change (s : ℝ) = fiveFiveP6LowCut at h
    apply hp6
    rw [h, fiveFiveP6LowCut_spec.2]
  have hfirst : sr ≠ fiveFiveP28FirstCut := by
    intro h
    change (s : ℝ) = fiveFiveP28FirstCut at h
    apply hp28
    rw [h, fiveFiveP28FirstCut_spec.2]
  have hsecond : sr ≠ fiveFiveP28SecondCut := by
    intro h
    change (s : ℝ) = fiveFiveP28SecondCut at h
    apply hp28
    rw [h, fiveFiveP28SecondCut_spec.2]
  have hthird : sr ≠ fiveFiveP28ThirdCut := by
    intro h
    change (s : ℝ) = fiveFiveP28ThirdCut at h
    apply hp28
    rw [h, fiveFiveP28ThirdCut_spec.2]
  have hhigh : sr ≠ fiveFiveP6HighCut := by
    intro h
    change (s : ℝ) = fiveFiveP6HighCut at h
    apply hp6
    rw [h, fiveFiveP6HighCut_spec.2]
  suffices hreal : fiveFiveResultantFactorReal sr (y : ℝ) ≠ 0 by
    intro hzero
    apply hreal
    have hcast : (fiveFiveResultantFactor s y : ℝ) = 0 := by
      exact_mod_cast hzero
    rw [← eval_fiveFiveResultantFactorPolyReal_ratCast] at hcast
    simpa only [eval_fiveFiveResultantFactorPolyReal] using hcast
  rcases fiveFive_sample_real_parameter_cells with
    ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6⟩
  rcases lt_or_gt_of_ne hlow with hs0 | hs0
  · exact fiveFiveResultantFactorReal_ne_zero_of_segment
      (1 / 100) sr (by norm_num) hsr
      fiveFive_sample_one_hundredth_pos_real
      (fun t ht => fiveFive_critical_free_below_p6_low
        (affine_segment_mem_Ioo hq0 ⟨hsr, hs0⟩ ht).1
        (affine_segment_mem_Ioo hq0 ⟨hsr, hs0⟩ ht).2) _
  rcases lt_or_gt_of_ne hfirst with hs1' | hs1'
  · exact fiveFiveResultantFactorReal_ne_zero_of_segment
      (1 / 5) sr (by norm_num) hsr
      fiveFive_sample_one_fifth_pos_real
      (fun t ht => fiveFive_critical_free_p6_low_p28_first
        (affine_segment_mem_Ioo hq1 ⟨hs0, hs1'⟩ ht)) _
  rcases lt_or_gt_of_ne hsr1 with hs2 | hs2
  · exact fiveFiveResultantFactorReal_ne_zero_of_segment
      (4 / 5) sr (by norm_num) hsr
      fiveFive_sample_four_fifths_pos_real
      (fun t ht => fiveFive_critical_free_p28_first_one
        (affine_segment_mem_Ioo hq2 ⟨hs1', hs2⟩ ht)) _
  rcases lt_or_gt_of_ne hsecond with hs3 | hs3
  · exact fiveFiveResultantFactorReal_ne_zero_of_segment
      2 sr (by norm_num) hsr
      fiveFive_sample_two_pos_real
      (fun t ht => fiveFive_critical_free_one_p28_second
        (affine_segment_mem_Ioo hq3 ⟨hs2, hs3⟩ ht)) _
  rcases lt_or_gt_of_ne hthird with hs4 | hs4
  · exact fiveFiveResultantFactorReal_ne_zero_of_segment
      (63 / 2) sr (by norm_num) hsr
      fiveFive_sample_sixty_three_halves_pos_real
      (fun t ht => fiveFive_critical_free_p28_second_third
        (affine_segment_mem_Ioo hq4 ⟨hs3, hs4⟩ ht)) _
  rcases lt_or_gt_of_ne hhigh with hs5 | hs5
  · exact fiveFiveResultantFactorReal_ne_zero_of_segment
      (317 / 10) sr (by norm_num) hsr
      fiveFive_sample_three_hundred_seventeen_tenths_pos_real
      (fun t ht => fiveFive_critical_free_p28_third_p6_high
        (affine_segment_mem_Ioo hq5 ⟨hs4, hs5⟩ ht)) _
  · exact fiveFiveResultantFactorReal_ne_zero_of_segment
      40 sr (by norm_num) hsr
      fiveFive_sample_forty_pos_real
      (fun t ht => fiveFive_critical_free_above_p6_high
        (affine_segment_gt hq6 hs5 ht)) _

/-- The normalized two-equation locus is empty once the explicit factor is nonzero. -/
theorem fiveFive_reduced_locus_empty
    {s : ℚ} (hs : 0 < s) (hs1 : s ≠ 1) :
    ¬ Nonempty (FiveFiveReducedPoint s) := by
  rintro ⟨P⟩
  exact fiveFiveResultantFactor_ne_zero hs hs1 P.y P.resultantFactor_eq_zero

/-- The original symmetric factorization is impossible once the reduced locus is empty. -/
theorem symmetric_five_five_impossible_from_reduced
    {s : ℚ} (hs : 0 < s) (hs1 : s ≠ 1) :
    ¬ SymmetricFiveFiveCase s := by
  intro hcase
  exact fiveFive_reduced_locus_empty hs hs1
    (reducedPoint_of_symmetricFiveFiveCase hs hcase)

end

end Cuboid2
