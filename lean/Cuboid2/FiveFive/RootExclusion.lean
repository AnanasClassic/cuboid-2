import Cuboid2.FiveFive.Resultant

/-!
# Final real-root exclusion for the symmetric `5+5` case

All multivariate algebra is completed before the one remaining theorem below.
The gap now asks only for the exact univariate real-algebra statement checked
by the published seven-obligation Sturm certificate: for positive rational
`s ≠ 1`, the explicit Sylvester resultant has no rational zero in `y`.
-/

namespace Cuboid2

noncomputable section

/--
The remaining `5+5` certificate theorem.  Its final implementation will check
explicit Sturm/positivity data in Lean rather than trust the generating
Python script.
-/
theorem fiveFive_resultant_ne_zero
    {s : ℚ} (hs : 0 < s) (hs1 : s ≠ 1) (y : ℚ) :
    fiveFiveResultant s y ≠ 0 := by
  sorry

/-- The normalized two-equation locus is empty once its resultant is nonzero. -/
theorem fiveFive_reduced_locus_empty
    {s : ℚ} (hs : 0 < s) (hs1 : s ≠ 1) :
    ¬ Nonempty (FiveFiveReducedPoint s) := by
  rintro ⟨P⟩
  exact fiveFive_resultant_ne_zero hs hs1 P.y (P.resultant_eq_zero hs)

/-- The original symmetric factorization is impossible once the reduced locus is empty. -/
theorem symmetric_five_five_impossible_from_reduced
    {s : ℚ} (hs : 0 < s) (hs1 : s ≠ 1) :
    ¬ SymmetricFiveFiveCase s := by
  intro hcase
  exact fiveFive_reduced_locus_empty hs hs1
    (reducedPoint_of_symmetricFiveFiveCase hs hcase)

end

end Cuboid2
