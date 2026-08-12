import Cuboid2.FiveFive.DiscriminantRoots

/-!
# Final real-root exclusion for the symmetric `5+5` case

All multivariate algebra is completed before the one remaining theorem below.
The exact Bézout identity reduces a hypothetical normalized `5+5` point to a
zero of the explicit 104-term scalar polynomial.

`DiscriminantRoots.lean` now checks, inside Lean, that both discriminant
factors used by the pinned interval decomposition have no rational roots.
The remaining gap is the real root-count/constancy certificate on the
resulting intervals, not the external CAS `ground_roots()` call.
-/

namespace Cuboid2

noncomputable section

/--
The remaining `5+5` certificate theorem.  Its final implementation must check
the pinned Sturm/positivity interval data in Lean rather than trust the
generating Python script.
-/
theorem fiveFiveResultantFactor_ne_zero
    {s : ℚ} (hs : 0 < s) (hs1 : s ≠ 1) (y : ℚ) :
    fiveFiveResultantFactor s y ≠ 0 := by
  sorry

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
