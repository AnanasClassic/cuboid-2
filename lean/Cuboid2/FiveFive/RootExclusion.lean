import Cuboid2.FiveFive.SamplePositivity40
import Cuboid2.FiveFive.DiscriminantP6Roots
import Cuboid2.FiveFive.DiscriminantP28Local

/-!
# Final real-root exclusion for the symmetric `5+5` case

All multivariate algebra is completed before the one remaining theorem below.
The exact Bézout identity reduces a hypothetical normalized `5+5` point to a
root of an explicit degree-sixteen polynomial in `y`.

The current Lean source checks both discriminant factors for rational roots,
all ten rational bracket-endpoint signs, the placement of all seven sample
parameters, and strict sum-of-squares positivity for every sample fibre.  The
degree-six discriminant factor is completely isolated over `ℝ` by exact
Bernstein sign and derivative certificates.  For the degree-twenty-eight
factor, the rightmost isolating bracket now has an exact Lean proof of strict
monotonicity as well.  The remaining gap is the other two P28 brackets plus
root-count constancy between the five discriminant cuts.
-/

namespace Cuboid2

noncomputable section

/--
The remaining `5+5` certificate theorem. Its final implementation must check
the pinned interval-continuation data in Lean rather than trust the generating
Python script.
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
