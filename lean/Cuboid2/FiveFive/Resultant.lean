import Cuboid2.FiveFive.Reduction
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Resultant of the normalized `5+5` equations

For fixed `s,y`, regard `G₂,G₃` as polynomials in `z`.  Mathlib defines their
resultant as the determinant of the Sylvester matrix.  A rational common root
therefore forces this resultant to vanish; no external CAS result is used for
that implication.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- `G₂(s,y,z)` as a quadratic polynomial in `z`. -/
def fiveFiveG2Poly (s y : ℚ) : ℚ[X] :=
  C (-4 * s ^ 2 * y) * X ^ 2 + C (8 * s ^ 2) * X +
    C (-4 * s ^ 3 * y ^ 2 - 24 * s ^ 3 * y + 60 * s ^ 3 +
      s ^ 2 * y ^ 4 - 2 * s ^ 2 * y ^ 2 + 4 * s ^ 2 * y - 39 * s ^ 2 +
      12 * s * y ^ 2 + 8 * s * y - 52 * s + 32)

/-- `G₃(s,y,z)` as a quartic polynomial in `z`. -/
def fiveFiveG3Poly (s y : ℚ) : ℚ[X] :=
  C (-s) * X ^ 4 +
    C (-12 * s ^ 2 + 2 * s + 4) * X ^ 2 +
      C (-8 * s ^ 2 + 4 * s * y ^ 2 - 4 * s + 24) * X +
        C (-32 * s ^ 3 + 52 * s ^ 2 - 8 * s * y + 39 * s - 60)

@[simp] theorem eval_fiveFiveG2Poly (s y z : ℚ) :
    eval z (fiveFiveG2Poly s y) = fiveFiveG2 s y z := by
  simp [fiveFiveG2Poly, fiveFiveG2]
  ring

@[simp] theorem eval_fiveFiveG3Poly (s y z : ℚ) :
    eval z (fiveFiveG3Poly s y) = fiveFiveG3 s y z := by
  simp [fiveFiveG3Poly, fiveFiveG3]
  ring

/-- The exact scalar resultant whose real-root certificate remains to be checked. -/
def fiveFiveResultant (s y : ℚ) : ℚ :=
  resultant (fiveFiveG2Poly s y) (fiveFiveG3Poly s y)

/-- The quartic polynomial is nonzero whenever `s≠0`. -/
theorem fiveFiveG3Poly_ne_zero {s y : ℚ} (hs0 : s ≠ 0) :
    fiveFiveG3Poly s y ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun F : ℚ[X] => F.coeff 4) hzero
  simp [fiveFiveG3Poly] at hcoeff
  exact hs0 (neg_eq_zero.mp hcoeff)

/-- A common rational root of `G₂,G₃` forces the Sylvester resultant to vanish. -/
theorem fiveFiveResultant_eq_zero_of_common_root
    {s y z : ℚ} (hs0 : s ≠ 0)
    (hg2 : fiveFiveG2 s y z = 0)
    (hg3 : fiveFiveG3 s y z = 0) :
    fiveFiveResultant s y = 0 := by
  unfold fiveFiveResultant
  rw [Polynomial.resultant_eq_zero_iff]
  constructor
  · exact Or.inr (fiveFiveG3Poly_ne_zero hs0)
  · intro hcoprime
    rcases hcoprime with ⟨A, B, hbezout⟩
    have heval := congrArg (Polynomial.eval z) hbezout
    simp [eval_add, eval_mul, hg2, hg3] at heval

/-- Every normalized `5+5` point lies above a zero of the scalar resultant. -/
theorem FiveFiveReducedPoint.resultant_eq_zero
    {s : ℚ} (P : FiveFiveReducedPoint s) (hs : 0 < s) :
    fiveFiveResultant s P.y = 0 := by
  exact fiveFiveResultant_eq_zero_of_common_root
    (ne_of_gt hs) P.g2 P.g3

end

end Cuboid2
