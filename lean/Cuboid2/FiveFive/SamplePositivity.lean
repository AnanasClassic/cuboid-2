import Cuboid2.FiveFive.ResultantPolynomial

/-!
# Exact positivity certificates for two `5+5` sample fibres

The pinned replay checks that the fibre polynomial has no real roots at seven
rational sample parameters.  For the first two samples we can avoid a Sturm
sequence entirely: after a harmless positive rescaling of `y`, the explicit
resultant factor is a sparse diagonally-dominant sum of squares.

Every identity below is checked by `ring`; strict positivity then follows from
positive rational coefficients and the positive constant square.
-/

namespace Cuboid2

noncomputable section

/-- Exact sum-of-squares certificate at `s=1/100`, after `y=30x`. -/
theorem fiveFive_sample_one_hundredth_sos (x : ℚ) :
    fiveFiveResultantFactor (1 / 100 : ℚ) (30 * x) =
      43046721 * (x ^ 8) ^ 2 +
      (143245138581 / 625 : ℚ) * (x ^ 7) ^ 2 +
      (1639111679904123 / 3125000 : ℚ) * (x ^ 6) ^ 2 +
      (2629653055807025151 / 3906250000 : ℚ) * (x ^ 5) ^ 2 +
      (20687483113105268944161 / 39062500000000 : ℚ) * (x ^ 4) ^ 2 +
      (127664963923184098716861 / 488281250000000 : ℚ) * (x ^ 3) ^ 2 +
      (1932064699358681368971921 / 24414062500000000 : ℚ) * (x ^ 2) ^ 2 +
      (16405015817010529416123 / 1220703125000000 : ℚ) * x ^ 2 +
      (599089638663728299493 / 610351562500000 : ℚ) +
      (1062882 / 3125 : ℚ) * (x ^ 6 - x ^ 5) ^ 2 +
      (5305375503 / 7812500 : ℚ) * (x ^ 5 - x ^ 4) ^ 2 +
      (1531373706387 / 4882812500 : ℚ) * (x ^ 4 - x ^ 3) ^ 2 +
      (7783077006211293 / 48828125000000 : ℚ) * (x ^ 3 + x ^ 2) ^ 2 +
      (4994426797760151 / 30517578125000 : ℚ) * (x ^ 2 + x) ^ 2 +
      (104264608376367027 / 3051757812500000 : ℚ) * (x + 1) ^ 2 := by
  unfold fiveFiveResultantFactor
  ring

/-- The first sample fibre is strictly positive on all rational `y`. -/
theorem fiveFive_sample_one_hundredth_pos (y : ℚ) :
    0 < fiveFiveResultantFactor (1 / 100 : ℚ) y := by
  let x : ℚ := y / 30
  have hy : y = 30 * x := by
    dsimp [x]
    ring
  rw [hy, fiveFive_sample_one_hundredth_sos]
  positivity

/-- Exact sum-of-squares certificate at `s=1/5`, after `y=3x`. -/
theorem fiveFive_sample_one_fifth_sos (x : ℚ) :
    fiveFiveResultantFactor (1 / 5 : ℚ) (3 * x) =
      (43046721 / 390625 : ℚ) * (x ^ 8) ^ 2 +
      (5471716536 / 1953125 : ℚ) * (x ^ 7) ^ 2 +
      (287231105916 / 9765625 : ℚ) * (x ^ 6) ^ 2 +
      (8116579350216 / 48828125 : ℚ) * (x ^ 5) ^ 2 +
      (134531012713446 / 244140625 : ℚ) * (x ^ 4) ^ 2 +
      (6566057536125681 / 6103515625 : ℚ) * (x ^ 3) ^ 2 +
      (7588093118962419 / 6103515625 : ℚ) * (x ^ 2) ^ 2 +
      (4486528025229519 / 6103515625 : ℚ) * x ^ 2 +
      (931702108697106 / 6103515625 : ℚ) +
      (34012224 / 390625 : ℚ) * (x ^ 6 - x ^ 5) ^ 2 +
      (1621249344 / 1953125 : ℚ) * (x ^ 5 - x ^ 4) ^ 2 +
      (19307465856 / 9765625 : ℚ) * (x ^ 4 - x ^ 3) ^ 2 +
      (110581593984 / 48828125 : ℚ) * (x ^ 3 + x ^ 2) ^ 2 +
      (76067452398519 / 6103515625 : ℚ) * (x ^ 3 + 1) ^ 2 +
      (4829421641481 / 6103515625 : ℚ) * (x ^ 2 + x) ^ 2 +
      (111540775104 / 9765625 : ℚ) * (x + 1) ^ 2 := by
  unfold fiveFiveResultantFactor
  ring

/-- The second sample fibre is strictly positive on all rational `y`. -/
theorem fiveFive_sample_one_fifth_pos (y : ℚ) :
    0 < fiveFiveResultantFactor (1 / 5 : ℚ) y := by
  let x : ℚ := y / 3
  have hy : y = 3 * x := by
    dsimp [x]
    ring
  rw [hy, fiveFive_sample_one_fifth_sos]
  positivity

/-- Neither of the first two sample fibres contains a rational root. -/
theorem fiveFive_first_two_sample_fibres_nonzero :
    (∀ y : ℚ, fiveFiveResultantFactor (1 / 100 : ℚ) y ≠ 0) ∧
      ∀ y : ℚ, fiveFiveResultantFactor (1 / 5 : ℚ) y ≠ 0 := by
  constructor
  · intro y
    exact ne_of_gt (fiveFive_sample_one_hundredth_pos y)
  · intro y
    exact ne_of_gt (fiveFive_sample_one_fifth_pos y)

end

end Cuboid2
