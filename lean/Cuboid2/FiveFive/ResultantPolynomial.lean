import Cuboid2.FiveFive.ResultantCertificate

/-!
# The `5+5` resultant as an explicit polynomial in `y`

The Bézout certificate stores the scalar resultant as a bivariate expression.
Sturm and Bernstein checkers are substantially easier to state against an
actual `Polynomial ℚ`, so this file groups the same 104 terms by powers of
`y` and proves the multiplication-back evaluation identity.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- The explicit degree-sixteen polynomial `y ↦ fiveFiveResultantFactor s y`. -/
def fiveFiveResultantFactorPoly (s : ℚ) : ℚ[X] :=
  C (s ^ 8) * X ^ 16 +
  C (-8 * s ^ 7 * (s + 2) * (2 * s - 3)) * X ^ 14 +
  C (4 * s ^ 6 *
      (24 * s ^ 4 + 84 * s ^ 3 - 177 * s ^ 2 - 124 * s + 248)) * X ^ 12 +
  C (-384 * s ^ 8) * X ^ 11 +
  C (-8 * s ^ 5 *
      (32 * s ^ 6 + 424 * s ^ 5 - 158 * s ^ 4 - 1729 * s ^ 3 +
        1306 * s ^ 2 + 1480 * s - 1440)) * X ^ 10 +
  C (1152 * s ^ 7 * (s + 2) * (2 * s - 3)) * X ^ 9 +
  C (2 * s ^ 4 *
      (128 * s ^ 8 + 6528 * s ^ 7 + 16848 * s ^ 6 - 48536 * s ^ 5 -
        28653 * s ^ 4 + 113864 * s ^ 3 - 26096 * s ^ 2 -
        72576 * s + 41088)) * X ^ 8 +
  C (-256 * s ^ 6 *
      (16 * s ^ 4 - 44 * s ^ 3 - 53 * s ^ 2 + 4 * s + 112)) * X ^ 7 +
  C (-8 * s ^ 3 *
      (2176 * s ^ 9 + 27968 * s ^ 8 - 12752 * s ^ 7 -
        138602 * s ^ 6 + 114839 * s ^ 5 + 176318 * s ^ 4 -
        231952 * s ^ 3 - 20032 * s ^ 2 + 125056 * s - 46080)) * X ^ 6 +
  C (256 * s ^ 5 *
      (16 * s ^ 6 - 624 * s ^ 5 - 522 * s ^ 4 + 2181 * s ^ 3 -
        162 * s ^ 2 - 1552 * s + 528)) * X ^ 5 +
  C (4 * s ^ 2 *
      (102784 * s ^ 10 + 364928 * s ^ 9 - 1217688 * s ^ 8 -
        498852 * s ^ 7 + 3024575 * s ^ 6 - 788884 * s ^ 5 -
        2840952 * s ^ 4 + 1915008 * s ^ 3 + 672128 * s ^ 2 -
        976896 * s + 253952)) * X ^ 4 +
  C (128 * s ^ 4 *
      (960 * s ^ 7 + 18336 * s ^ 6 - 31528 * s ^ 5 - 23015 * s ^ 4 +
        55672 * s ^ 3 - 5024 * s ^ 2 - 25664 * s + 9728)) * X ^ 3 +
  C (-8 * s *
      (489600 * s ^ 11 - 269664 * s ^ 10 - 2905432 * s ^ 9 +
        3068422 * s ^ 8 + 4199609 * s ^ 7 - 6851026 * s ^ 6 -
        756536 * s ^ 5 + 5456864 * s ^ 4 - 2037632 * s ^ 3 -
        1215488 * s ^ 2 + 1007616 * s - 196608)) * X ^ 2 +
  C (-128 * s ^ 3 *
      (23520 * s ^ 8 - 96 * s ^ 7 - 113874 * s ^ 6 + 72339 * s ^ 5 +
        132598 * s ^ 4 - 136096 * s ^ 3 - 23584 * s ^ 2 +
        64000 * s - 18432)) * X +
  C (12960000 * s ^ 12 - 30931200 * s ^ 11 - 16244128 * s ^ 10 +
    96898160 * s ^ 9 - 41403359 * s ^ 8 - 100331856 * s ^ 7 +
    93598176 * s ^ 6 + 26662144 * s ^ 5 - 61456128 * s ^ 4 +
    14524416 * s ^ 3 + 11501568 * s ^ 2 - 6815744 * s + 1048576)

/-- Grouping the 104 terms by `y` changes no mathematical content. -/
@[simp] theorem eval_fiveFiveResultantFactorPoly (s y : ℚ) :
    eval y (fiveFiveResultantFactorPoly s) =
      fiveFiveResultantFactor s y := by
  simp [fiveFiveResultantFactorPoly, fiveFiveResultantFactor]
  ring

/-- The coefficient controlling the two ends of the real line is `s^8`. -/
@[simp] theorem fiveFiveResultantFactorPoly_coeff_sixteen (s : ℚ) :
    (fiveFiveResultantFactorPoly s).coeff 16 = s ^ 8 := by
  simp [fiveFiveResultantFactorPoly]

/-- For nonzero `s` the explicit polynomial in `y` is nonzero. -/
theorem fiveFiveResultantFactorPoly_ne_zero
    {s : ℚ} (hs : s ≠ 0) :
    fiveFiveResultantFactorPoly s ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun P : ℚ[X] => P.coeff 16) hzero
  simp only [fiveFiveResultantFactorPoly_coeff_sixteen, coeff_zero] at hcoeff
  exact (pow_ne_zero 8 hs) hcoeff

/-- Any scalar zero is exactly a polynomial root in `y`. -/
theorem fiveFiveResultantFactor_eq_zero_iff_isRoot (s y : ℚ) :
    fiveFiveResultantFactor s y = 0 ↔
      IsRoot (fiveFiveResultantFactorPoly s) y := by
  simp [IsRoot]

end

end Cuboid2
