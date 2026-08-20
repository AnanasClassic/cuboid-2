import Cuboid2.QuadraticReduction.TransportCertificateData
import Cuboid2.QuadraticReduction.QuotientTransport

/-!
# Exact inverse of the reciprocal quotient transport

This file turns the generated `R5/E6` multiplication-back certificate into a
specialized inverse of the quartic map `E1 → C8`.  All rational-function
denominators are explicit.  The removable forward base point is intentionally
kept as a separate hypothesis; it is discharged by `TransportExceptions`.
-/

namespace Cuboid2

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Coefficient of `x` in the inverse penultimate subresultant. -/
def quotientInverseA (U V : ℚ) : ℚ :=
  quotientInverseACertificate U V

/-- Constant coefficient in the inverse penultimate subresultant. -/
def quotientInverseB (U V : ℚ) : ℚ :=
  quotientInverseBCertificate U V

/-- Recovered elliptic abscissa `x=-B/A`. -/
def quotientInverseX (U V : ℚ) : ℚ :=
  -quotientInverseB U V / quotientInverseA U V

/-- Coefficient of `y` in `f1-2U f3`. -/
def quotientInverseA1 (x U : ℚ) : ℚ :=
  (24 * x ^ 3 - 2186 * x ^ 2 + 4524 * x - 2982) -
    2 * U * (24 * x ^ 3 - 293 * x ^ 2 + 2857 * x - 3491)

/-- Constant coefficient in `f1-2U f3`. -/
def quotientInverseB1 (x U : ℚ) : ℚ :=
  (511 * x ^ 4 - 3430 * x ^ 3 - 3677 * x ^ 2 + 26438 * x - 22214) -
    2 * U * (583 * x ^ 4 - 715 * x ^ 3 - 3476 * x ^ 2 + 9529 * x - 7107)

/-- Coefficient of `y` in `f2-V f3`. -/
def quotientInverseA2 (x V : ℚ) : ℚ :=
  (24 * x ^ 3 - 1579 * x ^ 2 + 3636 * x - 2391) -
    V * (24 * x ^ 3 - 293 * x ^ 2 + 2857 * x - 3491)

/-- Constant coefficient in `f2-V f3`. -/
def quotientInverseB2 (x V : ℚ) : ℚ :=
  (535 * x ^ 4 - 3140 * x ^ 3 + 1380 * x ^ 2 + 9346 * x - 9307) -
    V * (583 * x ^ 4 - 715 * x ^ 3 - 3476 * x ^ 2 + 9529 * x - 7107)

/-- Recovered elliptic ordinate `y=-b1/a1`. -/
def quotientInverseY (U V : ℚ) : ℚ :=
  -quotientInverseB1 (quotientInverseX U V) U /
    quotientInverseA1 (quotientInverseX U V) U

/-- The degree-five projection factor from the first elimination. -/
def quotientInverseR5 (x U V : ℚ) : ℚ :=
  quotientInverseR5Certificate x U V

/-- The degree-six factor left after substituting the first linear equation. -/
def quotientInverseE6 (x U : ℚ) : ℚ :=
  quotientInverseE6Certificate x U 0

private theorem quotientInverseR5CertificateTerms_explicit :
    quotientInverseR5CertificateTerms = [
      (5, 1, 0, 4), (5, 0, 1, -3), (5, 0, 0, 1),
      (4, 1, 0, 4), (4, 0, 1, -1), (4, 0, 0, -4),
      (3, 1, 0, -64), (3, 0, 1, 34), (3, 0, 0, 24),
      (2, 1, 0, 88), (2, 0, 1, -11), (2, 0, 0, -72),
      (1, 1, 0, 8), (1, 0, 1, -95), (1, 0, 0, 87),
      (0, 1, 0, -44), (0, 0, 1, 80), (0, 0, 0, -36)
    ] := by
  native_decide

private theorem quotientInverseE6CertificateTerms_explicit :
    quotientInverseE6CertificateTerms = [
      (6, 2, 0, 4), (6, 1, 0, -4), (6, 0, 0, 1),
      (5, 2, 0, -12), (5, 1, 0, 36), (5, 0, 0, -24),
      (4, 1, 0, -88), (4, 0, 0, 83),
      (3, 2, 0, 20), (3, 1, 0, -20), (3, 0, 0, 4),
      (2, 1, 0, 388), (2, 0, 0, -388),
      (1, 2, 0, -12), (1, 1, 0, -568), (1, 0, 0, 580),
      (0, 2, 0, -4), (0, 1, 0, 264), (0, 0, 0, -260)
    ] := by
  native_decide

/-- Small expanded form of the generated degree-five factor. -/
theorem quotientInverseR5_explicit (x U V : ℚ) :
    quotientInverseR5 x U V =
      (4 * U - 3 * V + 1) * x ^ 5 +
      (4 * U - V - 4) * x ^ 4 +
      (-64 * U + 34 * V + 24) * x ^ 3 +
      (88 * U - 11 * V - 72) * x ^ 2 +
      (8 * U - 95 * V + 87) * x +
      (-44 * U + 80 * V - 36) := by
  unfold quotientInverseR5 quotientInverseR5Certificate
  rw [quotientInverseR5CertificateTerms_explicit]
  simp [transportEvalXUVTerms]
  ring

/-- Small expanded form of the generated degree-six factor. -/
theorem quotientInverseE6_explicit (x U : ℚ) :
    quotientInverseE6 x U =
      (4 * U ^ 2 - 4 * U + 1) * x ^ 6 +
      (-12 * U ^ 2 + 36 * U - 24) * x ^ 5 +
      (-88 * U + 83) * x ^ 4 +
      (20 * U ^ 2 - 20 * U + 4) * x ^ 3 +
      (388 * U - 388) * x ^ 2 +
      (-12 * U ^ 2 - 568 * U + 580) * x +
      (-4 * U ^ 2 + 264 * U - 260) := by
  unfold quotientInverseE6 quotientInverseE6Certificate
  rw [quotientInverseE6CertificateTerms_explicit]
  simp [transportEvalXUVTerms]
  ring

private theorem quotientInverseE6Certificate_eval (x U V : ℚ) :
    transportEvalXUVTerms quotientInverseE6CertificateTerms x U V =
      quotientInverseE6 x U := by
  rw [quotientInverseE6_explicit,
    quotientInverseE6CertificateTerms_explicit]
  simp [transportEvalXUVTerms]
  ring

/--
The first elimination determinant factors through the small degree-five
polynomial `R5`.
-/
theorem quotientInverse_projection_identity (x U V : ℚ) :
    quotientInverseA1 x U * quotientInverseB2 x V -
        quotientInverseA2 x V * quotientInverseB1 x U =
      (x - 2) * (576 * x - 352225) * quotientInverseR5 x U V := by
  rw [quotientInverseR5_explicit]
  simp [quotientInverseA1, quotientInverseB1,
    quotientInverseA2, quotientInverseB2]
  ring

/--
The numerator obtained by eliminating `y` from the curve equation factors
through the small degree-six polynomial `E6`.
-/
theorem quotientInverse_elliptic_substitution_identity (x U : ℚ) :
    quotientInverseB1 x U ^ 2 -
        quotientInverseA1 x U ^ 2 * (x ^ 3 - 5 * x + 4) =
      -(576 * x - 352225) * (x ^ 2 - 5) * quotientInverseE6 x U := by
  rw [quotientInverseE6_explicit]
  simp [quotientInverseA1, quotientInverseB1]
  ring

/-- Sparse homogeneous evaluation `A^5 R5(-B/A)`. -/
def quotientInverseR5Homogeneous (U V : ℚ) : ℚ :=
  transportEvalUVTerms
    (transportSubstituteLinearXTerms 5 quotientInverseR5CertificateTerms
      quotientInverseACertificateTerms quotientInverseBCertificateTerms) U V

/-- Sparse homogeneous evaluation `A^6 E6(-B/A)`. -/
def quotientInverseE6Homogeneous (U V : ℚ) : ℚ :=
  transportEvalUVTerms
    (transportSubstituteLinearXTerms 6 quotientInverseE6CertificateTerms
      quotientInverseACertificateTerms quotientInverseBCertificateTerms) U V

private theorem quotientInverseR5_x_degree :
    ∀ term ∈ quotientInverseR5CertificateTerms, term.1 ≤ 5 := by
  native_decide

private theorem quotientInverseE6_x_degree :
    ∀ term ∈ quotientInverseE6CertificateTerms, term.1 ≤ 6 := by
  native_decide

/-- Clearing `A` in the displayed rational evaluation of `R5`. -/
theorem quotientInverseR5_homogeneous
    {U V : ℚ} (hA : quotientInverseA U V ≠ 0) :
    quotientInverseA U V ^ 5 *
        quotientInverseR5 (quotientInverseX U V) U V =
      quotientInverseR5Homogeneous U V := by
  unfold quotientInverseX quotientInverseR5 quotientInverseR5Homogeneous
  symm
  exact transportEvalSubstituteLinearXTerms 5
    quotientInverseR5CertificateTerms quotientInverseACertificateTerms
    quotientInverseBCertificateTerms U V quotientInverseR5_x_degree hA

/-- Clearing `A` in the displayed rational evaluation of `E6`. -/
theorem quotientInverseE6_homogeneous
    {U V : ℚ} (hA : quotientInverseA U V ≠ 0) :
    quotientInverseA U V ^ 6 *
        quotientInverseE6 (quotientInverseX U V) U =
      quotientInverseE6Homogeneous U V := by
  have hsub := transportEvalSubstituteLinearXTerms 6
    quotientInverseE6CertificateTerms quotientInverseACertificateTerms
    quotientInverseBCertificateTerms U V quotientInverseE6_x_degree hA
  rw [quotientInverseE6Certificate_eval] at hsub
  unfold quotientInverseX quotientInverseE6Homogeneous
  unfold quotientInverseA quotientInverseB
  exact hsub.symm

private theorem quotientInverseR5_sparse_back :
    transportSubstituteLinearXTerms 5 quotientInverseR5CertificateTerms
        quotientInverseACertificateTerms quotientInverseBCertificateTerms =
      quotientInverseR5BackCertificateTerms := by
  native_decide

private theorem quotientInverseE6_sparse_back :
    transportSubstituteLinearXTerms 6 quotientInverseE6CertificateTerms
        quotientInverseACertificateTerms quotientInverseBCertificateTerms =
      quotientInverseE6BackCertificateTerms := by
  native_decide

/--
Exact multiplication-back of the degree-five factor.  The generated quotient
has 1005 terms; `ring` checks every integer coefficient.
-/
theorem quotientInverseR5_back_certificate (U V : ℚ) :
    quotientInverseR5Homogeneous U V =
      transportEvalUVTerms quotientInverseR5BackCertificateTerms U V := by
  exact congrArg (fun terms => transportEvalUVTerms terms U V)
    quotientInverseR5_sparse_back

/--
Exact multiplication-back of the degree-six factor.  The generated quotient
has 1485 terms; `ring` checks every integer coefficient.
-/
theorem quotientInverseE6_back_certificate (U V : ℚ) :
    quotientInverseE6Homogeneous U V =
      transportEvalUVTerms quotientInverseE6BackCertificateTerms U V := by
  exact congrArg (fun terms => transportEvalUVTerms terms U V)
    quotientInverseE6_sparse_back

private def reciprocalQuotientC8CertificateTerms : List TransportUVTerm :=
  transportParseUVTerms
    "6,0,16;5,1,-128;4,3,44;4,2,272;4,1,32;4,0,64;3,4,-76;3,3,-256;3,2,-180;3,1,-128;3,0,-32;2,6,-1;2,5,32;2,4,134;2,3,228;2,2,87;2,1,148;2,0,-44;1,5,-34;1,4,-80;1,3,-60;1,2,-164;1,1,94;1,0,-12;0,4,31;0,3,48;0,2,-46;0,1,12;0,0,-1"

private theorem reciprocalQuotientC8CertificateTerms_explicit :
    reciprocalQuotientC8CertificateTerms = [
      (6, 0, 16), (5, 1, -128),
      (4, 3, 44), (4, 2, 272), (4, 1, 32), (4, 0, 64),
      (3, 4, -76), (3, 3, -256), (3, 2, -180), (3, 1, -128),
      (3, 0, -32),
      (2, 6, -1), (2, 5, 32), (2, 4, 134), (2, 3, 228),
      (2, 2, 87), (2, 1, 148), (2, 0, -44),
      (1, 5, -34), (1, 4, -80), (1, 3, -60), (1, 2, -164),
      (1, 1, 94), (1, 0, -12),
      (0, 4, 31), (0, 3, 48), (0, 2, -46), (0, 1, 12),
      (0, 0, -1)
    ] := by
  native_decide

private theorem quotientInverseR5_sparse_division :
    quotientInverseR5BackCertificateTerms =
      transportMulUVTerms quotientInverseR5BackQuotientTerms
        reciprocalQuotientC8CertificateTerms := by
  native_decide

private theorem quotientInverseE6_sparse_division :
    quotientInverseE6BackCertificateTerms =
      transportMulUVTerms quotientInverseE6BackQuotientTerms
        reciprocalQuotientC8CertificateTerms := by
  native_decide

private theorem reciprocalQuotientC8_sparse_eval (U V : ℚ) :
    transportEvalUVTerms reciprocalQuotientC8CertificateTerms U V =
      reciprocalQuotientC8 U V := by
  rw [reciprocalQuotientC8CertificateTerms_explicit]
  simp [transportEvalUVTerms, transportEvalUVTerm, reciprocalQuotientC8]
  ring

theorem quotientInverseR5_back_divisible (U V : ℚ) :
    transportEvalUVTerms quotientInverseR5BackCertificateTerms U V =
      quotientInverseR5BackQuotient U V * reciprocalQuotientC8 U V := by
  have h := congrArg (fun terms => transportEvalUVTerms terms U V)
    quotientInverseR5_sparse_division
  rw [transportEvalMulUVTerms, reciprocalQuotientC8_sparse_eval] at h
  exact h

theorem quotientInverseE6_back_divisible (U V : ℚ) :
    transportEvalUVTerms quotientInverseE6BackCertificateTerms U V =
      quotientInverseE6BackQuotient U V * reciprocalQuotientC8 U V := by
  have h := congrArg (fun terms => transportEvalUVTerms terms U V)
    quotientInverseE6_sparse_division
  rw [transportEvalMulUVTerms, reciprocalQuotientC8_sparse_eval] at h
  exact h

/-- `C8=0` makes the recovered abscissa a root of `R5`. -/
theorem quotientInverseR5_zero
    {U V : ℚ} (hC8 : reciprocalQuotientC8 U V = 0)
    (hA : quotientInverseA U V ≠ 0) :
    quotientInverseR5 (quotientInverseX U V) U V = 0 := by
  have hback := quotientInverseR5_back_certificate U V
  have hdiv := quotientInverseR5_back_divisible U V
  rw [hC8, mul_zero] at hdiv
  rw [hdiv] at hback
  have hhom := quotientInverseR5_homogeneous hA
  rw [hback] at hhom
  exact (mul_eq_zero.mp hhom).resolve_left (pow_ne_zero 5 hA)

/-- `C8=0` makes the recovered abscissa a root of `E6`. -/
theorem quotientInverseE6_zero
    {U V : ℚ} (hC8 : reciprocalQuotientC8 U V = 0)
    (hA : quotientInverseA U V ≠ 0) :
    quotientInverseE6 (quotientInverseX U V) U = 0 := by
  have hback := quotientInverseE6_back_certificate U V
  have hdiv := quotientInverseE6_back_divisible U V
  rw [hC8, mul_zero] at hdiv
  rw [hdiv] at hback
  have hhom := quotientInverseE6_homogeneous hA
  rw [hback] at hhom
  exact (mul_eq_zero.mp hhom).resolve_left (pow_ne_zero 6 hA)

/-- The recovered ordinate satisfies the first cleared forward equation. -/
theorem quotientInverse_first_equation
    {U V : ℚ} (ha1 :
      quotientInverseA1 (quotientInverseX U V) U ≠ 0) :
    quotientForwardF1 (quotientInverseX U V) (quotientInverseY U V) -
        2 * U *
          quotientForwardF3 (quotientInverseX U V) (quotientInverseY U V) = 0 := by
  unfold quotientInverseY
  have hlinear :
      quotientForwardF1 (quotientInverseX U V)
          (-quotientInverseB1 (quotientInverseX U V) U /
            quotientInverseA1 (quotientInverseX U V) U) -
        2 * U * quotientForwardF3 (quotientInverseX U V)
          (-quotientInverseB1 (quotientInverseX U V) U /
            quotientInverseA1 (quotientInverseX U V) U) =
        quotientInverseA1 (quotientInverseX U V) U *
            (-quotientInverseB1 (quotientInverseX U V) U /
              quotientInverseA1 (quotientInverseX U V) U) +
          quotientInverseB1 (quotientInverseX U V) U := by
    simp [quotientForwardF1, quotientForwardF3,
      quotientInverseA1, quotientInverseB1]
    ring
  rw [hlinear]
  field_simp [ha1]
  ring

/-- The recovered ordinate satisfies the second cleared forward equation. -/
theorem quotientInverse_second_equation
    {U V : ℚ} (hC8 : reciprocalQuotientC8 U V = 0)
    (hA : quotientInverseA U V ≠ 0)
    (ha1 : quotientInverseA1 (quotientInverseX U V) U ≠ 0) :
    quotientForwardF2 (quotientInverseX U V) (quotientInverseY U V) -
        V * quotientForwardF3
          (quotientInverseX U V) (quotientInverseY U V) = 0 := by
  have hR5 := quotientInverseR5_zero hC8 hA
  have hdet := quotientInverse_projection_identity
    (quotientInverseX U V) U V
  rw [hR5, mul_zero] at hdet
  have hpair :
      quotientForwardF2 (quotientInverseX U V) (quotientInverseY U V) -
          V * quotientForwardF3
            (quotientInverseX U V) (quotientInverseY U V) =
        quotientInverseA2 (quotientInverseX U V) V *
            quotientInverseY U V +
          quotientInverseB2 (quotientInverseX U V) V := by
    simp [quotientForwardF2, quotientForwardF3,
      quotientInverseA2, quotientInverseB2]
    ring
  rw [hpair]
  unfold quotientInverseY
  field_simp [ha1]
  linarith [hdet]

/-- The recovered pair lies on `E1`. -/
theorem quotientInverse_on_E1
    {U V : ℚ} (hC8 : reciprocalQuotientC8 U V = 0)
    (hA : quotientInverseA U V ≠ 0)
    (ha1 : quotientInverseA1 (quotientInverseX U V) U ≠ 0) :
    e1Residual (quotientInverseX U V) (quotientInverseY U V) = 0 := by
  have hE6 := quotientInverseE6_zero hC8 hA
  have hfactor := quotientInverse_elliptic_substitution_identity
    (quotientInverseX U V) U
  rw [hE6, mul_zero] at hfactor
  unfold quotientInverseY e1Residual
  field_simp [ha1]
  nlinarith [hfactor]

/--
Regular inverse of the affine quartic transport.

The `hF3` hypothesis is necessary: the removable `-4P` forward base has
`A≠0` and `a1≠0`, but the displayed affine forward coordinates are undefined.
-/
theorem reciprocalQuotientC8_to_E1_regular
    {U V : ℚ} (hC8 : reciprocalQuotientC8 U V = 0)
    (hA : quotientInverseA U V ≠ 0)
    (ha1 : quotientInverseA1 (quotientInverseX U V) U ≠ 0)
    (hF3 : quotientForwardF3
      (quotientInverseX U V) (quotientInverseY U V) ≠ 0) :
    ∃ P : E1AffinePoint,
      quotientForwardU P.X P.Y = U ∧ quotientForwardV P.X P.Y = V := by
  let P : E1AffinePoint := {
    X := quotientInverseX U V
    Y := quotientInverseY U V
    onCurve := quotientInverse_on_E1 hC8 hA ha1
  }
  refine ⟨P, ?_, ?_⟩
  · have hfirst := quotientInverse_first_equation (U := U) (V := V) ha1
    change quotientForwardU
      (quotientInverseX U V) (quotientInverseY U V) = U
    unfold quotientForwardU
    field_simp [hF3]
    linarith
  · have hsecond := quotientInverse_second_equation hC8 hA ha1
    change quotientForwardV
      (quotientInverseX U V) (quotientInverseY U V) = V
    unfold quotientForwardV
    field_simp [hF3]
    linarith

end

end Cuboid2
