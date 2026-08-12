import Cuboid2.QuadraticReduction.ProjectionCertificateNegative
import Cuboid2.QuadraticReduction.CharacterDescent

/-!
# Reciprocal quotient and elliptic transport

This file checks the characteristic-zero identities in
`research/compact_signed_square/reciprocal_quotient/reciprocal_quotient.json`
and `research/arithmetic_geometry/low_degree_transport.json`.

The two physical signs use the same reciprocal quotient curve.  In the
negative branch its natural coordinates occur in the opposite order.  The
formulas below keep that swap explicit.
-/

namespace Cuboid2

noncomputable section

/-- The 29-term reciprocal quotient `C8(U,V)`. -/
def reciprocalQuotientC8 (U V : ℚ) : ℚ :=
  16 * U ^ 6 -
    128 * U ^ 5 * V +
    44 * U ^ 4 * V ^ 3 +
    272 * U ^ 4 * V ^ 2 +
    32 * U ^ 4 * V +
    64 * U ^ 4 -
    76 * U ^ 3 * V ^ 4 -
    256 * U ^ 3 * V ^ 3 -
    180 * U ^ 3 * V ^ 2 -
    128 * U ^ 3 * V -
    32 * U ^ 3 -
    U ^ 2 * V ^ 6 +
    32 * U ^ 2 * V ^ 5 +
    134 * U ^ 2 * V ^ 4 +
    228 * U ^ 2 * V ^ 3 +
    87 * U ^ 2 * V ^ 2 +
    148 * U ^ 2 * V -
    44 * U ^ 2 -
    34 * U * V ^ 5 -
    80 * U * V ^ 4 -
    60 * U * V ^ 3 -
    164 * U * V ^ 2 +
    94 * U * V -
    12 * U +
    31 * V ^ 4 +
    48 * V ^ 3 -
    46 * V ^ 2 +
    12 * V -
    1

/-- The positive compact projection clears to `C8(U,V)`. -/
theorem compactProjectionPositive_to_reciprocalQuotientC8
    {S K : ℚ} (hSp : S + 1 ≠ 0) (hKm : K - 1 ≠ 0) (hKp : K + 1 ≠ 0) :
    256 * compactProjectionPositive S K =
      (S + 1) ^ 8 * (K - 1) ^ 6 * (K + 1) ^ 4 *
        reciprocalQuotientC8 (reciprocalU S K) (reciprocalV S K) := by
  unfold reciprocalU reciprocalV reciprocalQuotientC8
  field_simp [hSp, hKm, hKp]
  simp [compactProjectionPositive]
  ring

/-- A positive compact point reaches the affine reciprocal quotient. -/
theorem reciprocalQuotientC8_of_compactProjectionPositive
    {S K : ℚ} (hSp : S + 1 ≠ 0) (hKm : K - 1 ≠ 0) (hKp : K + 1 ≠ 0)
    (hQ : compactProjectionPositive S K = 0) :
    reciprocalQuotientC8 (reciprocalU S K) (reciprocalV S K) = 0 := by
  have hidentity :=
    compactProjectionPositive_to_reciprocalQuotientC8 hSp hKm hKp
  rw [hQ] at hidentity
  have hproduct :
      (S + 1) ^ 8 * (K - 1) ^ 6 * (K + 1) ^ 4 *
          reciprocalQuotientC8 (reciprocalU S K) (reciprocalV S K) = 0 := by
    simpa only [mul_zero] using hidentity.symm
  have hfactor :
      (S + 1) ^ 8 * (K - 1) ^ 6 * (K + 1) ^ 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 8 hSp) (pow_ne_zero 6 hKm))
      (pow_ne_zero 4 hKp)
  exact (mul_eq_zero.mp hproduct).resolve_left hfactor

/--
The negative compact projection reaches the same quotient after swapping
the two fixed-field coordinates.
-/
theorem compactProjectionNegative_to_reciprocalQuotientC8
    {S K : ℚ} (hSp : S + 1 ≠ 0) (hKm : K - 1 ≠ 0) (hKp : K + 1 ≠ 0) :
    256 * compactProjectionNegative S K =
      -(S + 1) ^ 8 * (K + 1) ^ 6 * (K - 1) ^ 4 *
        reciprocalQuotientC8 (reciprocalV S K) (reciprocalU S K) := by
  unfold reciprocalU reciprocalV reciprocalQuotientC8
  field_simp [hSp, hKm, hKp]
  simp [compactProjectionNegative, compactProjectionPositive]
  ring

/-- A negative compact point reaches `C8` in swapped coordinates. -/
theorem reciprocalQuotientC8_of_compactProjectionNegative
    {S K : ℚ} (hSp : S + 1 ≠ 0) (hKm : K - 1 ≠ 0) (hKp : K + 1 ≠ 0)
    (hQ : compactProjectionNegative S K = 0) :
    reciprocalQuotientC8 (reciprocalV S K) (reciprocalU S K) = 0 := by
  have hidentity :=
    compactProjectionNegative_to_reciprocalQuotientC8 hSp hKm hKp
  rw [hQ] at hidentity
  have hproduct :
      -(S + 1) ^ 8 * (K + 1) ^ 6 * (K - 1) ^ 4 *
          reciprocalQuotientC8 (reciprocalV S K) (reciprocalU S K) = 0 := by
    simpa only [mul_zero] using hidentity.symm
  have hfactor :
      -(S + 1) ^ 8 * (K + 1) ^ 6 * (K - 1) ^ 4 ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 8 hSp)) (pow_ne_zero 6 hKp))
      (pow_ne_zero 4 hKm)
  exact (mul_eq_zero.mp hproduct).resolve_left hfactor

/--
The denominator-cleared form of
`C8(A/(2D),B/D)`.  The factor `64` is `2^6`, the largest power of two
introduced by the first quotient coordinate.
-/
def reciprocalQuotientC8Homogeneous (A B D : ℚ) : ℚ :=
  16 * A ^ 6 * B ^ 0 * D ^ 2 -
    256 * A ^ 5 * B ^ 1 * D ^ 2 +
    176 * A ^ 4 * B ^ 3 * D ^ 1 +
    1088 * A ^ 4 * B ^ 2 * D ^ 2 +
    128 * A ^ 4 * B ^ 1 * D ^ 3 +
    256 * A ^ 4 * B ^ 0 * D ^ 4 -
    608 * A ^ 3 * B ^ 4 * D ^ 1 -
    2048 * A ^ 3 * B ^ 3 * D ^ 2 -
    1440 * A ^ 3 * B ^ 2 * D ^ 3 -
    1024 * A ^ 3 * B ^ 1 * D ^ 4 -
    256 * A ^ 3 * B ^ 0 * D ^ 5 -
    16 * A ^ 2 * B ^ 6 * D ^ 0 +
    512 * A ^ 2 * B ^ 5 * D ^ 1 +
    2144 * A ^ 2 * B ^ 4 * D ^ 2 +
    3648 * A ^ 2 * B ^ 3 * D ^ 3 +
    1392 * A ^ 2 * B ^ 2 * D ^ 4 +
    2368 * A ^ 2 * B ^ 1 * D ^ 5 -
    704 * A ^ 2 * B ^ 0 * D ^ 6 -
    1088 * A ^ 1 * B ^ 5 * D ^ 2 -
    2560 * A ^ 1 * B ^ 4 * D ^ 3 -
    1920 * A ^ 1 * B ^ 3 * D ^ 4 -
    5248 * A ^ 1 * B ^ 2 * D ^ 5 +
    3008 * A ^ 1 * B ^ 1 * D ^ 6 -
    384 * A ^ 1 * B ^ 0 * D ^ 7 +
    1984 * A ^ 0 * B ^ 4 * D ^ 4 +
    3072 * A ^ 0 * B ^ 3 * D ^ 5 -
    2944 * A ^ 0 * B ^ 2 * D ^ 6 +
    768 * A ^ 0 * B ^ 1 * D ^ 7 -
    64 * A ^ 0 * B ^ 0 * D ^ 8

/-- Exact denominator clearing for the elliptic forward map. -/
theorem reciprocalQuotientC8_homogeneous
    {A B D : ℚ} (hD : D ≠ 0) :
    64 * D ^ 8 * reciprocalQuotientC8 (A / (2 * D)) (B / D) =
      reciprocalQuotientC8Homogeneous A B D := by
  unfold reciprocalQuotientC8 reciprocalQuotientC8Homogeneous
  field_simp [hD]
  ring

/-- First quartic numerator in the exact map `E1 → C8`. -/
def quotientForwardF1 (x y : ℚ) : ℚ :=
  511 * x ^ 4 +
    24 * x ^ 3 * y -
    3430 * x ^ 3 -
    2186 * x ^ 2 * y -
    3677 * x ^ 2 +
    4524 * x * y +
    26438 * x -
    2982 * y -
    22214

/-- Second quartic numerator in the exact map `E1 → C8`. -/
def quotientForwardF2 (x y : ℚ) : ℚ :=
  535 * x ^ 4 +
    24 * x ^ 3 * y -
    3140 * x ^ 3 -
    1579 * x ^ 2 * y +
    1380 * x ^ 2 +
    3636 * x * y +
    9346 * x -
    2391 * y -
    9307

/-- Common quartic denominator in the exact map `E1 → C8`. -/
def quotientForwardF3 (x y : ℚ) : ℚ :=
  583 * x ^ 4 +
    24 * x ^ 3 * y -
    715 * x ^ 3 -
    293 * x ^ 2 * y -
    3476 * x ^ 2 +
    2857 * x * y +
    9529 * x -
    3491 * y -
    7107

/-- First coordinate of the exact affine map `E1 → C8`. -/
def quotientForwardU (x y : ℚ) : ℚ :=
  quotientForwardF1 x y / (2 * quotientForwardF3 x y)

/-- Second coordinate of the exact affine map `E1 → C8`. -/
def quotientForwardV (x y : ℚ) : ℚ :=
  quotientForwardF2 x y / quotientForwardF3 x y

/--
A pair `a+b·y` in the quadratic algebra with
`y²=x³-5x+4`.  Keeping the two coefficients explicit gives a compact
kernel-checkable certificate for the large forward identity.
-/
def quadraticPairMul (x : ℚ) (P Q : ℚ × ℚ) : ℚ × ℚ :=
  (P.1 * Q.1 + (x ^ 3 - 5 * x + 4) * P.2 * Q.2,
    P.1 * Q.2 + P.2 * Q.1)

/-- Powers in the explicit quadratic algebra. -/
def quadraticPairPow (x : ℚ) (P : ℚ × ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => quadraticPairMul x (quadraticPairPow x P n) P

/-- Scalar multiplication of an explicit quadratic-algebra pair. -/
def quadraticPairScale (c : ℚ) (P : ℚ × ℚ) : ℚ × ℚ :=
  (c * P.1, c * P.2)

/-- Evaluation of a pair `a+b·y`. -/
def quadraticPairEval (P : ℚ × ℚ) (y : ℚ) : ℚ := P.1 + P.2 * y

private theorem quadraticPairEval_mul
    {x y : ℚ} (hE : y ^ 2 = x ^ 3 - 5 * x + 4) (P Q : ℚ × ℚ) :
    quadraticPairEval (quadraticPairMul x P Q) y =
      quadraticPairEval P y * quadraticPairEval Q y := by
  simp only [quadraticPairEval, quadraticPairMul]
  rw [← hE]
  ring

private theorem quadraticPairEval_pow
    {x y : ℚ} (hE : y ^ 2 = x ^ 3 - 5 * x + 4) (P : ℚ × ℚ) (n : ℕ) :
    quadraticPairEval (quadraticPairPow x P n) y = quadraticPairEval P y ^ n := by
  induction n with
  | zero => simp [quadraticPairPow, quadraticPairEval]
  | succ n ih =>
      rw [quadraticPairPow, quadraticPairEval_mul hE, ih, pow_succ]

private theorem quadraticPairEval_scale (c : ℚ) (P : ℚ × ℚ) (y : ℚ) :
    quadraticPairEval (quadraticPairScale c P) y = c * quadraticPairEval P y := by
  simp [quadraticPairEval, quadraticPairScale]
  ring

private theorem quadraticPairEval_add (P Q : ℚ × ℚ) (y : ℚ) :
    quadraticPairEval (P + Q) y = quadraticPairEval P y + quadraticPairEval Q y := by
  simp [quadraticPairEval]
  ring

/-- One homogeneous monomial in the pair certificate. -/
def quadraticPairTerm
    (x c : ℚ) (a b d : ℕ) (A B D : ℚ × ℚ) : ℚ × ℚ :=
  quadraticPairScale c
    (quadraticPairMul x (quadraticPairPow x A a)
      (quadraticPairMul x (quadraticPairPow x B b) (quadraticPairPow x D d)))

private theorem quadraticPairEval_term
    {x y : ℚ} (hE : y ^ 2 = x ^ 3 - 5 * x + 4)
    (c : ℚ) (a b d : ℕ) (A B D : ℚ × ℚ) :
    quadraticPairEval (quadraticPairTerm x c a b d A B D) y =
      c * quadraticPairEval A y ^ a * quadraticPairEval B y ^ b *
        quadraticPairEval D y ^ d := by
  rw [quadraticPairTerm, quadraticPairEval_scale,
    quadraticPairEval_mul hE, quadraticPairEval_pow hE,
    quadraticPairEval_mul hE, quadraticPairEval_pow hE,
    quadraticPairEval_pow hE]
  ring

/-- The 29 homogeneous `C8` terms evaluated in the quadratic algebra. -/
def reciprocalQuotientC8HomogeneousPair
    (x : ℚ) (A B D : ℚ × ℚ) : ℚ × ℚ :=
  quadraticPairTerm x 16 6 0 2 A B D +
    quadraticPairTerm x (-256) 5 1 2 A B D +
    quadraticPairTerm x 176 4 3 1 A B D +
    quadraticPairTerm x 1088 4 2 2 A B D +
    quadraticPairTerm x 128 4 1 3 A B D +
    quadraticPairTerm x 256 4 0 4 A B D +
    quadraticPairTerm x (-608) 3 4 1 A B D +
    quadraticPairTerm x (-2048) 3 3 2 A B D +
    quadraticPairTerm x (-1440) 3 2 3 A B D +
    quadraticPairTerm x (-1024) 3 1 4 A B D +
    quadraticPairTerm x (-256) 3 0 5 A B D +
    quadraticPairTerm x (-16) 2 6 0 A B D +
    quadraticPairTerm x 512 2 5 1 A B D +
    quadraticPairTerm x 2144 2 4 2 A B D +
    quadraticPairTerm x 3648 2 3 3 A B D +
    quadraticPairTerm x 1392 2 2 4 A B D +
    quadraticPairTerm x 2368 2 1 5 A B D +
    quadraticPairTerm x (-704) 2 0 6 A B D +
    quadraticPairTerm x (-1088) 1 5 2 A B D +
    quadraticPairTerm x (-2560) 1 4 3 A B D +
    quadraticPairTerm x (-1920) 1 3 4 A B D +
    quadraticPairTerm x (-5248) 1 2 5 A B D +
    quadraticPairTerm x 3008 1 1 6 A B D +
    quadraticPairTerm x (-384) 1 0 7 A B D +
    quadraticPairTerm x 1984 0 4 4 A B D +
    quadraticPairTerm x 3072 0 3 5 A B D +
    quadraticPairTerm x (-2944) 0 2 6 A B D +
    quadraticPairTerm x 768 0 1 7 A B D +
    quadraticPairTerm x (-64) 0 0 8 A B D

/-- Pair representation of `f1`. -/
def quotientForwardF1Pair (x : ℚ) : ℚ × ℚ :=
  (511 * x ^ 4 - 3430 * x ^ 3 - 3677 * x ^ 2 + 26438 * x - 22214,
    24 * x ^ 3 - 2186 * x ^ 2 + 4524 * x - 2982)

/-- Pair representation of `f2`. -/
def quotientForwardF2Pair (x : ℚ) : ℚ × ℚ :=
  (535 * x ^ 4 - 3140 * x ^ 3 + 1380 * x ^ 2 + 9346 * x - 9307,
    24 * x ^ 3 - 1579 * x ^ 2 + 3636 * x - 2391)

/-- Pair representation of `f3`. -/
def quotientForwardF3Pair (x : ℚ) : ℚ × ℚ :=
  (583 * x ^ 4 - 715 * x ^ 3 - 3476 * x ^ 2 + 9529 * x - 7107,
    24 * x ^ 3 - 293 * x ^ 2 + 2857 * x - 3491)

private theorem quotientForwardF1Pair_eval (x y : ℚ) :
    quadraticPairEval (quotientForwardF1Pair x) y = quotientForwardF1 x y := by
  simp [quadraticPairEval, quotientForwardF1Pair, quotientForwardF1]
  ring

private theorem quotientForwardF2Pair_eval (x y : ℚ) :
    quadraticPairEval (quotientForwardF2Pair x) y = quotientForwardF2 x y := by
  simp [quadraticPairEval, quotientForwardF2Pair, quotientForwardF2]
  ring

private theorem quotientForwardF3Pair_eval (x y : ℚ) :
    quadraticPairEval (quotientForwardF3Pair x) y = quotientForwardF3 x y := by
  simp [quadraticPairEval, quotientForwardF3Pair, quotientForwardF3]
  ring

set_option maxHeartbeats 2000000 in
/--
The compact two-component certificate for the forward map.  Its expansion is
the remainder of the cleared `C8` equation modulo
`y²-(x³-5x+4)`, and both components vanish identically.
-/
theorem quotientForward_pair_certificate (x : ℚ) :
    reciprocalQuotientC8HomogeneousPair x
      (quotientForwardF1Pair x) (quotientForwardF2Pair x)
      (quotientForwardF3Pair x) = (0, 0) := by
  apply Prod.ext <;>
    norm_num [reciprocalQuotientC8HomogeneousPair, quadraticPairTerm,
      quadraticPairScale, quadraticPairPow, quadraticPairMul,
      quotientForwardF1Pair, quotientForwardF2Pair, quotientForwardF3Pair] <;>
    ring

private theorem reciprocalQuotientC8HomogeneousPair_eval
    {x y : ℚ} (hE : y ^ 2 = x ^ 3 - 5 * x + 4) (A B D : ℚ × ℚ) :
    quadraticPairEval (reciprocalQuotientC8HomogeneousPair x A B D) y =
      reciprocalQuotientC8Homogeneous
        (quadraticPairEval A y) (quadraticPairEval B y) (quadraticPairEval D y) := by
  simp only [reciprocalQuotientC8HomogeneousPair, quadraticPairEval_add,
    quadraticPairEval_term hE, reciprocalQuotientC8Homogeneous]
  ring

/-- The cleared forward-map equation vanishes at every affine `E1` point. -/
theorem quotientForward_homogeneous_zero (P : E1AffinePoint) :
    reciprocalQuotientC8Homogeneous
      (quotientForwardF1 P.X P.Y) (quotientForwardF2 P.X P.Y)
      (quotientForwardF3 P.X P.Y) = 0 := by
  have hcurve := P.onCurve
  unfold e1Residual at hcurve
  have hE : P.Y ^ 2 = P.X ^ 3 - 5 * P.X + 4 := by
    linarith [hcurve]
  have hpair := congrArg (fun Q => quadraticPairEval Q P.Y)
    (quotientForward_pair_certificate P.X)
  rw [reciprocalQuotientC8HomogeneousPair_eval hE,
    quotientForwardF1Pair_eval, quotientForwardF2Pair_eval,
    quotientForwardF3Pair_eval] at hpair
  simpa [quadraticPairEval] using hpair

/-- The exact quartic rational map sends an affine `E1` point to `C8`. -/
theorem quotientForward_on_reciprocalQuotientC8
    (P : E1AffinePoint) (hF3 : quotientForwardF3 P.X P.Y ≠ 0) :
    reciprocalQuotientC8 (quotientForwardU P.X P.Y) (quotientForwardV P.X P.Y) = 0 := by
  have hclear := quotientForward_homogeneous_zero P
  have hhom := reciprocalQuotientC8_homogeneous
    (A := quotientForwardF1 P.X P.Y)
    (B := quotientForwardF2 P.X P.Y)
    (D := quotientForwardF3 P.X P.Y) hF3
  rw [hclear] at hhom
  have hproduct :
      64 * quotientForwardF3 P.X P.Y ^ 8 *
          reciprocalQuotientC8
            (quotientForwardF1 P.X P.Y / (2 * quotientForwardF3 P.X P.Y))
            (quotientForwardF2 P.X P.Y / quotientForwardF3 P.X P.Y) = 0 := by
    simpa only using hhom
  have hfactor : 64 * quotientForwardF3 P.X P.Y ^ 8 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 8 hF3)
  have hc8 := (mul_eq_zero.mp hproduct).resolve_left hfactor
  simpa [quotientForwardU, quotientForwardV] using hc8

/-- The two-torsion translation used by the common-character formulas. -/
def e1TransportTranslateX (X : ℚ) : ℚ := (X - 3) / (X - 1)

/-- The `Y`-coordinate of the two-torsion translation. -/
def e1TransportTranslateY (X Y : ℚ) : ℚ := 2 * Y / (X - 1) ^ 2

/-- The displayed translation preserves the affine `E1` equation. -/
theorem e1TransportTranslate_residual
    {X Y : ℚ} (hX1 : X ≠ 1) :
    e1Residual (e1TransportTranslateX X) (e1TransportTranslateY X Y) =
      4 * e1Residual X Y / (X - 1) ^ 4 := by
  unfold e1TransportTranslateX e1TransportTranslateY e1Residual
  field_simp [sub_ne_zero.mpr hX1]
  ring

/-- Translation of the first quartic numerator, in cleared form. -/
theorem quotientForwardF1_translate
    {X Y : ℚ} (hX1 : X ≠ 1) :
    (X - 1) ^ 5 *
        quotientForwardF1 (e1TransportTranslateX X) (e1TransportTranslateY X Y) =
      -4 * e1UNumerator X Y := by
  unfold e1TransportTranslateX e1TransportTranslateY quotientForwardF1
  unfold e1UNumerator
  field_simp [sub_ne_zero.mpr hX1]
  ring

/-- Translation of the second quartic numerator, in cleared form. -/
theorem quotientForwardF2_translate
    {X Y : ℚ} (hX1 : X ≠ 1) :
    (X - 1) ^ 5 *
        quotientForwardF2 (e1TransportTranslateX X) (e1TransportTranslateY X Y) =
      -2 * e1VNumerator X Y := by
  unfold e1TransportTranslateX e1TransportTranslateY quotientForwardF2
  unfold e1VNumerator
  field_simp [sub_ne_zero.mpr hX1]
  ring

/-- Translation of the common quartic denominator, in cleared form. -/
theorem quotientForwardF3_translate
    {X Y : ℚ} (hX1 : X ≠ 1) :
    (X - 1) ^ 5 *
        quotientForwardF3 (e1TransportTranslateX X) (e1TransportTranslateY X Y) =
      -2 * e1D0 X Y := by
  unfold e1TransportTranslateX e1TransportTranslateY quotientForwardF3
  unfold e1D0
  field_simp [sub_ne_zero.mpr hX1]
  ring

/-- The translated forward denominator is nonzero exactly where `e1D0` is. -/
theorem quotientForwardF3_translate_ne_zero
    {X Y : ℚ} (hX1 : X ≠ 1) (hD0 : e1D0 X Y ≠ 0) :
    quotientForwardF3 (e1TransportTranslateX X) (e1TransportTranslateY X Y) ≠ 0 := by
  intro hzero
  have htranslate := quotientForwardF3_translate (X := X) (Y := Y) hX1
  rw [hzero, mul_zero] at htranslate
  apply hD0
  linarith

/--
After the two-torsion translation, the quartic forward map is exactly the
existing common-character coordinate `e1U`.
-/
theorem quotientForwardU_translate
    {X Y : ℚ} (hX1 : X ≠ 1) (hD0 : e1D0 X Y ≠ 0) :
    quotientForwardU (e1TransportTranslateX X) (e1TransportTranslateY X Y) =
      e1U X Y := by
  have hF3 := quotientForwardF3_translate_ne_zero hX1 hD0
  have hF1 := quotientForwardF1_translate (X := X) (Y := Y) hX1
  have hF3clear := quotientForwardF3_translate (X := X) (Y := Y) hX1
  have ht : (X - 1) ^ 5 ≠ 0 := pow_ne_zero 5 (sub_ne_zero.mpr hX1)
  unfold quotientForwardU e1U
  field_simp [hF3, hD0]
  apply mul_left_cancel₀ ht
  calc
    (X - 1) ^ 5 *
          (quotientForwardF1 (e1TransportTranslateX X) (e1TransportTranslateY X Y) *
            e1D0 X Y) =
        ((X - 1) ^ 5 *
          quotientForwardF1 (e1TransportTranslateX X) (e1TransportTranslateY X Y)) *
            e1D0 X Y := by ring
    _ = (-4 * e1UNumerator X Y) * e1D0 X Y := by rw [hF1]
    _ = 2 * e1UNumerator X Y * (-2 * e1D0 X Y) := by ring
    _ = 2 * e1UNumerator X Y *
          ((X - 1) ^ 5 *
            quotientForwardF3
              (e1TransportTranslateX X) (e1TransportTranslateY X Y)) := by
      rw [hF3clear]
    _ = (X - 1) ^ 5 *
          (2 * quotientForwardF3
            (e1TransportTranslateX X) (e1TransportTranslateY X Y) *
              e1UNumerator X Y) := by ring

/--
After the same translation, the second quartic coordinate is exactly
`e1V`.
-/
theorem quotientForwardV_translate
    {X Y : ℚ} (hX1 : X ≠ 1) (hD0 : e1D0 X Y ≠ 0) :
    quotientForwardV (e1TransportTranslateX X) (e1TransportTranslateY X Y) =
      e1V X Y := by
  have hF3 := quotientForwardF3_translate_ne_zero hX1 hD0
  have hF2 := quotientForwardF2_translate (X := X) (Y := Y) hX1
  have hF3clear := quotientForwardF3_translate (X := X) (Y := Y) hX1
  have ht : (X - 1) ^ 5 ≠ 0 := pow_ne_zero 5 (sub_ne_zero.mpr hX1)
  unfold quotientForwardV e1V
  field_simp [hF3, hD0]
  apply mul_left_cancel₀ ht
  calc
    (X - 1) ^ 5 *
          (quotientForwardF2 (e1TransportTranslateX X) (e1TransportTranslateY X Y) *
            e1D0 X Y) =
        ((X - 1) ^ 5 *
          quotientForwardF2 (e1TransportTranslateX X) (e1TransportTranslateY X Y)) *
            e1D0 X Y := by ring
    _ = (-2 * e1VNumerator X Y) * e1D0 X Y := by rw [hF2]
    _ = e1VNumerator X Y * (-2 * e1D0 X Y) := by ring
    _ = e1VNumerator X Y *
          ((X - 1) ^ 5 *
            quotientForwardF3
              (e1TransportTranslateX X) (e1TransportTranslateY X Y)) := by
      rw [hF3clear]
    _ = (X - 1) ^ 5 *
          (quotientForwardF3
            (e1TransportTranslateX X) (e1TransportTranslateY X Y) *
              e1VNumerator X Y) := by ring

/-- The common-character coordinates in `CharacterDescent` lie on `C8`. -/
theorem e1_on_reciprocalQuotientC8
    (P : E1AffinePoint) (hX1 : P.X ≠ 1) (hD0 : e1D0 P.X P.Y ≠ 0) :
    reciprocalQuotientC8 (e1U P.X P.Y) (e1V P.X P.Y) = 0 := by
  let Q : E1AffinePoint := {
    X := e1TransportTranslateX P.X
    Y := e1TransportTranslateY P.X P.Y
    onCurve := by
      rw [e1TransportTranslate_residual hX1, P.onCurve]
      norm_num
  }
  have hF3 : quotientForwardF3 Q.X Q.Y ≠ 0 := by
    exact quotientForwardF3_translate_ne_zero hX1 hD0
  have hC8 := quotientForward_on_reciprocalQuotientC8 Q hF3
  change reciprocalQuotientC8
    (quotientForwardU (e1TransportTranslateX P.X) (e1TransportTranslateY P.X P.Y))
    (quotientForwardV (e1TransportTranslateX P.X) (e1TransportTranslateY P.X P.Y)) = 0
    at hC8
  rw [quotientForwardU_translate hX1 hD0,
    quotientForwardV_translate hX1 hD0] at hC8
  exact hC8

/--
The exact quotient equation and the exact common-character identity hold
simultaneously on the fully explicit open set.
-/
theorem e1_quotient_and_common_character
    (P : E1AffinePoint) (hX1 : P.X ≠ 1) (hD0 : e1D0 P.X P.Y ≠ 0)
    (hX3 : P.X ≠ 3) :
    reciprocalQuotientC8 (e1U P.X P.Y) (e1V P.X P.Y) = 0 ∧
      1 - e1U P.X P.Y * e1V P.X P.Y =
        2 * e1F P.X P.Y * e1G P.X P.Y ^ 2 :=
  ⟨e1_on_reciprocalQuotientC8 P hX1 hD0,
    e1_common_character P hD0 hX3⟩

end

end Cuboid2
