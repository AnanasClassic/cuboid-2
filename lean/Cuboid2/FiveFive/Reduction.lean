import Cuboid2.FiveFive.Basic

/-!
# Normalized two-equation reduction for the symmetric `5+5` case

Starting from the five coefficient equations, set

`r = e / s^2`, `a = r y`, `d = r^4 z`.

For positive `s`, the constant equation gives `r^2=s` and `e=r^5`.  Eliminating
`b,c` leaves the two exact equations `G₂(s,y,z)=G₃(s,y,z)=0` used by the
pinned real-root certificate.
-/

namespace Cuboid2

open Polynomial

noncomputable section

namespace FiveFiveCoefficientSolution

/-- The signed square root determined by the constant coefficient. -/
def r {s : ℚ} (S : FiveFiveCoefficientSolution s) : ℚ :=
  S.e / s ^ 2

/-- Normalized fourth-degree coefficient. -/
def y {s : ℚ} (S : FiveFiveCoefficientSolution s) : ℚ :=
  S.a / S.r

/-- Normalized linear coefficient. -/
def z {s : ℚ} (S : FiveFiveCoefficientSolution s) : ℚ :=
  S.d / S.r ^ 4

/-- The constant equation gives `r²=s`. -/
theorem r_sq {s : ℚ} (S : FiveFiveCoefficientSolution s) (hs : 0 < s) :
    S.r ^ 2 = s := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  unfold r
  calc
    (S.e / s ^ 2) ^ 2 = S.e ^ 2 / s ^ 4 := by
      field_simp [hs0]
    _ = s ^ 5 / s ^ 4 := by rw [S.constant]
    _ = s := by
      field_simp [hs0]

/-- In particular the signed root is nonzero. -/
theorem r_ne_zero {s : ℚ} (S : FiveFiveCoefficientSolution s) (hs : 0 < s) :
    S.r ≠ 0 := by
  intro hr
  have hsq := S.r_sq hs
  rw [hr, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
  linarith

/-- The same constant equation gives the exact sign-sensitive identity `e=r⁵`. -/
theorem e_eq_r_pow_five
    {s : ℚ} (S : FiveFiveCoefficientSolution s) (hs : 0 < s) :
    S.e = S.r ^ 5 := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hpow : S.e ^ 5 = S.e * s ^ 10 := by
    calc
      S.e ^ 5 = S.e * (S.e ^ 2) ^ 2 := by ring
      _ = S.e * (s ^ 5) ^ 2 := by rw [S.constant]
      _ = S.e * s ^ 10 := by ring
  symm
  unfold r
  calc
    (S.e / s ^ 2) ^ 5 = S.e ^ 5 / s ^ 10 := by
      field_simp [hs0]
    _ = (S.e * s ^ 10) / s ^ 10 := by rw [hpow]
    _ = S.e := by field_simp [hs0]

/-- Solve the `X^8` equation for `b`. -/
theorem b_formula {s : ℚ} (S : FiveFiveCoefficientSolution s) :
    S.b = (S.a ^ 2 + fiveFiveCoeff8 s) / 2 := by
  nlinarith [S.coeff8]

/-- Solve the `X^2` equation for `c`, after the constant normalization. -/
theorem c_formula
    {s : ℚ} (S : FiveFiveCoefficientSolution s) (hs : 0 < s) :
    S.c = (S.d ^ 2 - fiveFiveCoeff2 s) / (2 * S.r ^ 5) := by
  have hr0 : S.r ≠ 0 := S.r_ne_zero hs
  have he : S.e = S.r ^ 5 := S.e_eq_r_pow_five hs
  have hden : (2 : ℚ) * S.r ^ 5 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 5 hr0)
  apply (eq_div_iff hden).2
  rw [← he]
  nlinarith [S.coeff2]

/-- Recover `a=r y`. -/
theorem a_eq_r_mul_y
    {s : ℚ} (S : FiveFiveCoefficientSolution s) (hs : 0 < s) :
    S.a = S.r * S.y := by
  have hr0 : S.r ≠ 0 := S.r_ne_zero hs
  unfold y
  field_simp [hr0]

/-- Recover `d=r⁴ z`. -/
theorem d_eq_r_pow_four_mul_z
    {s : ℚ} (S : FiveFiveCoefficientSolution s) (hs : 0 < s) :
    S.d = S.r ^ 4 * S.z := by
  have hr0 : S.r ≠ 0 := S.r_ne_zero hs
  unfold z
  field_simp [hr0]

end FiveFiveCoefficientSolution

/-- First cleared equation after eliminating `b,c`. -/
def fiveFiveE2 (r a d : ℚ) : ℚ :=
  a ^ 4 * r ^ 5 - 4 * a ^ 2 * r ^ 9 - 2 * a ^ 2 * r ^ 7 +
    12 * a ^ 2 * r ^ 5 - 4 * a * d ^ 2 - 24 * a * r ^ 10 +
    4 * a * r ^ 8 + 8 * a * r ^ 6 + 8 * d * r ^ 5 +
    60 * r ^ 11 - 39 * r ^ 9 - 52 * r ^ 7 + 32 * r ^ 5

/-- Second cleared equation after eliminating `b,c`. -/
def fiveFiveE3 (r a d : ℚ) : ℚ :=
  4 * a ^ 2 * d * r ^ 10 - 8 * a * r ^ 15 - d ^ 4 -
    12 * d ^ 2 * r ^ 10 + 2 * d ^ 2 * r ^ 8 + 4 * d ^ 2 * r ^ 6 -
    8 * d * r ^ 14 - 4 * d * r ^ 12 + 24 * d * r ^ 10 -
    32 * r ^ 20 + 52 * r ^ 18 + 39 * r ^ 16 - 60 * r ^ 14

/-- First normalized equation from the published `5+5` certificate. -/
def fiveFiveG2 (s y z : ℚ) : ℚ :=
  -4 * s ^ 3 * y ^ 2 - 24 * s ^ 3 * y + 60 * s ^ 3 +
    s ^ 2 * y ^ 4 - 2 * s ^ 2 * y ^ 2 - 4 * s ^ 2 * y * z ^ 2 +
    4 * s ^ 2 * y + 8 * s ^ 2 * z - 39 * s ^ 2 +
    12 * s * y ^ 2 + 8 * s * y - 52 * s + 32

/-- Second normalized equation from the published `5+5` certificate. -/
def fiveFiveG3 (s y z : ℚ) : ℚ :=
  -32 * s ^ 3 - 12 * s ^ 2 * z ^ 2 - 8 * s ^ 2 * z + 52 * s ^ 2 +
    4 * s * y ^ 2 * z - 8 * s * y - s * z ^ 4 + 2 * s * z ^ 2 -
    4 * s * z + 39 * s + 4 * z ^ 2 + 24 * z - 60

/-- The residual `X^6` equation is exactly `E₂=0`. -/
theorem FiveFiveCoefficientSolution.e2_zero
    {s : ℚ} (S : FiveFiveCoefficientSolution s) (hs : 0 < s) :
    fiveFiveE2 S.r S.a S.d = 0 := by
  have hr0 : S.r ≠ 0 := S.r_ne_zero hs
  have hsrel : s = S.r ^ 2 := (S.r_sq hs).symm
  have hb := S.b_formula
  have hc := S.c_formula hs
  unfold fiveFiveCoeff8 at hb
  unfold fiveFiveCoeff2 at hc
  have hres :
      S.b ^ 2 + 2 * S.d - 2 * S.a * S.c - fiveFiveCoeff6 s = 0 := by
    nlinarith [S.coeff6]
  calc
    fiveFiveE2 S.r S.a S.d =
        4 * S.r ^ 5 *
          (S.b ^ 2 + 2 * S.d - 2 * S.a * S.c - fiveFiveCoeff6 s) := by
      unfold fiveFiveE2 fiveFiveCoeff6
      rw [hb, hc]
      simp only [hsrel]
      field_simp [hr0]
      ring
    _ = 0 := by rw [hres]; ring

/-- The residual `X^4` equation is exactly `E₃=0`. -/
theorem FiveFiveCoefficientSolution.e3_zero
    {s : ℚ} (S : FiveFiveCoefficientSolution s) (hs : 0 < s) :
    fiveFiveE3 S.r S.a S.d = 0 := by
  have hr0 : S.r ≠ 0 := S.r_ne_zero hs
  have hsrel : s = S.r ^ 2 := (S.r_sq hs).symm
  have hb := S.b_formula
  have hc := S.c_formula hs
  have he := S.e_eq_r_pow_five hs
  unfold fiveFiveCoeff8 at hb
  unfold fiveFiveCoeff2 at hc
  have hres :
      2 * S.b * S.d - S.c ^ 2 - 2 * S.a * S.e - fiveFiveCoeff4 s = 0 := by
    nlinarith [S.coeff4]
  calc
    fiveFiveE3 S.r S.a S.d =
        4 * S.r ^ 10 *
          (2 * S.b * S.d - S.c ^ 2 - 2 * S.a * S.e - fiveFiveCoeff4 s) := by
      unfold fiveFiveE3 fiveFiveCoeff4
      rw [hb, hc, he]
      simp only [hsrel]
      field_simp [hr0]
      ring
    _ = 0 := by rw [hres]; ring

/-- A rational point on the normalized two-equation `5+5` locus. -/
structure FiveFiveReducedPoint (s : ℚ) where
  y : ℚ
  z : ℚ
  g2 : fiveFiveG2 s y z = 0
  g3 : fiveFiveG3 s y z = 0

/-- The first normalized equation follows from `E₂=r⁵G₂`. -/
theorem FiveFiveCoefficientSolution.g2_zero
    {s : ℚ} (S : FiveFiveCoefficientSolution s) (hs : 0 < s) :
    fiveFiveG2 s S.y S.z = 0 := by
  have hr0 : S.r ≠ 0 := S.r_ne_zero hs
  have hsrel : s = S.r ^ 2 := (S.r_sq hs).symm
  have ha := S.a_eq_r_mul_y hs
  have hd := S.d_eq_r_pow_four_mul_z hs
  have hid :
      fiveFiveE2 S.r S.a S.d = S.r ^ 5 * fiveFiveG2 s S.y S.z := by
    rw [ha, hd]
    simp only [hsrel]
    unfold fiveFiveE2 fiveFiveG2
    ring
  have hmul : S.r ^ 5 * fiveFiveG2 s S.y S.z = 0 := by
    rw [← hid, S.e2_zero hs]
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 5 hr0)

/-- The second normalized equation follows from `E₃=r¹⁴G₃`. -/
theorem FiveFiveCoefficientSolution.g3_zero
    {s : ℚ} (S : FiveFiveCoefficientSolution s) (hs : 0 < s) :
    fiveFiveG3 s S.y S.z = 0 := by
  have hr0 : S.r ≠ 0 := S.r_ne_zero hs
  have hsrel : s = S.r ^ 2 := (S.r_sq hs).symm
  have ha := S.a_eq_r_mul_y hs
  have hd := S.d_eq_r_pow_four_mul_z hs
  have hid :
      fiveFiveE3 S.r S.a S.d = S.r ^ 14 * fiveFiveG3 s S.y S.z := by
    rw [ha, hd]
    simp only [hsrel]
    unfold fiveFiveE3 fiveFiveG3
    ring
  have hmul : S.r ^ 14 * fiveFiveG3 s S.y S.z = 0 := by
    rw [← hid, S.e3_zero hs]
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 14 hr0)

/-- Convert a coefficient solution into the normalized two-equation point. -/
def FiveFiveCoefficientSolution.toReducedPoint
    {s : ℚ} (S : FiveFiveCoefficientSolution s) (hs : 0 < s) :
    FiveFiveReducedPoint s where
  y := S.y
  z := S.z
  g2 := S.g2_zero hs
  g3 := S.g3_zero hs

/-- Every admissible symmetric factorization reaches the normalized locus. -/
theorem reducedPoint_of_symmetricFiveFiveCase
    {s : ℚ} (hs : 0 < s) (hcase : SymmetricFiveFiveCase s) :
    Nonempty (FiveFiveReducedPoint s) := by
  rcases coefficientSolution_of_symmetricFiveFiveCase hcase with ⟨S⟩
  exact ⟨S.toReducedPoint hs⟩

/-- Exact reciprocal exchange of the two normalized equations. -/
theorem fiveFiveG2_reciprocal
    {s : ℚ} (hs0 : s ≠ 0) (y z : ℚ) :
    s ^ 3 * fiveFiveG2 s⁻¹ z y = -fiveFiveG3 s y z := by
  unfold fiveFiveG2 fiveFiveG3
  field_simp [hs0]
  ring

/-- The reciprocal identity in the opposite direction. -/
theorem fiveFiveG3_reciprocal
    {s : ℚ} (hs0 : s ≠ 0) (y z : ℚ) :
    s ^ 3 * fiveFiveG3 s⁻¹ z y = -fiveFiveG2 s y z := by
  unfold fiveFiveG2 fiveFiveG3
  field_simp [hs0]
  ring

/-- A normalized point at `s` transports to one at `1/s`, exchanging `y,z`. -/
def FiveFiveReducedPoint.reciprocal
    {s : ℚ} (P : FiveFiveReducedPoint s) (hs0 : s ≠ 0) :
    FiveFiveReducedPoint s⁻¹ where
  y := P.z
  z := P.y
  g2 := by
    have h := fiveFiveG2_reciprocal hs0 P.y P.z
    rw [P.g3, neg_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 3 hs0)
  g3 := by
    have h := fiveFiveG3_reciprocal hs0 P.y P.z
    rw [P.g2, neg_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 3 hs0)

end

end Cuboid2
