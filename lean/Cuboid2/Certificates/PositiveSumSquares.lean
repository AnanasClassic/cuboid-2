import Mathlib

/-!
# Kernel-checked positive sum-of-squares certificates

External algebra systems may search for a decomposition, but the only proof
premise retained here is an exact polynomial identity.  Lean then checks that
identity and derives strict positivity from a positive constant plus a finite
sum of nonnegative weighted squares.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/--
An exact certificate that `p` is a positive constant plus a finite weighted
sum of polynomial squares.
-/
structure PositiveSumSquaresCertificate (p : ℚ[X]) where
  terms : ℕ
  constant : ℚ
  weight : Fin terms → ℚ
  square : Fin terms → ℚ[X]
  constant_pos : 0 < constant
  weight_nonneg : ∀ i, 0 ≤ weight i
  identity :
    p = C constant + ∑ i : Fin terms, C (weight i) * (square i) ^ 2

/-- Every polynomial carrying such a certificate is strictly positive on `ℚ`. -/
theorem PositiveSumSquaresCertificate.eval_pos
    {p : ℚ[X]} (cert : PositiveSumSquaresCertificate p) (x : ℚ) :
    0 < eval x p := by
  have hsquares :
      0 ≤ ∑ i : Fin cert.terms,
        cert.weight i * (eval x (cert.square i)) ^ 2 := by
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (cert.weight_nonneg i) (sq_nonneg _)
  calc
    0 < cert.constant +
        ∑ i : Fin cert.terms,
          cert.weight i * (eval x (cert.square i)) ^ 2 :=
      add_pos_of_pos_of_nonneg cert.constant_pos hsquares
    _ = eval x p := by
      have hsum :
          eval x
              (∑ i : Fin cert.terms,
                C (cert.weight i) * (cert.square i) ^ 2) =
            ∑ i : Fin cert.terms,
              cert.weight i * (eval x (cert.square i)) ^ 2 := by
        change
          eval x
              (∑ i ∈ Finset.univ,
                C (cert.weight i) * (cert.square i) ^ 2) =
            ∑ i ∈ Finset.univ,
              cert.weight i * (eval x (cert.square i)) ^ 2
        rw [eval_finsetSum]
        simp
      have hidentity := congrArg (eval x) cert.identity
      rw [eval_add, eval_C, hsum] at hidentity
      exact hidentity.symm

/-- In particular a certified positive polynomial has no rational zero. -/
theorem PositiveSumSquaresCertificate.eval_ne_zero
    {p : ℚ[X]} (cert : PositiveSumSquaresCertificate p) (x : ℚ) :
    eval x p ≠ 0 :=
  ne_of_gt (cert.eval_pos x)

/-- Affine substitution used by compact certificates such as `y = 30*x`. -/
def affinePolynomial (a b : ℚ) : ℚ[X] :=
  C a * X + C b

@[simp] theorem eval_affinePolynomial (a b x : ℚ) :
    eval x (affinePolynomial a b) = a * x + b := by
  simp [affinePolynomial]

/--
Strict positivity after an invertible affine change of variable implies
strict positivity of the original polynomial.
-/
theorem eval_pos_of_affine_certificate
    {p : ℚ[X]} {a b : ℚ} (ha : a ≠ 0)
    (cert : PositiveSumSquaresCertificate (p.comp (affinePolynomial a b)))
    (y : ℚ) :
    0 < eval y p := by
  let x : ℚ := (y - b) / a
  have hsub : a * x + b = y := by
    dsimp [x]
    field_simp [ha]
    ring
  have hpos := cert.eval_pos x
  simpa [eval_comp, hsub] using hpos

/-- The corresponding no-root form of the affine certificate theorem. -/
theorem eval_ne_zero_of_affine_certificate
    {p : ℚ[X]} {a b : ℚ} (ha : a ≠ 0)
    (cert : PositiveSumSquaresCertificate (p.comp (affinePolynomial a b)))
    (y : ℚ) :
    eval y p ≠ 0 :=
  ne_of_gt (eval_pos_of_affine_certificate ha cert y)

end

end Cuboid2
