import Cuboid2.CapellQuintic

/-!
# Exact coefficient equations for the symmetric `5+5` case

A monic quintic factor

`R(X)=X^5+aX^4+bX^3+cX^2+dX+e`

paired with `-R(-X)` has only even powers.  This file checks the complete
multiplication identity in Lean and extracts the five coefficient equations
used by the pinned `5+5` certificate.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- A generic monic quintic with named coefficients. -/
def quinticFactor (a b c d e : ℚ) : ℚ[X] :=
  X ^ 5 + C a * X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C d * X + C e

/-- The coefficient of `X^8` in `P_s(X^2)`. -/
def fiveFiveCoeff8 (s : ℚ) : ℚ :=
  (2 + s) * (3 - 2 * s)

/-- The coefficient of `X^6` in `P_s(X^2)`. -/
def fiveFiveCoeff6 (s : ℚ) : ℚ :=
  1 + 10 * s + 4 * s ^ 2 - 14 * s ^ 3 + s ^ 4

/-- The coefficient of `X^4` in `P_s(X^2)`. -/
def fiveFiveCoeff4 (s : ℚ) : ℚ :=
  -s * (1 - 14 * s + 4 * s ^ 2 + 10 * s ^ 3 + s ^ 4)

/-- The coefficient of `X^2` in `P_s(X^2)`. -/
def fiveFiveCoeff2 (s : ℚ) : ℚ :=
  -s ^ 3 * (1 + 2 * s) * (-2 + 3 * s)

/-- The complete even form of the normalized composition. -/
theorem normalizedEvenPolynomial_explicit (s : ℚ) :
    normalizedEvenPolynomial s =
      X ^ 10 + C (fiveFiveCoeff8 s) * X ^ 8 +
        C (fiveFiveCoeff6 s) * X ^ 6 +
          C (fiveFiveCoeff4 s) * X ^ 4 +
            C (fiveFiveCoeff2 s) * X ^ 2 + C (-s ^ 5) := by
  simp [normalizedEvenPolynomial, normalizedQuintic, normalizedQuinticLower,
    fiveFiveCoeff8, fiveFiveCoeff6, fiveFiveCoeff4, fiveFiveCoeff2]
  ring

/-- Exact multiplication of a quintic by its signed reflection. -/
theorem quinticFactor_symmetric_product (a b c d e : ℚ) :
    quinticFactor a b c d e *
        (-(quinticFactor a b c d e).comp (-X)) =
      X ^ 10 + C (2 * b - a ^ 2) * X ^ 8 +
        C (b ^ 2 + 2 * d - 2 * a * c) * X ^ 6 +
          C (2 * b * d - c ^ 2 - 2 * a * e) * X ^ 4 +
            C (d ^ 2 - 2 * c * e) * X ^ 2 + C (-e ^ 2) := by
  simp [quinticFactor]
  ring

/-- Every monic degree-five polynomial has the displayed coefficient form. -/
theorem eq_quinticFactor_of_monic_degree_five
    {R : ℚ[X]} (hR : R.Monic) (hdegree : R.natDegree = 5) :
    R = quinticFactor (R.coeff 4) (R.coeff 3) (R.coeff 2)
      (R.coeff 1) (R.coeff 0) := by
  calc
    R = X ^ R.natDegree +
        ∑ i ∈ Finset.range R.natDegree, C (R.coeff i) * X ^ i := hR.as_sum
    _ = quinticFactor (R.coeff 4) (R.coeff 3) (R.coeff 2)
        (R.coeff 1) (R.coeff 0) := by
      rw [hdegree]
      simp [quinticFactor, Finset.sum_range_succ]
      ring

/-- The five scalar equations forced by a symmetric factorization. -/
structure FiveFiveCoefficientSolution (s : ℚ) where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  e : ℚ
  coeff8 : 2 * b - a ^ 2 = fiveFiveCoeff8 s
  coeff6 : b ^ 2 + 2 * d - 2 * a * c = fiveFiveCoeff6 s
  coeff4 : 2 * b * d - c ^ 2 - 2 * a * e = fiveFiveCoeff4 s
  coeff2 : d ^ 2 - 2 * c * e = fiveFiveCoeff2 s
  constant : e ^ 2 = s ^ 5

/-- A symmetric `5+5` factorization supplies the exact coefficient solution. -/
theorem coefficientSolution_of_symmetricFiveFiveCase
    {s : ℚ} (hcase : SymmetricFiveFiveCase s) :
    Nonempty (FiveFiveCoefficientSolution s) := by
  rcases hcase with ⟨R, hRmonic, hRdegree, hRirreducible, hfactor⟩
  let a : ℚ := R.coeff 4
  let b : ℚ := R.coeff 3
  let c : ℚ := R.coeff 2
  let d : ℚ := R.coeff 1
  let e : ℚ := R.coeff 0
  have hRexplicit : R = quinticFactor a b c d e := by
    simpa [a, b, c, d, e] using
      (eq_quinticFactor_of_monic_degree_five hRmonic hRdegree)
  have hfactor' :
      normalizedEvenPolynomial s =
        quinticFactor a b c d e *
          (-(quinticFactor a b c d e).comp (-X)) := by
    simpa [normalizedEvenPolynomial, hRexplicit] using hfactor
  have hpoly :
      X ^ 10 + C (fiveFiveCoeff8 s) * X ^ 8 +
          C (fiveFiveCoeff6 s) * X ^ 6 +
            C (fiveFiveCoeff4 s) * X ^ 4 +
              C (fiveFiveCoeff2 s) * X ^ 2 + C (-s ^ 5) =
        X ^ 10 + C (2 * b - a ^ 2) * X ^ 8 +
          C (b ^ 2 + 2 * d - 2 * a * c) * X ^ 6 +
            C (2 * b * d - c ^ 2 - 2 * a * e) * X ^ 4 +
              C (d ^ 2 - 2 * c * e) * X ^ 2 + C (-e ^ 2) := by
    calc
      _ = normalizedEvenPolynomial s := (normalizedEvenPolynomial_explicit s).symm
      _ = quinticFactor a b c d e *
          (-(quinticFactor a b c d e).comp (-X)) := hfactor'
      _ = _ := quinticFactor_symmetric_product a b c d e
  have h8 := congrArg (fun F : ℚ[X] => F.coeff 8) hpoly
  have h6 := congrArg (fun F : ℚ[X] => F.coeff 6) hpoly
  have h4 := congrArg (fun F : ℚ[X] => F.coeff 4) hpoly
  have h2 := congrArg (fun F : ℚ[X] => F.coeff 2) hpoly
  have h0 := congrArg (fun F : ℚ[X] => F.coeff 0) hpoly
  refine ⟨{
    a := a
    b := b
    c := c
    d := d
    e := e
    coeff8 := ?_
    coeff6 := ?_
    coeff4 := ?_
    coeff2 := ?_
    constant := ?_ }⟩
  · simpa using h8.symm
  · simpa using h6.symm
  · simpa using h4.symm
  · simpa using h2.symm
  · simpa using (congrArg Neg.neg h0).symm

end

end Cuboid2
