import Mathlib

/-!
# Closed finite certificates for the Gaussian-cover argument

This module contains only finite, exhaustive computations.  Gaussian residues
are represented by pairs of canonical natural-number representatives, and the
elliptic-curve calculations use the explicit affine group law.  Consequently
the statements below do not depend on a global rank theorem, a reduction
theorem, or a computer-algebra oracle.
-/

namespace Cuboid2
namespace GaussianFinite

/-- A Gaussian residue is stored as its real and imaginary representatives. -/
abbrev GaussResidue := ℕ × ℕ

/-- Canonical reduction of a Gaussian pair modulo `n`. -/
def gaussNormalize (n : ℕ) (z : GaussResidue) : GaussResidue :=
  (z.1 % n, z.2 % n)

/-- Subtraction of natural representatives in `ℤ/nℤ`. -/
def residueSub (n a b : ℕ) : ℕ :=
  (a % n + (n - b % n)) % n

/-- Addition in `(ℤ/nℤ)[i]`. -/
def gaussAdd (n : ℕ) (z w : GaussResidue) : GaussResidue :=
  ((z.1 + w.1) % n, (z.2 + w.2) % n)

/-- Multiplication in `(ℤ/nℤ)[i]`, with `i² = -1`. -/
def gaussMul (n : ℕ) (z w : GaussResidue) : GaussResidue :=
  (residueSub n (z.1 * w.1) (z.2 * w.2),
    (z.1 * w.2 + z.2 * w.1) % n)

/-- The square of a Gaussian residue. -/
def gaussSq (n : ℕ) (z : GaussResidue) : GaussResidue :=
  gaussMul n z z

/-- The fourth power of a Gaussian residue. -/
def gaussFourth (n : ℕ) (z : GaussResidue) : GaussResidue :=
  gaussSq n (gaussSq n z)

/-- All pairs of canonical representatives modulo `n`. -/
def gaussResidues (n : ℕ) : List GaussResidue :=
  (List.range n).flatMap fun a => (List.range n).map fun b => (a, b)

/-- The complete, duplicate-free list of Gaussian square residues modulo `n`. -/
def gaussSquareResidues (n : ℕ) : List GaussResidue :=
  ((gaussResidues n).map (gaussSq n)).eraseDups

/-- `1+i` does not divide at least one of `U,V`. -/
def lambdaPrimitive (U V : GaussResidue) : Bool :=
  !((U.1 + U.2) % 2 == 0 && (V.1 + V.2) % 2 == 0)

/-- The right side of
`N² = d U⁴ + A U²V² + (B/d)V⁴` modulo `n`.

The fourth argument is the already exact-divided Gaussian integer `B/d`.
-/
def homogeneousSpaceRhs
    (n : ℕ) (A d BdivD U V : GaussResidue) : GaussResidue :=
  gaussAdd n
    (gaussAdd n
      (gaussMul n d (gaussFourth n U))
      (gaussMul n A (gaussMul n (gaussSq n U) (gaussSq n V))))
    (gaussMul n BdivD (gaussFourth n V))

/-- Exhaustive local-solubility search for a `lambda`-primitive homogeneous
space solution.  The list tested for membership is exactly the image of the
squaring map on all Gaussian residues.
-/
def hasPrimitiveHomogeneousSpaceSolution
    (n : ℕ) (A d BdivD : GaussResidue) : Bool :=
  let squares := gaussSquareResidues n
  (gaussResidues n).any fun U =>
    (gaussResidues n).any fun V =>
      lambdaPrimitive U V &&
        squares.contains (homogeneousSpaceRhs n A d BdivD U V)

/-- Proposition-level interface to the exhaustive homogeneous-space search. -/
def PrimitiveHomogeneousSpaceLocallySoluble
    (n : ℕ) (A d BdivD : GaussResidue) : Prop :=
  hasPrimitiveHomogeneousSpaceSolution n A d BdivD = true

/-! ## Odd `lambda`-valuation obstruction rows

The squarefree support at `lambda = 1+i` has two parity choices.  The
previous candidate lists account for the even choice; the following sixteen
closed computations account for the odd choice, one row for each remaining
unit/prime class on each of the four homogeneous spaces.  All coefficients
displayed in the theorem statements are the canonical residues of the exact
Gaussian integers `A`, `d`, and `B/d` modulo `4`.
-/

/-- On `E₀`, the class `lambda` is obstructed modulo `4`.
Here `B/lambda = -3-i`.
-/
theorem e0_lambda_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (0, 2) (1, 1) (1, 3) = false := by
  native_decide

/-- On `E₀`, the class `i*lambda` is obstructed modulo `4`.
Here `i*lambda = -1+i` and `B/(i*lambda) = -1+3i`.
-/
theorem e0_iLambda_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (0, 2) (3, 1) (3, 3) = false := by
  native_decide

/-- On `E₀`, the class `lambda*pi` is obstructed modulo `4`.
Here `lambda*pi = -1+3i` and `B/(lambda*pi) = -1+i`.
-/
theorem e0_lambdaPi_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (0, 2) (3, 3) (3, 1) = false := by
  native_decide

/-- On `E₀`, the class `i*lambda*pi` is obstructed modulo `4`.
Here `i*lambda*pi = -3-i` and `B/(i*lambda*pi) = 1+i`.
-/
theorem e0_iLambdaPi_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (0, 2) (1, 3) (1, 1) = false := by
  native_decide

/-- On the dual of `E₀`, the class `lambda` is obstructed modulo `4`.
Here `B/lambda = 10+6i`.
-/
theorem e0Dual_lambda_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (0, 0) (1, 1) (2, 2) = false := by
  native_decide

/-- On the dual of `E₀`, the class `i*lambda` is obstructed modulo `4`.
Here `i*lambda = -1+i` and `B/(i*lambda) = 6-10i`.
-/
theorem e0Dual_iLambda_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (0, 0) (3, 1) (2, 2) = false := by
  native_decide

/-- On the dual of `E₀`, the class `lambda*rho` is obstructed modulo `4`.
Here `lambda*rho = -3+5i` and `B/(lambda*rho) = 2-2i`.
-/
theorem e0Dual_lambdaRho_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (0, 0) (1, 1) (2, 2) = false := by
  native_decide

/-- On the dual of `E₀`, the class `i*lambda*rho` is obstructed modulo `4`.
Here `i*lambda*rho = -5-3i` and `B/(i*lambda*rho) = -2-2i`.
-/
theorem e0Dual_iLambdaRho_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (0, 0) (3, 1) (2, 2) = false := by
  native_decide

/-- On `E₁`, the class `lambda` is obstructed modulo `4`.
Here `B/lambda = 3+i`.
-/
theorem e1_lambda_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (2, 0) (1, 1) (3, 1) = false := by
  native_decide

/-- On `E₁`, the class `i*lambda` is obstructed modulo `4`.
Here `i*lambda = -1+i` and `B/(i*lambda) = 1-3i`.
-/
theorem e1_iLambda_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (2, 0) (3, 1) (1, 1) = false := by
  native_decide

/-- On `E₁`, the class `lambda*pi` is obstructed modulo `4`.
Here `lambda*pi = -1+3i` and `B/(lambda*pi) = 1-i`.
-/
theorem e1_lambdaPi_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (2, 0) (3, 3) (1, 3) = false := by
  native_decide

/-- On `E₁`, the class `i*lambda*pi` is obstructed modulo `4`.
Here `i*lambda*pi = -3-i` and `B/(i*lambda*pi) = -1-i`.
-/
theorem e1_iLambdaPi_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (2, 0) (1, 3) (3, 3) = false := by
  native_decide

/-- On the dual of `E₁`, the class `lambda` is obstructed modulo `4`.
Here `B/lambda = -10-6i`.
-/
theorem e1Dual_lambda_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (0, 0) (1, 1) (2, 2) = false := by
  native_decide

/-- On the dual of `E₁`, the class `i*lambda` is obstructed modulo `4`.
Here `i*lambda = -1+i` and `B/(i*lambda) = -6+10i`.
-/
theorem e1Dual_iLambda_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (0, 0) (3, 1) (2, 2) = false := by
  native_decide

/-- On the dual of `E₁`, the class `lambda*rho` is obstructed modulo `4`.
Here `lambda*rho = -3+5i` and `B/(lambda*rho) = -2+2i`.
-/
theorem e1Dual_lambdaRho_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (0, 0) (1, 1) (2, 2) = false := by
  native_decide

/-- On the dual of `E₁`, the class `i*lambda*rho` is obstructed modulo `4`.
Here `i*lambda*rho = -5-3i` and `B/(i*lambda*rho) = 2+2i`.
-/
theorem e1Dual_iLambdaRho_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (0, 0) (3, 1) (2, 2) = false := by
  native_decide

/-- The class `i` on the dual of `E₀` is obstructed modulo `16`. -/
theorem e0Dual_i_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 16 (0, 12) (0, 1) (0, 12) = false := by
  native_decide

/-- The class `i*rho` on the dual of `E₀` is obstructed modulo `16`. -/
theorem e0Dual_iRho_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 16 (0, 12) (12, 1) (0, 12) = false := by
  native_decide

/-- The class `i` on `E₁` is obstructed modulo `8`. -/
theorem e1_i_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 8 (2, 0) (0, 1) (4, 6) = false := by
  native_decide

/-- The class `pi` on `E₁` is already obstructed modulo `4`. -/
theorem e1_pi_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 4 (2, 0) (1, 2) (2, 0) = false := by
  native_decide

/-- The class `i` on the dual of `E₁` is obstructed modulo `32`. -/
theorem e1Dual_i_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 32 (28, 0) (0, 1) (16, 4) = false := by
  native_decide

/-- The class `i*rho` on the dual of `E₁` is obstructed modulo `32`. -/
theorem e1Dual_iRho_local_obstruction :
    hasPrimitiveHomogeneousSpaceSolution 32 (28, 0) (28, 1) (0, 4) = false := by
  native_decide

/-- Proposition-level collection of all six closed local obstructions. -/
theorem allHomogeneousSpaceLocalObstructions :
    ¬ PrimitiveHomogeneousSpaceLocallySoluble 16 (0, 12) (0, 1) (0, 12) ∧
    ¬ PrimitiveHomogeneousSpaceLocallySoluble 16 (0, 12) (12, 1) (0, 12) ∧
    ¬ PrimitiveHomogeneousSpaceLocallySoluble 8 (2, 0) (0, 1) (4, 6) ∧
    ¬ PrimitiveHomogeneousSpaceLocallySoluble 4 (2, 0) (1, 2) (2, 0) ∧
    ¬ PrimitiveHomogeneousSpaceLocallySoluble 32 (28, 0) (0, 1) (16, 4) ∧
    ¬ PrimitiveHomogeneousSpaceLocallySoluble 32 (28, 0) (28, 1) (0, 4) := by
  simp only [PrimitiveHomogeneousSpaceLocallySoluble,
    e0Dual_i_local_obstruction, e0Dual_iRho_local_obstruction,
    e1_i_local_obstruction, e1_pi_local_obstruction,
    e1Dual_i_local_obstruction, e1Dual_iRho_local_obstruction,
    Bool.false_eq_true, not_false_eq_true, and_self]

/-! ## Explicit finite elliptic-curve arithmetic -/

/-- An affine point, with `none` representing the point at infinity. -/
abbrev FinitePoint := Option (ℕ × ℕ)

/-- Multiplicative inverse by exhaustive search.  It is used below only for
nonzero elements of the displayed prime fields.
-/
def residueInv (p a : ℕ) : ℕ :=
  (((List.range p).find? fun b => (a * b) % p == 1).getD 0) % p

/-- The right side `x³ + A x² + B x` modulo `p`. -/
def finiteCurveRhs (p A B x : ℕ) : ℕ :=
  (x ^ 3 + A * x ^ 2 + B * x) % p

/-- The explicit affine addition law on `y²=x³+Ax²+Bx` modulo `p`. -/
def finiteAdd (p A B : ℕ) (P Q : FinitePoint) : FinitePoint :=
  match P, Q with
  | none, Q => Q
  | P, none => P
  | some (x, y), some (X, Y) =>
      if x % p = X % p && (y + Y) % p = 0 then
        none
      else
        let slope :=
          if x % p = X % p then
            ((3 * x ^ 2 + 2 * A * x + B) *
              residueInv p (2 * y % p)) % p
          else
            (residueSub p Y y * residueInv p (residueSub p X x)) % p
        let xr := residueSub p
          (residueSub p (residueSub p (slope ^ 2) A) x) X
        let yr := residueSub p (slope * residueSub p x xr) y
        some (xr, yr)

/-- Scalar multiplication by repeated addition.  The concrete certificates
are tiny, so this deliberately simple definition is adequate and transparent.
-/
def finiteMul (p A B : ℕ) (P : FinitePoint) : ℕ → FinitePoint
  | 0 => none
  | n + 1 => finiteAdd p A B (finiteMul p A B P n) P

/-- Exhaustive list of all points on `y²=x³+Ax²+Bx` over `ℤ/pℤ`. -/
def finitePoints (p A B : ℕ) : List FinitePoint :=
  none ::
    (List.range p).flatMap fun x =>
      (List.range p).filterMap fun y =>
        if y ^ 2 % p = finiteCurveRhs p A B x then
          some (some (x, y))
        else
          none

/-- The first positive multiple equal to infinity, within the Hasse-safe
search bound used by the independent certificate.
-/
def finiteOrder (p A B : ℕ) (P : FinitePoint) : ℕ :=
  (((List.range (4 * p + 20)).map Nat.succ).find? fun n =>
    finiteMul p A B P n == none).getD 0

/-- The least common multiple of all point orders. -/
def finiteExponent (p A B : ℕ) : ℕ :=
  (finitePoints p A B).foldl
    (fun e P => Nat.lcm e (finiteOrder p A B P)) 1

/-- Equality of projective `x`-coordinates, including infinity. -/
def sameX : FinitePoint → FinitePoint → Bool
  | none, none => true
  | some P, some Q => P.1 == Q.1
  | _, _ => false

/-- Curve coefficients after substituting a root for `i` in `E₀`. -/
def e0Coefficients (p root : ℕ) : ℕ × ℕ :=
  (2 * root % p, residueSub p (p - 2) (4 * root))

/-! ## Torsion-bound rows -/

/-- Curve coefficients after substituting a root for `i` in `E₁`. -/
def e1Coefficients (p root : ℕ) : ℕ × ℕ :=
  (2 % p, (2 + 4 * root) % p)

/-- Both split fibres over `13` have the certified orders used to bound
prime-to-13 torsion on `E₀`. -/
theorem e0TorsionRows13 :
    let plus := e0Coefficients 13 5
    let minus := e0Coefficients 13 8
    (finitePoints 13 plus.1 plus.2).length = 12 ∧
      (finitePoints 13 minus.1 minus.2).length = 18 := by
  native_decide

/-- Both split fibres over `29` have the certified orders used to exclude
the remaining possible `13`-primary torsion on `E₀`. -/
theorem e0TorsionRows29 :
    let plus := e0Coefficients 29 12
    let minus := e0Coefficients 29 17
    (finitePoints 29 plus.1 plus.2).length = 28 ∧
      (finitePoints 29 minus.1 minus.2).length = 38 := by
  native_decide

/-- Both split fibres over `13` have the certified orders used to bound
prime-to-13 torsion on `E₁`. -/
theorem e1TorsionRows13 :
    let plus := e1Coefficients 13 5
    let minus := e1Coefficients 13 8
    (finitePoints 13 plus.1 plus.2).length = 16 ∧
      (finitePoints 13 minus.1 minus.2).length = 10 := by
  native_decide

/-- Both split fibres over `29` have the certified orders used to exclude
the remaining possible `13`-primary torsion on `E₁`. -/
theorem e1TorsionRows29 :
    let plus := e1Coefficients 29 12
    let minus := e1Coefficients 29 17
    (finitePoints 29 plus.1 plus.2).length = 32 ∧
      (finitePoints 29 minus.1 minus.2).length = 22 := by
  native_decide

/-! ## Index rows -/

/-- The `p=29`, `i=12` row: 28 points, `P` has order 14, and
`[7]P=(0,0)`.
-/
theorem indexRow29 :
    let coeff := e0Coefficients 29 12
    (finitePoints 29 coeff.1 coeff.2).length = 28 ∧
      finiteOrder 29 coeff.1 coeff.2 (some (2, 2)) = 14 ∧
      finiteMul 29 coeff.1 coeff.2 (some (2, 2)) 7 = some (0, 0) ∧
      finiteMul 29 coeff.1 coeff.2 (some (2, 2)) 14 = none := by
  native_decide

/-- The `p=157`, `i=28` row: 148 points, `P` has order 74, and
`[37]P=(92,0)`.
-/
theorem indexRow157 :
    let coeff := e0Coefficients 157 28
    (finitePoints 157 coeff.1 coeff.2).length = 148 ∧
      finiteOrder 157 coeff.1 coeff.2 (some (2, 2)) = 74 ∧
      finiteMul 157 coeff.1 coeff.2 (some (2, 2)) 37 = some (92, 0) ∧
      finiteMul 157 coeff.1 coeff.2 (some (2, 2)) 74 = none := by
  native_decide

end GaussianFinite
end Cuboid2
