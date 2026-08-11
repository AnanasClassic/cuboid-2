import Cuboid2.Polynomial

/-!
# Exact quadratic-factor equations

This file formalizes the elementary polynomial division at the entrance to
the `2+3` branch.  No resultant or arithmetic-geometry oracle is used: the
identity is checked directly in `ℚ[X]` by normalization in the polynomial
ring.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- Coefficient of `X^4` in the normalized quintic. -/
def quinticC4 (s : ℚ) : ℚ := (2 + s) * (3 - 2 * s)

/-- Coefficient of `X^3` in the normalized quintic. -/
def quinticC3 (s : ℚ) : ℚ :=
  1 + 10 * s + 4 * s ^ 2 - 14 * s ^ 3 + s ^ 4

/-- Coefficient of `X^2` in the normalized quintic. -/
def quinticC2 (s : ℚ) : ℚ :=
  -s * (1 - 14 * s + 4 * s ^ 2 + 10 * s ^ 3 + s ^ 4)

/-- Coefficient of `X` in the normalized quintic. -/
def quinticC1 (s : ℚ) : ℚ :=
  -s ^ 3 * (1 + 2 * s) * (-2 + 3 * s)

/-- Constant coefficient of the normalized quintic. -/
def quinticC0 (s : ℚ) : ℚ := -s ^ 5

/-- The prospective monic quadratic factor `X^2+aX+b`. -/
def monicQuadratic (a b : ℚ) : ℚ[X] :=
  X ^ 2 + C a * X + C b

/-- The quotient forced by the top three coefficient comparisons. -/
def forcedCubic (s a b : ℚ) : ℚ[X] :=
  X ^ 3 + C (quinticC4 s - a) * X ^ 2 +
    C (a ^ 2 - a * quinticC4 s + quinticC3 s - b) * X +
    C (-a ^ 3 + a ^ 2 * quinticC4 s + 2 * a * b -
      a * quinticC3 s - b * quinticC4 s + quinticC2 s)

/-- Coefficient of `X` in the exact division remainder. -/
def quadraticR1 (s a b : ℚ) : ℚ :=
  b ^ 2 +
    (-3 * a ^ 2 + 2 * a * quinticC4 s - quinticC3 s) * b +
    (a ^ 4 - quinticC4 s * a ^ 3 + quinticC3 s * a ^ 2 -
      quinticC2 s * a + quinticC1 s)

/-- Constant coefficient in the exact division remainder. -/
def quadraticR0 (s a b : ℚ) : ℚ :=
  (quinticC4 s - 2 * a) * b ^ 2 +
    (a ^ 3 - quinticC4 s * a ^ 2 + quinticC3 s * a - quinticC2 s) * b +
    quinticC0 s

/-- The normalized quintic written with its five scalar coefficient functions. -/
theorem normalizedQuintic_coefficient_form (s : ℚ) :
    normalizedQuintic s =
      X ^ 5 + C (quinticC4 s) * X ^ 4 + C (quinticC3 s) * X ^ 3 +
        C (quinticC2 s) * X ^ 2 + C (quinticC1 s) * X + C (quinticC0 s) := by
  simp [normalizedQuintic, normalizedQuinticLower, quinticC4, quinticC3,
    quinticC2, quinticC1, quinticC0]
  ring

/--
Exact Euclidean-division identity.  In particular, the two scalar equations
`quadraticR1=0` and `quadraticR0=0` are sufficient for a quadratic factor.
-/
theorem normalizedQuintic_quadratic_division (s a b : ℚ) :
    normalizedQuintic s =
      monicQuadratic a b * forcedCubic s a b +
        C (quadraticR1 s a b) * X + C (quadraticR0 s a b) := by
  rw [normalizedQuintic_coefficient_form]
  simp [monicQuadratic, forcedCubic, quadraticR1, quadraticR0]
  ring

/-- The exact pair of remainder equations used by every later certificate. -/
def SatisfiesQuadraticRemainders (s a b : ℚ) : Prop :=
  quadraticR1 s a b = 0 ∧ quadraticR0 s a b = 0

/-- Vanishing of the two remainders gives the advertised factorization. -/
theorem factorization_of_quadratic_remainders
    {s a b : ℚ} (h : SatisfiesQuadraticRemainders s a b) :
    normalizedQuintic s = monicQuadratic a b * forcedCubic s a b := by
  rw [normalizedQuintic_quadratic_division, h.1, h.2]
  simp

/-- Conversely, equality with the forced cubic makes both remainders zero. -/
theorem quadratic_remainders_of_forced_factorization
    {s a b : ℚ}
    (h : normalizedQuintic s = monicQuadratic a b * forcedCubic s a b) :
    SatisfiesQuadraticRemainders s a b := by
  have hrem : C (quadraticR1 s a b) * X + C (quadraticR0 s a b) = 0 := by
    calc
      C (quadraticR1 s a b) * X + C (quadraticR0 s a b) =
          normalizedQuintic s - monicQuadratic a b * forcedCubic s a b := by
            rw [normalizedQuintic_quadratic_division]
            ring
      _ = 0 := by rw [h]; ring
  constructor
  · have := congrArg (fun P : ℚ[X] => P.coeff 1) hrem
    simpa using this
  · have := congrArg (fun P : ℚ[X] => P.coeff 0) hrem
    simpa using this

end

end Cuboid2
