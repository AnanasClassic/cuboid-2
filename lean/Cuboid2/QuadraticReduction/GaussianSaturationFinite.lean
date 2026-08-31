import Cuboid2.QuadraticReduction.GaussianP37

/-!
# Closed finite certificates for the index of the visible Gaussian point

The visible point `P=(2,2)` need not be assumed primitive.  If
`P = mG + δT` in a rank-one Mordell--Weil group, a prime divisor of `m`
would make either `P` or `P+T` divisible by that prime after every good
reduction.  The three closed computations below rule this out for
`3`, `7`, and `37`.
-/

namespace Cuboid2
namespace GaussianSaturationFinite

open GaussianFinite GaussianP37

/-- Whether a finite point belongs to the image of multiplication by `n`. -/
def finiteDivisible
    (p A B n : ℕ) (P : FinitePoint) : Bool :=
  (finitePoints p A B).any fun Q =>
    finiteMul p A B Q n == P

/-- At the plus prime above `37`, neither `P` nor `P+T` is three-divisible. -/
theorem p37_not_three_divisible :
    let coeff := e0Coefficients 37 6
    let P : FinitePoint := some (2, 2)
    let T : FinitePoint := some (0, 0)
    finiteDivisible 37 coeff.1 coeff.2 3 P = false ∧
      finiteDivisible 37 coeff.1 coeff.2 3
        (finiteAdd 37 coeff.1 coeff.2 P T) = false := by
  native_decide

/-- At the plus prime above `29`, neither `P` nor `P+T` is seven-divisible. -/
theorem p29_not_seven_divisible :
    let coeff := e0Coefficients 29 12
    let P : FinitePoint := some (2, 2)
    let T : FinitePoint := some (0, 0)
    finiteDivisible 29 coeff.1 coeff.2 7 P = false ∧
      finiteDivisible 29 coeff.1 coeff.2 7
        (finiteAdd 29 coeff.1 coeff.2 P T) = false := by
  native_decide

/-- At the plus prime above `157`, neither `P` nor `P+T` is
thirty-seven-divisible. -/
theorem p157_not_thirtySeven_divisible :
    let coeff := e0Coefficients 157 28
    let P : FinitePoint := some (2, 2)
    let T : FinitePoint := some (0, 0)
    finiteDivisible 157 coeff.1 coeff.2 37 P = false ∧
      finiteDivisible 157 coeff.1 coeff.2 37
        (finiteAdd 157 coeff.1 coeff.2 P T) = false := by
  native_decide

end GaussianSaturationFinite
end Cuboid2
