import Cuboid2.QuadraticReduction.GaussianSplit37ReductionActual
import Cuboid2.QuadraticReduction.GaussianSaturationBridge

/-!
# Actual saturation of the visible point at the split prime above 37

The plus reduction at `i ↦ 6` is an actual homomorphism on all
`E₀(ℚ(i))`-points, and every value belongs to the exhaustive finite point
table.  The closed finite certificate at 37 therefore rules out a
three-division preimage of the visible point.  The final theorem transfers
this fact to the free coefficient in any exact rank-one normal form.
-/

namespace Cuboid2
namespace GaussianP37SaturationActual

noncomputable section

open GaussianFinite
open GaussianFiniteExponent
open GaussianP37
open GaussianIndexIndependent
open GaussianSaturationFinite
open GaussianSaturationBridge
open GaussianProjectiveReduction
open GaussianProjectiveReductionHom
open GaussianVisibleReduction
open GaussianSplit37ReductionActual

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have hxnonneg : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

/-- The visible point has no three-division preimage in the actual Gaussian
elliptic curve. -/
theorem visiblePoint_not_three_divisible :
    ¬ ∃ Q : E0Point, 3 • Q = visiblePoint := by
  rintro ⟨Q, hQ⟩
  have hmap :
      reduceE0Plus (3 • Q) =
        finiteMul 37 plusCoefficients.1 plusCoefficients.2
          (reduceE0Plus Q) 3 :=
    map_nsmul_finite
      37 plusCoefficients.1 plusCoefficients.2
      reduceE0Plus reduceE0Plus_zero reduceE0Plus_add Q 3
  have hmul :
      finiteMul 37 plusCoefficients.1 plusCoefficients.2
          (reduceE0Plus Q) 3 =
        some (2, 2) := by
    rw [← hmap, hQ]
    exact reduceE0Plus_gaussianE0P
  have htrue :
      finiteDivisible 37 plusCoefficients.1 plusCoefficients.2 3
          (some (2, 2)) =
        true :=
    finiteDivisible_eq_true_of_witness
      37 plusCoefficients.1 plusCoefficients.2 3
      (some (2, 2)) (reduceE0Plus Q)
      (reduceE0Plus_mem_finitePoints Q) hmul
  have hfalse :
      finiteDivisible 37 plusCoefficients.1 plusCoefficients.2 3
          (some (2, 2)) =
        false := by
    simpa only [plusCoefficients] using p37_not_three_divisible.1
  rw [hfalse] at htrue
  contradiction

/-- In any exact `ℤ × ZMod 2` normal form for `E₀(ℚ(i))`, the free
coefficient of the visible point is not divisible by three. -/
theorem three_not_dvd_visiblePoint_coefficient
    (e : E0Point ≃+ ℤ × ZMod 2)
    {m : ℤ} {δ : ℕ}
    (hP :
      visiblePoint = m • freeGenerator e + δ • twoTorsionPoint) :
    ¬ (3 : ℤ) ∣ m := by
  intro hdiv
  apply visiblePoint_not_three_divisible
  exact
    visiblePoint_divisible_of_odd_dvd_coefficient
      e hP (by norm_num) hdiv

end

end GaussianP37SaturationActual
end Cuboid2
