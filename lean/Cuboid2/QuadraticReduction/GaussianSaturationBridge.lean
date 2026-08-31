import Cuboid2.QuadraticReduction.GaussianFiniteExponent
import Cuboid2.QuadraticReduction.GaussianIndexIndependent
import Cuboid2.QuadraticReduction.GaussianSaturationFinite

/-!
# Group-theoretic bridge for visible-point saturation

An odd prime divisor of the free coefficient of the visible point makes the
point itself divisible by that prime: the possible two-torsion translate is
unchanged by odd multiplication.  The second half packages how an actual
finite reduction witness contradicts the closed `finiteDivisible = false`
rows.
-/

namespace Cuboid2
namespace GaussianSaturationBridge

noncomputable section

open GaussianFinite GaussianFiniteExponent GaussianSaturationFinite
  GaussianIndexIndependent GaussianRankArithmetic

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have hxnonneg : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

/-- Odd scalar multiplication fixes a point killed by two. -/
theorem odd_nsmul_twoTorsion
    {G : Type*} [AddCommGroup G]
    (T : G) (hT : 2 • T = 0)
    {n : ℕ} (hn : Odd n) :
    n • T = T := by
  obtain ⟨k, hk⟩ := hn
  calc
    n • T = (k * 2 + 1) • T := by rw [hk, Nat.mul_comm 2 k]
    _ = (k * 2) • T + T := by rw [add_nsmul, one_nsmul]
    _ = k • (2 • T) + T := by rw [mul_nsmul']
    _ = T := by rw [hT, nsmul_zero, zero_add]

/-- If an odd natural number divides the integral free coefficient in a
rank-one normal form, the represented point is divisible by that number. -/
theorem point_divisible_of_odd_dvd_freeCoefficient
    {G : Type*} [AddCommGroup G]
    (T Gen P : G) (hT : 2 • T = 0)
    {m : ℤ} {δ : ℕ}
    (hP : P = m • Gen + δ • T)
    {n : ℕ} (hn : Odd n)
    (hdiv : (n : ℤ) ∣ m) :
    ∃ Q : G, n • Q = P := by
  obtain ⟨a, ha⟩ := hdiv
  refine ⟨a • Gen + δ • T, ?_⟩
  rw [nsmul_add]
  have hfree : n • (a • Gen) = m • Gen := by
    calc
      n • (a • Gen) = (n : ℤ) • (a • Gen) :=
        (natCast_zsmul (a • Gen) n).symm
      _ = ((n : ℤ) * a) • Gen := by rw [smul_smul]
      _ = m • Gen := by rw [ha]
  rw [hfree]
  have htor :
      n • (δ • T) = δ • T := by
    rw [smul_comm, odd_nsmul_twoTorsion T hT hn]
  rw [htor, ← hP]

/-- Actual specialization to the visible point and the named Gaussian
two-torsion point. -/
theorem visiblePoint_divisible_of_odd_dvd_coefficient
    (e : E0Point ≃+ ℤ × ZMod 2)
    {m : ℤ} {δ : ℕ}
    (hP :
      visiblePoint = m • freeGenerator e + δ • twoTorsionPoint)
    {n : ℕ} (hn : Odd n)
    (hdiv : (n : ℤ) ∣ m) :
    ∃ Q : E0Point, n • Q = visiblePoint :=
  point_divisible_of_odd_dvd_freeCoefficient
    twoTorsionPoint (freeGenerator e) visiblePoint
    two_nsmul_gaussianE0T hP hn hdiv

/-- A listed finite preimage makes the executable divisibility predicate
true. -/
theorem finiteDivisible_eq_true_of_witness
    (p A B n : ℕ) (P Q : FinitePoint)
    (hQ : Q ∈ finitePoints p A B)
    (hmul : finiteMul p A B Q n = P) :
    finiteDivisible p A B n P = true := by
  unfold finiteDivisible
  rw [List.any_eq_true]
  exact ⟨Q, hQ, by simpa only [beq_iff_eq] using hmul⟩

end

end GaussianSaturationBridge
end Cuboid2
