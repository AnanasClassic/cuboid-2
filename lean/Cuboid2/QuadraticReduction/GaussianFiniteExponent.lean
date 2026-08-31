import Cuboid2.QuadraticReduction.GaussianP37

/-!
# Executable exponent certificates for the split fibres at 37

The point lists in `GaussianFinite` are exhaustive.  These two closed rows
record, in a form convenient for actual reduction maps, that multiplication
by the displayed exponent kills every listed point.
-/

namespace Cuboid2
namespace GaussianFiniteExponent

open GaussianFinite GaussianP37

/-- The two special-fibre coefficient pairs for `E₁` at the same split prime
above `37`. -/
def e1PlusCoefficients : ℕ × ℕ := e1Coefficients 37 6

def e1MinusCoefficients : ℕ × ℕ := e1Coefficients 37 31

/-- Any actual reduction function satisfying the zero and addition laws
commutes with natural scalar multiplication and the executable finite group
law. -/
theorem map_nsmul_finite
    {G : Type*} [AddMonoid G]
    (p A B : ℕ) (red : G → FinitePoint)
    (hzero : red 0 = none)
    (hadd :
      ∀ Q R : G,
        red (Q + R) = finiteAdd p A B (red Q) (red R))
    (Q : G) (n : ℕ) :
    red (n • Q) = finiteMul p A B (red Q) n := by
  induction n with
  | zero =>
      simpa only [zero_nsmul, finiteMul] using hzero
  | succ n ih =>
      rw [succ_nsmul, hadd, ih]
      rfl

/-- Multiplication by twelve kills every point on the plus fibre. -/
theorem plus_all_twelve :
    (finitePoints 37 plusCoefficients.1 plusCoefficients.2).all
      (fun P ↦
        finiteMul 37 plusCoefficients.1 plusCoefficients.2 P 12 == none) =
      true := by
  native_decide

/-- Multiplication by forty-two kills every point on the minus fibre. -/
theorem minus_all_fortyTwo :
    (finitePoints 37 minusCoefficients.1 minusCoefficients.2).all
      (fun P ↦
        finiteMul 37 minusCoefficients.1 minusCoefficients.2 P 42 == none) =
      true := by
  native_decide

/-- The plus `E₁` fibre has 28 points, and multiplication by 28 kills every
point in its exhaustive list. -/
theorem e1Plus_all_twentyEight :
    e1PlusCoefficients = (2, 26) ∧
      (finitePoints 37 e1PlusCoefficients.1 e1PlusCoefficients.2).length =
        28 ∧
      (finitePoints 37 e1PlusCoefficients.1 e1PlusCoefficients.2).all
        (fun P ↦
          finiteMul 37 e1PlusCoefficients.1 e1PlusCoefficients.2 P 28 ==
            none) =
        true := by
  native_decide

/-- The minus `E₁` fibre has 34 points, and multiplication by 34 kills every
point in its exhaustive list. -/
theorem e1Minus_all_thirtyFour :
    e1MinusCoefficients = (2, 15) ∧
      (finitePoints 37 e1MinusCoefficients.1 e1MinusCoefficients.2).length =
        34 ∧
      (finitePoints 37 e1MinusCoefficients.1 e1MinusCoefficients.2).all
        (fun P ↦
          finiteMul 37 e1MinusCoefficients.1 e1MinusCoefficients.2 P 34 ==
            none) =
        true := by
  native_decide

/-- Membership in the exhaustive plus list exposes its exponent
certificate. -/
theorem plus_twelve_eq_none_of_mem
    {P : FinitePoint}
    (hP :
      P ∈ finitePoints 37 plusCoefficients.1 plusCoefficients.2) :
    finiteMul 37 plusCoefficients.1 plusCoefficients.2 P 12 = none := by
  have h :=
    (List.all_eq_true.mp plus_all_twelve) P hP
  simpa only [beq_iff_eq] using h

/-- Membership in the exhaustive minus list exposes its exponent
certificate. -/
theorem minus_fortyTwo_eq_none_of_mem
    {P : FinitePoint}
    (hP :
      P ∈ finitePoints 37 minusCoefficients.1 minusCoefficients.2) :
    finiteMul 37 minusCoefficients.1 minusCoefficients.2 P 42 = none := by
  have h :=
    (List.all_eq_true.mp minus_all_fortyTwo) P hP
  simpa only [beq_iff_eq] using h

/-- Membership in the exhaustive plus `E₁` list exposes its order bound. -/
theorem e1Plus_twentyEight_eq_none_of_mem
    {P : FinitePoint}
    (hP :
      P ∈ finitePoints 37 e1PlusCoefficients.1 e1PlusCoefficients.2) :
    finiteMul 37 e1PlusCoefficients.1 e1PlusCoefficients.2 P 28 = none := by
  have h :=
    (List.all_eq_true.mp e1Plus_all_twentyEight.2.2) P hP
  simpa only [beq_iff_eq] using h

/-- Membership in the exhaustive minus `E₁` list exposes its order bound. -/
theorem e1Minus_thirtyFour_eq_none_of_mem
    {P : FinitePoint}
    (hP :
      P ∈ finitePoints 37 e1MinusCoefficients.1 e1MinusCoefficients.2) :
    finiteMul 37 e1MinusCoefficients.1 e1MinusCoefficients.2 P 34 = none := by
  have h :=
    (List.all_eq_true.mp e1Minus_all_thirtyFour.2.2) P hP
  simpa only [beq_iff_eq] using h

/-- The two split-fibre exponents have gcd six. -/
theorem six_nsmul_eq_zero_of_twelve_and_fortyTwo
    {G : Type*} [AddCommGroup G] (P : G)
    (hTwelve : 12 • P = 0)
    (hFortyTwo : 42 • P = 0) :
    6 • P = 0 := by
  calc
    6 • P = 3 • (12 • P) + 6 • P := by rw [hTwelve, nsmul_zero, zero_add]
    _ = (36 + 6) • P := by rw [add_nsmul, smul_smul]; norm_num
    _ = 42 • P := by norm_num
    _ = 0 := hFortyTwo

/-- The two `E₁` split-fibre order bounds have gcd two. -/
theorem two_nsmul_eq_zero_of_twentyEight_and_thirtyFour
    {G : Type*} [AddCommGroup G] (P : G)
    (hTwentyEight : 28 • P = 0)
    (hThirtyFour : 34 • P = 0) :
    2 • P = 0 := by
  have hSix : 6 • P = 0 := by
    have h := hThirtyFour
    rw [show 34 • P = 28 • P + 6 • P by
      rw [← add_nsmul]] at h
    simpa only [hTwentyEight, zero_add] using h
  have hFour : 4 • P = 0 := by
    have h := hTwentyEight
    rw [show 28 • P = 4 • (6 • P) + 4 • P by
      rw [smul_smul, ← add_nsmul]
      norm_num] at h
    simpa only [hSix, nsmul_zero, zero_add] using h
  have h := hSix
  rw [show 6 • P = 4 • P + 2 • P by
    rw [← add_nsmul]] at h
  simpa only [hFour, zero_add] using h

end GaussianFiniteExponent
end Cuboid2
