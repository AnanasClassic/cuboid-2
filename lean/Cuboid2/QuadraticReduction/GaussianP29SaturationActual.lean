import Cuboid2.QuadraticReduction.GaussianIndexIndependent
import Cuboid2.QuadraticReduction.GaussianSaturationFinite
import Cuboid2.QuadraticReduction.GaussianSaturationBridge
import Cuboid2.QuadraticReduction.GaussianFraction
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Actual seven-saturation of the visible Gaussian point

This module uses the split Gaussian prime `i ↦ 12 (mod 29)`.  The local
certificate is expressed by the standard seventh-division abscissa
polynomial.  A denominator-free weighted addition chain connects that
polynomial to the actual affine group law.
-/

namespace Cuboid2
namespace GaussianP29SaturationActual

noncomputable section

open scoped Polynomial
open GaussianDescent GaussianFraction GaussianIndexIndependent
  GaussianSaturationBridge

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

/-! ## The split residue map -/

/-- The split Gaussian prime above `29`, characterized by `i ↦ 12`. -/
def residueHom29 : GaussianInt →+* ZMod 29 :=
  Zsqrtd.lift
    ⟨12, by native_decide⟩

@[simp] theorem residueHom29_apply (z : GaussianInt) :
    residueHom29 z =
      (z.re : ZMod 29) + (z.im : ZMod 29) * 12 := by
  rfl

/-- Integral coefficients of the displayed `E₀` model. -/
def e0AInt : GaussianInt := ⟨0, 2⟩

def e0BInt : GaussianInt := ⟨-2, -4⟩

@[simp] theorem algebraMap_e0AInt :
    algebraMap GaussianInt GaussianRat e0AInt = E0A := by
  rw [algebraMap_gaussianInt_apply]
  apply QuadraticAlgebra.ext <;>
    norm_num [e0AInt, E0A, gaussianI,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

@[simp] theorem algebraMap_e0BInt :
    algebraMap GaussianInt GaussianRat e0BInt = E0B := by
  rw [algebraMap_gaussianInt_apply]
  apply QuadraticAlgebra.ext <;>
    norm_num [e0BInt, E0B, gaussianI,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

/-! ## Computable seventh-division polynomials -/

section DivisionPolynomials

variable {R : Type*} [CommRing R]

/-- The square of the second division polynomial on
`y² = x³ + A x² + B x`. -/
def psiTwoSq (A B : R) : R[X] :=
  4 * Polynomial.X ^ 3 +
    Polynomial.C (4 * A) * Polynomial.X ^ 2 +
    Polynomial.C (4 * B) * Polynomial.X

/-- The third division polynomial. -/
def psiThree (A B : R) : R[X] :=
  3 * Polynomial.X ^ 4 +
    Polynomial.C (4 * A) * Polynomial.X ^ 3 +
    Polynomial.C (6 * B) * Polynomial.X ^ 2 -
    Polynomial.C (B ^ 2)

/-- The factor of the fourth division polynomial left after removing
`2y`. -/
def prePsiFour (A B : R) : R[X] :=
  2 * Polynomial.X ^ 6 +
    Polynomial.C (4 * A) * Polynomial.X ^ 5 +
    Polynomial.C (10 * B) * Polynomial.X ^ 4 -
    Polynomial.C (10 * B ^ 2) * Polynomial.X ^ 2 -
    Polynomial.C (4 * A * B ^ 2) * Polynomial.X -
    Polynomial.C (2 * B ^ 3)

def prePsiFive (A B : R) : R[X] :=
  prePsiFour A B * psiTwoSq A B ^ 2 -
    psiThree A B ^ 3

def prePsiSix (A B : R) : R[X] :=
  psiThree A B * prePsiFive A B -
    psiThree A B * prePsiFour A B ^ 2

def prePsiSeven (A B : R) : R[X] :=
  prePsiFive A B * psiThree A B ^ 3 -
    prePsiFour A B ^ 3 * psiTwoSq A B ^ 2

def prePsiEight (A B : R) : R[X] :=
  psiThree A B ^ 2 * prePsiFour A B * prePsiSix A B -
    prePsiFour A B * prePsiFive A B ^ 2

/-- `ψ₇²`, which has degree `48`. -/
def psiSevenSq (A B : R) : R[X] :=
  prePsiSeven A B ^ 2

/-- `φ₇`, the numerator of the abscissa of `[7]Q`. -/
def phiSeven (A B : R) : R[X] :=
  Polynomial.X * psiSevenSq A B -
    prePsiEight A B * prePsiSix A B * psiTwoSq A B

/-- The equation forced by `x([7]Q)=2`. -/
def sevenPreimagePolynomial (A B : R) : R[X] :=
  phiSeven A B - 2 * psiSevenSq A B

/-- Scalar evaluator matching `psiTwoSq`. -/
def psiTwoSqValue (A B x : R) : R :=
  4 * x ^ 3 + 4 * A * x ^ 2 + 4 * B * x

def psiThreeValue (A B x : R) : R :=
  3 * x ^ 4 + 4 * A * x ^ 3 + 6 * B * x ^ 2 - B ^ 2

def prePsiFourValue (A B x : R) : R :=
  2 * x ^ 6 + 4 * A * x ^ 5 + 10 * B * x ^ 4 -
    10 * B ^ 2 * x ^ 2 - 4 * A * B ^ 2 * x - 2 * B ^ 3

def prePsiFiveValue (A B x : R) : R :=
  prePsiFourValue A B x * psiTwoSqValue A B x ^ 2 -
    psiThreeValue A B x ^ 3

def prePsiSixValue (A B x : R) : R :=
  psiThreeValue A B x * prePsiFiveValue A B x -
    psiThreeValue A B x * prePsiFourValue A B x ^ 2

def prePsiSevenValue (A B x : R) : R :=
  prePsiFiveValue A B x * psiThreeValue A B x ^ 3 -
    prePsiFourValue A B x ^ 3 * psiTwoSqValue A B x ^ 2

def prePsiEightValue (A B x : R) : R :=
  psiThreeValue A B x ^ 2 * prePsiFourValue A B x *
      prePsiSixValue A B x -
    prePsiFourValue A B x * prePsiFiveValue A B x ^ 2

def psiSevenSqValue (A B x : R) : R :=
  prePsiSevenValue A B x ^ 2

def phiSevenValue (A B x : R) : R :=
  x * psiSevenSqValue A B x -
    prePsiEightValue A B x * prePsiSixValue A B x *
      psiTwoSqValue A B x

def phiSixValue (A B x : R) : R :=
  x * prePsiSixValue A B x ^ 2 * psiTwoSqValue A B x -
    prePsiSevenValue A B x * prePsiFiveValue A B x

def sevenPreimageValue (A B x : R) : R :=
  phiSevenValue A B x - 2 * psiSevenSqValue A B x

end DivisionPolynomials

/-- The integral Weierstrass model used to compare the computable
recurrences above with Mathlib's division polynomials. -/
def integralCurve {R : Type*} [CommRing R] (A B : R) :
    WeierstrassCurve R where
  a₁ := 0
  a₂ := A
  a₃ := 0
  a₄ := B
  a₆ := 0

@[simp] theorem integralCurve_a₁ {R : Type*} [CommRing R] (A B : R) :
    (integralCurve A B).a₁ = 0 := rfl

@[simp] theorem integralCurve_a₂ {R : Type*} [CommRing R] (A B : R) :
    (integralCurve A B).a₂ = A := rfl

@[simp] theorem integralCurve_a₃ {R : Type*} [CommRing R] (A B : R) :
    (integralCurve A B).a₃ = 0 := rfl

@[simp] theorem integralCurve_a₄ {R : Type*} [CommRing R] (A B : R) :
    (integralCurve A B).a₄ = B := rfl

@[simp] theorem integralCurve_a₆ {R : Type*} [CommRing R] (A B : R) :
    (integralCurve A B).a₆ = 0 := rfl

@[simp] theorem integralCurve_e0_eq :
    integralCurve E0A E0B = gaussianE0 := by
  calc
    integralCurve E0A E0B = curve E0A E0B := rfl
    _ = gaussianE0 := gaussianE0_eq_curve.symm

theorem psiTwoSq_eq_divisionPolynomial
    {R : Type*} [CommRing R] (A B : R) :
    psiTwoSq A B = (integralCurve A B).Ψ₂Sq := by
  simp only [psiTwoSq, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    integralCurve_a₁, integralCurve_a₂, integralCurve_a₃,
    integralCurve_a₄, integralCurve_a₆]
  ring_nf
  simp [Polynomial.C_ofNat]

theorem psiThree_eq_divisionPolynomial
    {R : Type*} [CommRing R] (A B : R) :
    psiThree A B = (integralCurve A B).Ψ₃ := by
  simp only [psiThree, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, integralCurve_a₁, integralCurve_a₂,
    integralCurve_a₃, integralCurve_a₄, integralCurve_a₆]
  ring_nf
  simp [Polynomial.C_ofNat]
  ring

theorem prePsiFour_eq_divisionPolynomial
    {R : Type*} [CommRing R] (A B : R) :
    prePsiFour A B = (integralCurve A B).preΨ₄ := by
  simp only [prePsiFour, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, integralCurve_a₁, integralCurve_a₂,
    integralCurve_a₃, integralCurve_a₄, integralCurve_a₆]
  ring_nf
  simp [Polynomial.C_ofNat]
  ring

theorem prePsiFive_eq_divisionPolynomial
    {R : Type*} [CommRing R] (A B : R) :
    prePsiFive A B = (integralCurve A B).preΨ 5 := by
  rw [show (5 : ℤ) = 2 * 2 + 1 by norm_num,
    WeierstrassCurve.preΨ_odd]
  norm_num
  simp only [prePsiFive, WeierstrassCurve.preΨ_four,
    WeierstrassCurve.preΨ_two, WeierstrassCurve.preΨ_one,
    WeierstrassCurve.preΨ_three, if_pos (show Even (2 : ℤ) by decide),
    pow_one, one_mul, psiTwoSq_eq_divisionPolynomial,
    psiThree_eq_divisionPolynomial, prePsiFour_eq_divisionPolynomial]

theorem prePsiSix_eq_divisionPolynomial
    {R : Type*} [CommRing R] (A B : R) :
    prePsiSix A B = (integralCurve A B).preΨ 6 := by
  rw [show (6 : ℤ) = 2 * 3 by norm_num,
    WeierstrassCurve.preΨ_even]
  norm_num
  simp only [prePsiSix, WeierstrassCurve.preΨ_two,
    WeierstrassCurve.preΨ_three, WeierstrassCurve.preΨ_one,
    WeierstrassCurve.preΨ_four, pow_two, one_mul,
    psiThree_eq_divisionPolynomial, prePsiFour_eq_divisionPolynomial,
    prePsiFive_eq_divisionPolynomial]

theorem prePsiSeven_eq_divisionPolynomial
    {R : Type*} [CommRing R] (A B : R) :
    prePsiSeven A B = (integralCurve A B).preΨ 7 := by
  rw [show (7 : ℤ) = 2 * 3 + 1 by norm_num,
    WeierstrassCurve.preΨ_odd]
  norm_num
  simp only [prePsiSeven, WeierstrassCurve.preΨ_two,
    WeierstrassCurve.preΨ_three, WeierstrassCurve.preΨ_four,
    if_neg (show ¬Even (3 : ℤ) by decide), mul_one, one_mul,
    psiTwoSq_eq_divisionPolynomial, psiThree_eq_divisionPolynomial,
    prePsiFour_eq_divisionPolynomial, prePsiFive_eq_divisionPolynomial]

theorem prePsiEight_eq_divisionPolynomial
    {R : Type*} [CommRing R] (A B : R) :
    prePsiEight A B = (integralCurve A B).preΨ 8 := by
  rw [show (8 : ℤ) = 2 * 4 by norm_num,
    WeierstrassCurve.preΨ_even]
  norm_num
  simp only [prePsiEight, WeierstrassCurve.preΨ_two,
    WeierstrassCurve.preΨ_three, WeierstrassCurve.preΨ_four,
    one_mul, psiThree_eq_divisionPolynomial,
    prePsiFour_eq_divisionPolynomial, prePsiFive_eq_divisionPolynomial,
    prePsiSix_eq_divisionPolynomial]

theorem psiSevenSq_eq_divisionPolynomial
    {R : Type*} [CommRing R] (A B : R) :
    psiSevenSq A B = (integralCurve A B).ΨSq 7 := by
  simp only [psiSevenSq, WeierstrassCurve.ΨSq,
    if_neg (show ¬Even (7 : ℤ) by decide), mul_one,
    prePsiSeven_eq_divisionPolynomial]

theorem phiSeven_eq_divisionPolynomial
    {R : Type*} [CommRing R] (A B : R) :
    phiSeven A B = (integralCurve A B).Φ 7 := by
  simp only [phiSeven, WeierstrassCurve.Φ,
    if_neg (show ¬Even (7 : ℤ) by decide), mul_one,
    psiTwoSq_eq_divisionPolynomial, psiSevenSq_eq_divisionPolynomial,
    prePsiSix_eq_divisionPolynomial, prePsiEight_eq_divisionPolynomial]
  ring

/-- The split-`29` certificate has no possible residue abscissa for a
seventh root of `(2,2)`. -/
theorem p29_sevenPreimagePolynomial_no_root :
    ∀ x : ZMod 29,
      sevenPreimageValue 24 8 x ≠ 0 := by
  native_decide

/-- The seventh-preimage polynomial is monic, so every Gaussian-rational
root is a Gaussian integer. -/
theorem sevenPreimagePolynomial_monic :
    (sevenPreimagePolynomial e0AInt e0BInt).Monic := by
  rw [sevenPreimagePolynomial, phiSeven_eq_divisionPolynomial,
    psiSevenSq_eq_divisionPolynomial]
  apply Polynomial.Monic.sub_of_left
  · exact (integralCurve e0AInt e0BInt).leadingCoeff_Φ 7
  · have htwo : (2 : GaussianInt[X]) ≠ 0 := by norm_num
    have hpsi :
        (integralCurve e0AInt e0BInt).ΨSq 7 ≠ 0 :=
      (integralCurve e0AInt e0BInt).ΨSq_ne_zero
        (by norm_num : (7 : GaussianInt) ≠ 0)
    have hmul :
        (2 : GaussianInt[X]) *
            (integralCurve e0AInt e0BInt).ΨSq 7 ≠ 0 :=
      mul_ne_zero htwo hpsi
    have hphi :
        (integralCurve e0AInt e0BInt).Φ 7 ≠ 0 :=
      (integralCurve e0AInt e0BInt).Φ_ne_zero 7
    have hnat :
        ((2 : GaussianInt[X]) *
            (integralCurve e0AInt e0BInt).ΨSq 7).natDegree <
          ((integralCurve e0AInt e0BInt).Φ 7).natDegree := by
      calc
        ((2 : GaussianInt[X]) *
            (integralCurve e0AInt e0BInt).ΨSq 7).natDegree
            ≤ ((integralCurve e0AInt e0BInt).ΨSq 7).natDegree := by
              simpa only [← Polynomial.C_ofNat] using
                Polynomial.natDegree_C_mul_le (2 : GaussianInt)
                  ((integralCurve e0AInt e0BInt).ΨSq 7)
        _ ≤ (7 : ℤ).natAbs ^ 2 - 1 :=
          (integralCurve e0AInt e0BInt).natDegree_ΨSq_le 7
        _ < (7 : ℤ).natAbs ^ 2 := by norm_num
        _ = ((integralCurve e0AInt e0BInt).Φ 7).natDegree := by
          symm
          exact (integralCurve e0AInt e0BInt).natDegree_Φ 7
    rw [Polynomial.degree_eq_natDegree hmul,
      Polynomial.degree_eq_natDegree hphi]
    exact_mod_cast hnat

/-! ## A denominator-free weighted addition chain -/

structure WeightedPoint (R : Type*) where
  X : R
  Y : R
  Z : R

variable {R : Type*} [CommRing R]

def weightedDouble (A B : R) (P : WeightedPoint R) :
    WeightedPoint R :=
  let M :=
    3 * P.X ^ 2 + 2 * A * P.X * P.Z ^ 2 + B * P.Z ^ 4
  let X :=
    M ^ 2 - (A * P.Z ^ 2 + 2 * P.X) * (2 * P.Y) ^ 2
  let Y :=
    M * (4 * P.Y ^ 2 * P.X - X) - 8 * P.Y ^ 4
  let Z := 2 * P.Y * P.Z
  ⟨X, Y, Z⟩

def weightedAddBase
    (A : R) (x y : R) (P : WeightedPoint R) :
    WeightedPoint R :=
  let E := P.X - x * P.Z ^ 2
  let N := P.Y - y * P.Z ^ 3
  let D := P.Z * E
  let X := N ^ 2 - (A + x) * D ^ 2 - P.X * E ^ 2
  let Y := -N * (X - P.X * E ^ 2) - P.Y * E ^ 3
  ⟨X, Y, D⟩

def weightedOne (x y : R) : WeightedPoint R := ⟨x, y, 1⟩

def weightedTwo (A B x y : R) : WeightedPoint R :=
  weightedDouble A B (weightedOne x y)

def weightedThree (A B x y : R) : WeightedPoint R :=
  weightedAddBase A x y (weightedTwo A B x y)

def weightedSix (A B x y : R) : WeightedPoint R :=
  weightedDouble A B (weightedThree A B x y)

def weightedSeven (A B x y : R) : WeightedPoint R :=
  weightedAddBase A x y (weightedSix A B x y)

/-! The first identities in the denominator-free chain.  Keeping these
steps separate is substantially cheaper for the kernel than normalizing the
whole `[7]` formula at once. -/

theorem weightedTwo_Z_sq
    (A B x y : R)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x) :
    (weightedTwo A B x y).Z ^ 2 = psiTwoSqValue A B x := by
  simp only [weightedTwo, weightedDouble, weightedOne, psiTwoSqValue]
  rw [show (2 * y * 1) ^ 2 = 4 * y ^ 2 by ring, hcurve]
  ring

theorem weightedTwo_X
    (A B x y : R)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x) :
    (weightedTwo A B x y).X =
      x * psiTwoSqValue A B x - psiThreeValue A B x := by
  simp only [weightedTwo, weightedDouble, weightedOne,
    psiTwoSqValue, psiThreeValue]
  rw [show (2 * y) ^ 2 = 4 * y ^ 2 by ring, hcurve]
  ring

theorem weightedTwo_base_difference
    (A B x y : R)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x) :
    (weightedTwo A B x y).X -
        x * (weightedTwo A B x y).Z ^ 2 =
      -psiThreeValue A B x := by
  rw [weightedTwo_X A B x y hcurve,
    weightedTwo_Z_sq A B x y hcurve]
  ring

theorem weightedTwo_base_numerator
    (A B x y : R)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x) :
    (weightedTwo A B x y).Y -
        y * (weightedTwo A B x y).Z ^ 3 =
      (3 * x ^ 2 + 2 * A * x + B) *
          psiThreeValue A B x -
        psiTwoSqValue A B x ^ 2 := by
  have hx := weightedTwo_X A B x y hcurve
  have hq :
      psiTwoSqValue A B x = 4 * y ^ 2 := by
    rw [hcurve]
    simp only [psiTwoSqValue]
    ring
  dsimp only [weightedTwo, weightedDouble, weightedOne] at hx ⊢
  rw [hx, hq]
  ring

theorem weightedThree_Z
    (A B x y : R)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x) :
    (weightedThree A B x y).Z =
      -(2 * y * psiThreeValue A B x) := by
  simp only [weightedThree, weightedAddBase]
  rw [weightedTwo_base_difference A B x y hcurve]
  simp only [weightedTwo, weightedDouble, weightedOne]
  ring

theorem weightedThree_X
    (A B x y : R)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x) :
    (weightedThree A B x y).X =
      psiTwoSqValue A B x *
        (x * psiThreeValue A B x ^ 2 -
          prePsiFourValue A B x * psiTwoSqValue A B x) := by
  simp only [weightedThree, weightedAddBase]
  rw [weightedTwo_base_numerator A B x y hcurve,
    weightedTwo_base_difference A B x y hcurve,
    weightedTwo_X A B x y hcurve]
  have hZsq := weightedTwo_Z_sq A B x y hcurve
  calc
    ((3 * x ^ 2 + 2 * A * x + B) *
              psiThreeValue A B x -
            psiTwoSqValue A B x ^ 2) ^ 2 -
          (A + x) *
              ((weightedTwo A B x y).Z *
                -psiThreeValue A B x) ^ 2 -
        (x * psiTwoSqValue A B x -
            psiThreeValue A B x) *
          (-psiThreeValue A B x) ^ 2 =
        ((3 * x ^ 2 + 2 * A * x + B) *
              psiThreeValue A B x -
            psiTwoSqValue A B x ^ 2) ^ 2 -
          (A + x) * (weightedTwo A B x y).Z ^ 2 *
              psiThreeValue A B x ^ 2 -
          (x * psiTwoSqValue A B x -
              psiThreeValue A B x) *
            psiThreeValue A B x ^ 2 := by ring
    _ =
        ((3 * x ^ 2 + 2 * A * x + B) *
              psiThreeValue A B x -
            psiTwoSqValue A B x ^ 2) ^ 2 -
          (A + x) * psiTwoSqValue A B x *
              psiThreeValue A B x ^ 2 -
          (x * psiTwoSqValue A B x -
              psiThreeValue A B x) *
            psiThreeValue A B x ^ 2 := by rw [hZsq]
    _ =
        psiTwoSqValue A B x *
          (x * psiThreeValue A B x ^ 2 -
            prePsiFourValue A B x *
              psiTwoSqValue A B x) := by
      simp only [psiTwoSqValue, psiThreeValue, prePsiFourValue]
      ring

theorem weightedTwo_Y_twice
    (A B x y : R)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x) :
    2 * (weightedTwo A B x y).Y =
      2 * (3 * x ^ 2 + 2 * A * x + B) *
          psiThreeValue A B x -
        psiTwoSqValue A B x ^ 2 := by
  have hn := weightedTwo_base_numerator A B x y hcurve
  have htail :
      2 * y * (weightedTwo A B x y).Z ^ 3 =
        psiTwoSqValue A B x ^ 2 := by
    have hq :
        psiTwoSqValue A B x = 4 * y ^ 2 := by
      rw [hcurve]
      simp only [psiTwoSqValue]
      ring
    rw [hq]
    simp only [weightedTwo, weightedDouble, weightedOne]
    ring
  calc
    2 * (weightedTwo A B x y).Y =
        2 *
            ((weightedTwo A B x y).Y -
              y * (weightedTwo A B x y).Z ^ 3) +
          2 * y * (weightedTwo A B x y).Z ^ 3 := by ring
    _ =
        2 *
            ((3 * x ^ 2 + 2 * A * x + B) *
                psiThreeValue A B x -
              psiTwoSqValue A B x ^ 2) +
          psiTwoSqValue A B x ^ 2 := by rw [hn, htail]
    _ =
        2 * (3 * x ^ 2 + 2 * A * x + B) *
            psiThreeValue A B x -
          psiTwoSqValue A B x ^ 2 := by ring

theorem weightedThree_Y_relation
    (A B x y : R)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x) :
    2 * psiThreeValue A B x *
        (weightedThree A B x y).Y =
      -(psiTwoSqValue A B x ^ 2 *
          prePsiSixValue A B x) := by
  have hYdef :
      (weightedThree A B x y).Y =
        -((weightedTwo A B x y).Y -
              y * (weightedTwo A B x y).Z ^ 3) *
            ((weightedThree A B x y).X -
              (weightedTwo A B x y).X *
                ((weightedTwo A B x y).X -
                    x * (weightedTwo A B x y).Z ^ 2) ^ 2) -
          (weightedTwo A B x y).Y *
            ((weightedTwo A B x y).X -
                x * (weightedTwo A B x y).Z ^ 2) ^ 3 := by
    rfl
  rw [hYdef]
  rw [weightedTwo_base_numerator A B x y hcurve,
    weightedTwo_base_difference A B x y hcurve,
    weightedThree_X A B x y hcurve,
    weightedTwo_X A B x y hcurve]
  have hY2 := weightedTwo_Y_twice A B x y hcurve
  calc
    2 * psiThreeValue A B x *
          (-((3 * x ^ 2 + 2 * A * x + B) *
                  psiThreeValue A B x -
                psiTwoSqValue A B x ^ 2) *
              (psiTwoSqValue A B x *
                    (x * psiThreeValue A B x ^ 2 -
                      prePsiFourValue A B x *
                        psiTwoSqValue A B x) -
                (x * psiTwoSqValue A B x -
                    psiThreeValue A B x) *
                  (-psiThreeValue A B x) ^ 2) -
            (weightedTwo A B x y).Y *
              (-psiThreeValue A B x) ^ 3) =
        -2 * psiThreeValue A B x *
            ((3 * x ^ 2 + 2 * A * x + B) *
                  psiThreeValue A B x -
                psiTwoSqValue A B x ^ 2) *
              (psiTwoSqValue A B x *
                    (x * psiThreeValue A B x ^ 2 -
                      prePsiFourValue A B x *
                        psiTwoSqValue A B x) -
                (x * psiTwoSqValue A B x -
                    psiThreeValue A B x) *
                  psiThreeValue A B x ^ 2) +
          (2 * (weightedTwo A B x y).Y) *
            psiThreeValue A B x ^ 4 := by ring
    _ =
        -2 * psiThreeValue A B x *
            ((3 * x ^ 2 + 2 * A * x + B) *
                  psiThreeValue A B x -
                psiTwoSqValue A B x ^ 2) *
              (psiTwoSqValue A B x *
                    (x * psiThreeValue A B x ^ 2 -
                      prePsiFourValue A B x *
                        psiTwoSqValue A B x) -
                (x * psiTwoSqValue A B x -
                    psiThreeValue A B x) *
                  psiThreeValue A B x ^ 2) +
          (2 * (3 * x ^ 2 + 2 * A * x + B) *
                psiThreeValue A B x -
              psiTwoSqValue A B x ^ 2) *
            psiThreeValue A B x ^ 4 := by rw [hY2]
    _ =
        -(psiTwoSqValue A B x ^ 2 *
            prePsiSixValue A B x) := by
      simp only [psiTwoSqValue, psiThreeValue,
        prePsiFourValue, prePsiFiveValue, prePsiSixValue]
      ring

theorem weightedSix_Z
    (A B x y : R)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x) :
    (weightedSix A B x y).Z =
      2 * y * psiTwoSqValue A B x ^ 2 *
        prePsiSixValue A B x := by
  change
    2 * (weightedThree A B x y).Y *
        (weightedThree A B x y).Z =
      2 * y * psiTwoSqValue A B x ^ 2 *
        prePsiSixValue A B x
  rw [weightedThree_Z A B x y hcurve]
  have hyrel := weightedThree_Y_relation A B x y hcurve
  calc
    2 * (weightedThree A B x y).Y *
          -(2 * y * psiThreeValue A B x) =
        -2 * y *
          (2 * psiThreeValue A B x *
            (weightedThree A B x y).Y) := by ring
    _ =
        -2 * y *
          (-(psiTwoSqValue A B x ^ 2 *
            prePsiSixValue A B x)) := by rw [hyrel]
    _ =
        2 * y * psiTwoSqValue A B x ^ 2 *
          prePsiSixValue A B x := by ring

theorem weightedThree_Z_sq
    (A B x y : R)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x) :
    (weightedThree A B x y).Z ^ 2 =
      psiTwoSqValue A B x *
        psiThreeValue A B x ^ 2 := by
  rw [weightedThree_Z A B x y hcurve]
  have hq :
      psiTwoSqValue A B x = 4 * y ^ 2 := by
    rw [hcurve]
    simp only [psiTwoSqValue]
    ring
  rw [hq]
  ring

theorem weightedSix_X_cross
    (A B x y : R)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x) :
    psiThreeValue A B x ^ 2 *
        (weightedSix A B x y).X =
      psiThreeValue A B x ^ 2 *
        (psiTwoSqValue A B x ^ 4 *
          phiSixValue A B x) := by
  have hx3 := weightedThree_X A B x y hcurve
  have hz3 := weightedThree_Z_sq A B x y hcurve
  have hy3 := weightedThree_Y_relation A B x y hcurve
  have hy3sq :
      psiThreeValue A B x ^ 2 *
          (2 * (weightedThree A B x y).Y) ^ 2 =
        psiTwoSqValue A B x ^ 4 *
          prePsiSixValue A B x ^ 2 := by
    calc
      psiThreeValue A B x ^ 2 *
          (2 * (weightedThree A B x y).Y) ^ 2 =
        (2 * psiThreeValue A B x *
            (weightedThree A B x y).Y) ^ 2 := by ring
      _ =
        (-(psiTwoSqValue A B x ^ 2 *
            prePsiSixValue A B x)) ^ 2 := by rw [hy3]
      _ =
        psiTwoSqValue A B x ^ 4 *
          prePsiSixValue A B x ^ 2 := by ring
  change
    psiThreeValue A B x ^ 2 *
        ((3 * (weightedThree A B x y).X ^ 2 +
              2 * A * (weightedThree A B x y).X *
                (weightedThree A B x y).Z ^ 2 +
              B * (weightedThree A B x y).Z ^ 4) ^ 2 -
          (A * (weightedThree A B x y).Z ^ 2 +
              2 * (weightedThree A B x y).X) *
            (2 * (weightedThree A B x y).Y) ^ 2) =
      psiThreeValue A B x ^ 2 *
        (psiTwoSqValue A B x ^ 4 *
          phiSixValue A B x)
  rw [show (weightedThree A B x y).Z ^ 4 =
    ((weightedThree A B x y).Z ^ 2) ^ 2 by ring]
  rw [hx3, hz3]
  calc
    psiThreeValue A B x ^ 2 *
          ((3 *
                  (psiTwoSqValue A B x *
                    (x * psiThreeValue A B x ^ 2 -
                      prePsiFourValue A B x *
                        psiTwoSqValue A B x)) ^ 2 +
                2 * A *
                    (psiTwoSqValue A B x *
                      (x * psiThreeValue A B x ^ 2 -
                        prePsiFourValue A B x *
                          psiTwoSqValue A B x)) *
                  (psiTwoSqValue A B x *
                    psiThreeValue A B x ^ 2) +
                B *
                  (psiTwoSqValue A B x *
                    psiThreeValue A B x ^ 2) ^ 2) ^ 2 -
            (A *
                  (psiTwoSqValue A B x *
                    psiThreeValue A B x ^ 2) +
                2 *
                  (psiTwoSqValue A B x *
                    (x * psiThreeValue A B x ^ 2 -
                      prePsiFourValue A B x *
                        psiTwoSqValue A B x))) *
              (2 * (weightedThree A B x y).Y) ^ 2) =
        psiThreeValue A B x ^ 2 *
            (psiTwoSqValue A B x ^ 4 *
              (3 *
                    (x * psiThreeValue A B x ^ 2 -
                      prePsiFourValue A B x *
                        psiTwoSqValue A B x) ^ 2 +
                  2 * A *
                    (x * psiThreeValue A B x ^ 2 -
                      prePsiFourValue A B x *
                        psiTwoSqValue A B x) *
                    psiThreeValue A B x ^ 2 +
                  B * psiThreeValue A B x ^ 4) ^ 2) -
          (psiTwoSqValue A B x *
              (A * psiThreeValue A B x ^ 2 +
                2 *
                  (x * psiThreeValue A B x ^ 2 -
                    prePsiFourValue A B x *
                      psiTwoSqValue A B x))) *
            (psiThreeValue A B x ^ 2 *
              (2 * (weightedThree A B x y).Y) ^ 2) := by
          ring
    _ =
        psiThreeValue A B x ^ 2 *
            (psiTwoSqValue A B x ^ 4 *
              (3 *
                    (x * psiThreeValue A B x ^ 2 -
                      prePsiFourValue A B x *
                        psiTwoSqValue A B x) ^ 2 +
                  2 * A *
                    (x * psiThreeValue A B x ^ 2 -
                      prePsiFourValue A B x *
                        psiTwoSqValue A B x) *
                    psiThreeValue A B x ^ 2 +
                  B * psiThreeValue A B x ^ 4) ^ 2) -
          (psiTwoSqValue A B x *
              (A * psiThreeValue A B x ^ 2 +
                2 *
                  (x * psiThreeValue A B x ^ 2 -
                    prePsiFourValue A B x *
                      psiTwoSqValue A B x))) *
            (psiTwoSqValue A B x ^ 4 *
              prePsiSixValue A B x ^ 2) := by rw [hy3sq]
    _ =
        psiThreeValue A B x ^ 2 *
          (psiTwoSqValue A B x ^ 4 *
            phiSixValue A B x) := by
      simp only [psiTwoSqValue, psiThreeValue,
        prePsiFourValue, prePsiFiveValue, prePsiSixValue,
        prePsiSevenValue, phiSixValue]
      ring

theorem weightedSix_Y_cross
    (A B x y : R)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x) :
    psiThreeValue A B x ^ 4 *
        (2 * (weightedSix A B x y).Y) =
      psiThreeValue A B x ^ 4 *
        (psiTwoSqValue A B x ^ 6 *
          (prePsiEightValue A B x *
              prePsiFiveValue A B x ^ 2 -
            prePsiFourValue A B x *
              prePsiSevenValue A B x ^ 2)) := by
  let q := psiTwoSqValue A B x
  let r := psiThreeValue A B x
  let s := prePsiFourValue A B x
  let t := prePsiFiveValue A B x
  let u := prePsiSixValue A B x
  let v := prePsiSevenValue A B x
  let w := prePsiEightValue A B x
  let f := x * r ^ 2 - s * q
  let g := phiSixValue A B x
  let m := 3 * f ^ 2 + 2 * A * f * r ^ 2 + B * r ^ 4
  let P3 := weightedThree A B x y
  let P6 := weightedSix A B x y
  have hx3 : P3.X = q * f := by
    dsimp only [P3, q, f, r, s]
    exact weightedThree_X A B x y hcurve
  have hz3 : P3.Z ^ 2 = q * r ^ 2 := by
    dsimp only [P3, q, r]
    exact weightedThree_Z_sq A B x y hcurve
  have hy3 := weightedThree_Y_relation A B x y hcurve
  have hy3sq :
      r ^ 2 * (2 * P3.Y) ^ 2 = q ^ 4 * u ^ 2 := by
    dsimp only [P3, q, r, u]
    calc
      psiThreeValue A B x ^ 2 *
          (2 * (weightedThree A B x y).Y) ^ 2 =
        (2 * psiThreeValue A B x *
            (weightedThree A B x y).Y) ^ 2 := by ring
      _ =
        (-(psiTwoSqValue A B x ^ 2 *
            prePsiSixValue A B x)) ^ 2 := by rw [hy3]
      _ =
        psiTwoSqValue A B x ^ 4 *
          prePsiSixValue A B x ^ 2 := by ring
  have hx6 := weightedSix_X_cross A B x y hcurve
  have hx6' : r ^ 2 * P6.X = r ^ 2 * (q ^ 4 * g) := by
    dsimp only [P6, q, r, g]
    exact hx6
  have hm :
      3 * P3.X ^ 2 + 2 * A * P3.X * P3.Z ^ 2 +
          B * P3.Z ^ 4 =
        q ^ 2 * m := by
    rw [show P3.Z ^ 4 = (P3.Z ^ 2) ^ 2 by ring, hx3, hz3]
    dsimp only [m]
    ring
  have hterm :
      r ^ 4 * ((2 * P3.Y) ^ 2 * P3.X - P6.X) =
        q ^ 5 * r ^ 2 * u ^ 2 * f -
          r ^ 4 * q ^ 4 * g := by
    calc
      r ^ 4 * ((2 * P3.Y) ^ 2 * P3.X - P6.X) =
          (r ^ 2 * (2 * P3.Y) ^ 2) *
              (r ^ 2 * P3.X) -
            r ^ 2 * (r ^ 2 * P6.X) := by ring
      _ =
          (q ^ 4 * u ^ 2) * (r ^ 2 * (q * f)) -
            r ^ 2 * (r ^ 2 * (q ^ 4 * g)) := by
        rw [hy3sq, hx3, hx6']
      _ =
          q ^ 5 * r ^ 2 * u ^ 2 * f -
            r ^ 4 * q ^ 4 * g := by ring
  have hyfour :
      r ^ 4 * (2 * P3.Y) ^ 4 = q ^ 8 * u ^ 4 := by
    calc
      r ^ 4 * (2 * P3.Y) ^ 4 =
          (r ^ 2 * (2 * P3.Y) ^ 2) ^ 2 := by ring
      _ = (q ^ 4 * u ^ 2) ^ 2 := by rw [hy3sq]
      _ = q ^ 8 * u ^ 4 := by ring
  change
    r ^ 4 *
        (2 *
          ((3 * P3.X ^ 2 + 2 * A * P3.X * P3.Z ^ 2 +
                B * P3.Z ^ 4) *
              (4 * P3.Y ^ 2 * P3.X - P6.X) -
            8 * P3.Y ^ 4)) =
      r ^ 4 * (q ^ 6 * (w * t ^ 2 - s * v ^ 2))
  calc
    r ^ 4 *
          (2 *
            ((3 * P3.X ^ 2 + 2 * A * P3.X * P3.Z ^ 2 +
                  B * P3.Z ^ 4) *
                (4 * P3.Y ^ 2 * P3.X - P6.X) -
              8 * P3.Y ^ 4)) =
        2 *
            (3 * P3.X ^ 2 + 2 * A * P3.X * P3.Z ^ 2 +
              B * P3.Z ^ 4) *
            (r ^ 4 * ((2 * P3.Y) ^ 2 * P3.X - P6.X)) -
          r ^ 4 * (2 * P3.Y) ^ 4 := by ring
    _ =
        2 * (q ^ 2 * m) *
            (q ^ 5 * r ^ 2 * u ^ 2 * f -
              r ^ 4 * q ^ 4 * g) -
          q ^ 8 * u ^ 4 := by rw [hm, hterm, hyfour]
    _ = r ^ 4 * (q ^ 6 * (w * t ^ 2 - s * v ^ 2)) := by
      dsimp only [q, r, s, t, u, v, w, f, g, m]
      simp only [psiTwoSqValue, psiThreeValue,
        prePsiFourValue, prePsiFiveValue, prePsiSixValue,
        prePsiSevenValue, prePsiEightValue, phiSixValue]
      ring

/-- The single low-degree identity among the initial division-polynomial
values needed by the final `6+1` addition step. -/
theorem initialDivisionValue_identity
    (A B x : R) :
    12 * psiThreeValue A B x ^ 2 *
          psiTwoSqValue A B x * x -
        prePsiFourValue A B x ^ 2 -
        2 * psiTwoSqValue A B x ^ 2 *
          prePsiFourValue A B x -
        psiTwoSqValue A B x ^ 4 +
        4 * A * psiThreeValue A B x ^ 2 *
          psiTwoSqValue A B x -
        4 * psiThreeValue A B x ^ 3 = 0 := by
  simp only [psiTwoSqValue, psiThreeValue, prePsiFourValue]
  ring

/-- The final EDS recurrence identity, isolated from the concrete initial
polynomials so `ring` only sees five indeterminates. -/
theorem seventhRecurrence_identity
    (A x q r s : R)
    (hbase :
      12 * r ^ 2 * q * x - s ^ 2 - 2 * q ^ 2 * s - q ^ 4 +
          4 * A * r ^ 2 * q - 4 * r ^ 3 = 0) :
    let t := s * q ^ 2 - r ^ 3
    let u := r * t - r * s ^ 2
    let v := t * r ^ 3 - s ^ 3 * q ^ 2
    let w := r ^ 2 * s * u - s * t ^ 2
    let g := x * u ^ 2 * q - v * t
    let n := w * t ^ 2 - s * v ^ 2 - q ^ 2 * u ^ 3
    let p := x * v ^ 2 - w * u * q
    (q ^ 6 * n) ^ 2 -
          4 * (A + x) * (q ^ 5 * u ^ 2) *
            (-(q ^ 4 * v * t)) ^ 2 -
          4 * (q ^ 4 * g) * (-(q ^ 4 * v * t)) ^ 2 =
      4 * (q ^ 13 * t ^ 2 * u ^ 2 * p) := by
  dsimp only
  linear_combination
    -(q ^ 12 * (s * q ^ 2 - r ^ 3) ^ 2 *
      (s ^ 2 - (s * q ^ 2 - r ^ 3)) ^ 2 *
      ((s * q ^ 2 - r ^ 3) * r ^ 3 -
        s ^ 3 * q ^ 2) ^ 2) * hbase

section WeightedSemantics

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

theorem weightedSix_X
    (A B x y : K)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x)
    (hr : psiThreeValue A B x ≠ 0) :
    (weightedSix A B x y).X =
      psiTwoSqValue A B x ^ 4 * phiSixValue A B x := by
  apply mul_left_cancel₀ (pow_ne_zero 2 hr)
  exact weightedSix_X_cross A B x y hcurve

theorem weightedSix_Y_twice
    (A B x y : K)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x)
    (hr : psiThreeValue A B x ≠ 0) :
    2 * (weightedSix A B x y).Y =
      psiTwoSqValue A B x ^ 6 *
        (prePsiEightValue A B x *
            prePsiFiveValue A B x ^ 2 -
          prePsiFourValue A B x *
            prePsiSevenValue A B x ^ 2) := by
  apply mul_left_cancel₀ (pow_ne_zero 4 hr)
  exact weightedSix_Y_cross A B x y hcurve

theorem weightedSix_Z_sq
    (A B x y : K)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x) :
    (weightedSix A B x y).Z ^ 2 =
      psiTwoSqValue A B x ^ 5 *
        prePsiSixValue A B x ^ 2 := by
  rw [weightedSix_Z A B x y hcurve]
  have hq :
      psiTwoSqValue A B x = 4 * y ^ 2 := by
    rw [hcurve]
    simp only [psiTwoSqValue]
    ring
  rw [hq]
  ring

theorem weightedSix_base_difference
    (A B x y : K)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x)
    (hr : psiThreeValue A B x ≠ 0) :
    (weightedSix A B x y).X -
        x * (weightedSix A B x y).Z ^ 2 =
      -(psiTwoSqValue A B x ^ 4 *
          prePsiSevenValue A B x *
          prePsiFiveValue A B x) := by
  rw [weightedSix_X A B x y hcurve hr,
    weightedSix_Z_sq A B x y hcurve]
  simp only [phiSixValue, prePsiSevenValue]
  ring

theorem weightedSix_base_numerator_twice
    (A B x y : K)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x)
    (hr : psiThreeValue A B x ≠ 0) :
    2 *
        ((weightedSix A B x y).Y -
          y * (weightedSix A B x y).Z ^ 3) =
      psiTwoSqValue A B x ^ 6 *
        (prePsiEightValue A B x *
              prePsiFiveValue A B x ^ 2 -
            prePsiFourValue A B x *
              prePsiSevenValue A B x ^ 2 -
            psiTwoSqValue A B x ^ 2 *
              prePsiSixValue A B x ^ 3) := by
  have hy6 := weightedSix_Y_twice A B x y hcurve hr
  have htail :
      2 * y * (weightedSix A B x y).Z ^ 3 =
        psiTwoSqValue A B x ^ 8 *
          prePsiSixValue A B x ^ 3 := by
    rw [weightedSix_Z A B x y hcurve]
    have hq :
        psiTwoSqValue A B x = 4 * y ^ 2 := by
      rw [hcurve]
      simp only [psiTwoSqValue]
      ring
    rw [hq]
    ring
  calc
    2 *
          ((weightedSix A B x y).Y -
            y * (weightedSix A B x y).Z ^ 3) =
        2 * (weightedSix A B x y).Y -
          2 * y * (weightedSix A B x y).Z ^ 3 := by ring
    _ =
        psiTwoSqValue A B x ^ 6 *
            (prePsiEightValue A B x *
                prePsiFiveValue A B x ^ 2 -
              prePsiFourValue A B x *
                prePsiSevenValue A B x ^ 2) -
          psiTwoSqValue A B x ^ 8 *
            prePsiSixValue A B x ^ 3 := by rw [hy6, htail]
    _ =
        psiTwoSqValue A B x ^ 6 *
          (prePsiEightValue A B x *
                prePsiFiveValue A B x ^ 2 -
              prePsiFourValue A B x *
                prePsiSevenValue A B x ^ 2 -
              psiTwoSqValue A B x ^ 2 *
                prePsiSixValue A B x ^ 3) := by ring

set_option maxHeartbeats 2000000 in
theorem weightedSeven_X
    (A B x y : K)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x)
    (hr : psiThreeValue A B x ≠ 0) :
    (weightedSeven A B x y).X =
      psiTwoSqValue A B x ^ 13 *
        prePsiFiveValue A B x ^ 2 *
        prePsiSixValue A B x ^ 2 *
        phiSevenValue A B x := by
  let q := psiTwoSqValue A B x
  let s := prePsiFourValue A B x
  let t := prePsiFiveValue A B x
  let u := prePsiSixValue A B x
  let v := prePsiSevenValue A B x
  let w := prePsiEightValue A B x
  let g := phiSixValue A B x
  let n := w * t ^ 2 - s * v ^ 2 - q ^ 2 * u ^ 3
  let P6 := weightedSix A B x y
  have hx6 : P6.X = q ^ 4 * g := by
    dsimp only [P6, q, g]
    exact weightedSix_X A B x y hcurve hr
  have hz6 : P6.Z ^ 2 = q ^ 5 * u ^ 2 := by
    dsimp only [P6, q, u]
    exact weightedSix_Z_sq A B x y hcurve
  have he6 : P6.X - x * P6.Z ^ 2 = -(q ^ 4 * v * t) := by
    dsimp only [P6, q, v, t]
    exact weightedSix_base_difference A B x y hcurve hr
  have hn6 :
      2 * (P6.Y - y * P6.Z ^ 3) = q ^ 6 * n := by
    dsimp only [P6, q, s, t, u, v, w, n]
    exact weightedSix_base_numerator_twice A B x y hcurve hr
  change
    (P6.Y - y * P6.Z ^ 3) ^ 2 -
          (A + x) *
            (P6.Z * (P6.X - x * P6.Z ^ 2)) ^ 2 -
          P6.X * (P6.X - x * P6.Z ^ 2) ^ 2 =
      q ^ 13 * t ^ 2 * u ^ 2 * phiSevenValue A B x
  apply mul_left_cancel₀ (show (4 : K) ≠ 0 by norm_num)
  calc
    4 *
          ((P6.Y - y * P6.Z ^ 3) ^ 2 -
            (A + x) *
              (P6.Z * (P6.X - x * P6.Z ^ 2)) ^ 2 -
            P6.X * (P6.X - x * P6.Z ^ 2) ^ 2) =
        (2 * (P6.Y - y * P6.Z ^ 3)) ^ 2 -
          4 * (A + x) * P6.Z ^ 2 *
            (P6.X - x * P6.Z ^ 2) ^ 2 -
          4 * P6.X *
            (P6.X - x * P6.Z ^ 2) ^ 2 := by ring
    _ =
        (q ^ 6 * n) ^ 2 -
          4 * (A + x) * (q ^ 5 * u ^ 2) *
            (-(q ^ 4 * v * t)) ^ 2 -
          4 * (q ^ 4 * g) *
            (-(q ^ 4 * v * t)) ^ 2 := by
      rw [hn6, he6, hz6, hx6]
    _ =
        4 *
          (q ^ 13 * t ^ 2 * u ^ 2 *
            phiSevenValue A B x) := by
      have hbase :
          12 * psiThreeValue A B x ^ 2 *
                psiTwoSqValue A B x * x -
              prePsiFourValue A B x ^ 2 -
              2 * psiTwoSqValue A B x ^ 2 *
                prePsiFourValue A B x -
              psiTwoSqValue A B x ^ 4 +
              4 * A * psiThreeValue A B x ^ 2 *
                psiTwoSqValue A B x -
              4 * psiThreeValue A B x ^ 3 = 0 :=
        initialDivisionValue_identity A B x
      convert
          seventhRecurrence_identity A x
            (psiTwoSqValue A B x) (psiThreeValue A B x)
            (prePsiFourValue A B x) hbase using 1 <;>
        simp only [q, s, t, u, v, w, g, n,
          prePsiFiveValue, prePsiSixValue,
          prePsiSevenValue, prePsiEightValue,
          psiSevenSqValue, phiSixValue, phiSevenValue] <;>
        ring

theorem weightedSeven_Z_sq
    (A B x y : K)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x)
    (hr : psiThreeValue A B x ≠ 0) :
    (weightedSeven A B x y).Z ^ 2 =
      psiTwoSqValue A B x ^ 13 *
        prePsiFiveValue A B x ^ 2 *
        prePsiSixValue A B x ^ 2 *
        psiSevenSqValue A B x := by
  change
    ((weightedSix A B x y).Z *
      ((weightedSix A B x y).X -
        x * (weightedSix A B x y).Z ^ 2)) ^ 2 =
      psiTwoSqValue A B x ^ 13 *
        prePsiFiveValue A B x ^ 2 *
        prePsiSixValue A B x ^ 2 *
        psiSevenSqValue A B x
  rw [weightedSix_base_difference A B x y hcurve hr]
  calc
    ((weightedSix A B x y).Z *
          -(psiTwoSqValue A B x ^ 4 *
            prePsiSevenValue A B x *
            prePsiFiveValue A B x)) ^ 2 =
        (weightedSix A B x y).Z ^ 2 *
          (psiTwoSqValue A B x ^ 4 *
            prePsiSevenValue A B x *
            prePsiFiveValue A B x) ^ 2 := by ring
    _ =
        (psiTwoSqValue A B x ^ 5 *
            prePsiSixValue A B x ^ 2) *
          (psiTwoSqValue A B x ^ 4 *
            prePsiSevenValue A B x *
            prePsiFiveValue A B x) ^ 2 := by
      rw [weightedSix_Z_sq A B x y hcurve]
    _ =
        psiTwoSqValue A B x ^ 13 *
          prePsiFiveValue A B x ^ 2 *
          prePsiSixValue A B x ^ 2 *
          psiSevenSqValue A B x := by
      simp only [psiSevenSqValue]
      ring

theorem weightedSeven_cross
    (A B x y : K)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x)
    (hr : psiThreeValue A B x ≠ 0) :
    (weightedSeven A B x y).X *
        psiSevenSqValue A B x =
      (weightedSeven A B x y).Z ^ 2 *
        phiSevenValue A B x := by
  rw [weightedSeven_X A B x y hcurve hr,
    weightedSeven_Z_sq A B x y hcurve hr]
  ring

/-- A packaged form of `weightedSeven_cross` whose result type only mentions
an abstract weighted point.  This avoids normalizing the full weighted
addition chain when a caller already has a local name for that point. -/
theorem weightedSeven_cross_of_eq
    (A B x y : K) (P : WeightedPoint K)
    (hP : P = weightedSeven A B x y)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x)
    (hr : psiThreeValue A B x ≠ 0) :
    P.X * psiSevenSqValue A B x =
      P.Z ^ 2 * phiSevenValue A B x := by
  subst P
  exact weightedSeven_cross A B x y hcurve hr

set_option maxHeartbeats 1000000 in
/-- A nonzero weighted seventh multiple with abscissa `2` is a root of
the seventh-preimage value polynomial. -/
theorem weightedSeven_value_zero
    (A B x y : K)
    (hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x)
    (hZ : (weightedSeven A B x y).Z ≠ 0)
    (hx :
      (weightedSeven A B x y).X /
          (weightedSeven A B x y).Z ^ 2 = 2) :
    sevenPreimageValue A B x = 0 := by
  have hr : psiThreeValue A B x ≠ 0 := by
    intro hr0
    have hZ3 :
        (weightedThree A B x y).Z = 0 := by
      rw [weightedThree_Z A B x y hcurve, hr0]
      ring
    have hZ6 :
        (weightedSix A B x y).Z = 0 := by
      change
        2 * (weightedThree A B x y).Y *
          (weightedThree A B x y).Z = 0
      rw [hZ3]
      ring
    have hZ7 :
        (weightedSeven A B x y).Z = 0 := by
      change
        (weightedSix A B x y).Z *
          ((weightedSix A B x y).X -
            x * (weightedSix A B x y).Z ^ 2) = 0
      rw [hZ6]
      ring
    exact hZ hZ7
  have hcross := weightedSeven_cross A B x y hcurve hr
  have hX :
      (weightedSeven A B x y).X =
        2 * (weightedSeven A B x y).Z ^ 2 :=
    (div_eq_iff (pow_ne_zero 2 hZ)).mp hx
  rw [hX] at hcross
  have hmul :
      (weightedSeven A B x y).Z ^ 2 *
          sevenPreimageValue A B x = 0 := by
    rw [sevenPreimageValue]
    linear_combination -hcross
  exact
    (mul_eq_zero.mp hmul).resolve_left
      (pow_ne_zero 2 hZ)

/-- Affine abscissa represented by a nonzero weighted denominator. -/
def weightedX (P : WeightedPoint K) : K :=
  P.X / P.Z ^ 2

/-- Affine ordinate represented by a nonzero weighted denominator. -/
def weightedY (P : WeightedPoint K) : K :=
  P.Y / P.Z ^ 3

/-- The denominator-free doubling formula represents actual doubling on
the affine point group. -/
theorem weightedDouble_represents_double
    (A B : K) (P : WeightedPoint K)
    (hZ : P.Z ≠ 0) (hY : P.Y ≠ 0)
    (hpoint :
      (integralCurve A B).toAffine.Nonsingular
        (weightedX P) (weightedY P)) :
    ∃ hdouble :
        (integralCurve A B).toAffine.Nonsingular
          (weightedX (weightedDouble A B P))
          (weightedY (weightedDouble A B P)),
      2 •
          (WeierstrassCurve.Affine.Point.some
            (weightedX P) (weightedY P) hpoint) =
        .some
          (weightedX (weightedDouble A B P))
          (weightedY (weightedDouble A B P)) hdouble := by
  let W := (integralCurve A B).toAffine
  have hyAff : weightedY P ≠ 0 :=
    div_ne_zero hY (pow_ne_zero 3 hZ)
  have hyNeg :
      weightedY P ≠ W.negY (weightedX P) (weightedY P) := by
    dsimp [W, integralCurve]
    simp only [WeierstrassCurve.Affine.negY, zero_mul, sub_zero]
    change weightedY P ≠ -weightedY P
    intro h
    have htwo : (2 : K) * weightedY P = 0 := by
      linear_combination h
    exact hyAff ((mul_eq_zero.mp htwo).resolve_left (by norm_num))
  let slope :=
    W.slope (weightedX P) (weightedX P)
      (weightedY P) (weightedY P)
  have hslope :
      slope =
        (3 * weightedX P ^ 2 +
            2 * A * weightedX P + B) /
          (2 * weightedY P) := by
    dsimp [slope]
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyNeg]
    simp only [W, integralCurve, WeierstrassCurve.Affine.negY,
      zero_mul, sub_zero]
    change
      (3 * weightedX P ^ 2 +
          2 * A * weightedX P + B) /
          (weightedY P - -weightedY P) =
        (3 * weightedX P ^ 2 +
          2 * A * weightedX P + B) /
          (2 * weightedY P)
    ring
  have hx :
      W.addX (weightedX P) (weightedX P) slope =
        weightedX (weightedDouble A B P) := by
    rw [hslope]
    simp only [W, integralCurve, WeierstrassCurve.Affine.addX,
      weightedX, weightedY, weightedDouble, zero_mul, add_zero]
    field_simp [hZ, hY]
    ring
  have hy :
      W.addY (weightedX P) (weightedX P) (weightedY P) slope =
        weightedY (weightedDouble A B P) := by
    have haddY :
        W.addY (weightedX P) (weightedX P) (weightedY P) slope =
          -(slope *
              (W.addX (weightedX P) (weightedX P) slope -
                weightedX P) + weightedY P) := by
      simp [W, integralCurve, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.negAddY]
    rw [haddY, hx, hslope]
    simp only [weightedX, weightedY, weightedDouble]
    field_simp [hZ, hY]
    ring
  have hnew :
      W.Nonsingular
        (W.addX (weightedX P) (weightedX P) slope)
        (W.addY (weightedX P) (weightedX P) (weightedY P) slope) :=
    WeierstrassCurve.Affine.nonsingular_add
      hpoint hpoint (fun h => hyNeg h.right)
  have hdouble :
      W.Nonsingular
        (weightedX (weightedDouble A B P))
        (weightedY (weightedDouble A B P)) := by
    rwa [← hx, ← hy]
  refine ⟨hdouble, ?_⟩
  rw [two_nsmul,
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyNeg]
  simp only [slope, hx, hy]

/-- The denominator-free mixed addition formula represents addition by its
fixed affine base point. -/
theorem weightedAddBase_represents_add
    (A B x y : K) (P : WeightedPoint K)
    (hZ : P.Z ≠ 0)
    (hE : P.X - x * P.Z ^ 2 ≠ 0)
    (hpoint :
      (integralCurve A B).toAffine.Nonsingular
        (weightedX P) (weightedY P))
    (hbase : (integralCurve A B).toAffine.Nonsingular x y) :
    ∃ hadd :
        (integralCurve A B).toAffine.Nonsingular
          (weightedX (weightedAddBase A x y P))
          (weightedY (weightedAddBase A x y P)),
      (WeierstrassCurve.Affine.Point.some
          (weightedX P) (weightedY P) hpoint) +
          (.some x y hbase) =
        .some
          (weightedX (weightedAddBase A x y P))
          (weightedY (weightedAddBase A x y P)) hadd := by
  let W := (integralCurve A B).toAffine
  have hxBase : weightedX P ≠ x := by
    intro hx
    apply hE
    unfold weightedX at hx
    field_simp [hZ] at hx
    linear_combination hx
  let slope :=
    W.slope (weightedX P) x (weightedY P) y
  have hslope :
      slope =
        (P.Y - y * P.Z ^ 3) /
          (P.Z * (P.X - x * P.Z ^ 2)) := by
    dsimp [slope]
    rw [WeierstrassCurve.Affine.slope_of_X_ne hxBase]
    unfold weightedX weightedY
    field_simp [hZ, hE]
  have hx :
      W.addX (weightedX P) x slope =
        weightedX (weightedAddBase A x y P) := by
    have hD :
        P.Z * (P.X - x * P.Z ^ 2) ≠ 0 :=
      mul_ne_zero hZ hE
    have hE' : P.X - P.Z ^ 2 * x ≠ 0 := by
      convert hE using 1 <;> ring
    rw [hslope]
    simp only [W, integralCurve, WeierstrassCurve.Affine.addX,
      weightedX, weightedAddBase, zero_mul, add_zero]
    change
      ((P.Y - y * P.Z ^ 3) /
            (P.Z * (P.X - x * P.Z ^ 2))) ^ 2 -
          A - P.X / P.Z ^ 2 - x =
        ((P.Y - y * P.Z ^ 3) ^ 2 -
            (A + x) *
              (P.Z * (P.X - x * P.Z ^ 2)) ^ 2 -
            P.X * (P.X - x * P.Z ^ 2) ^ 2) /
          (P.Z * (P.X - x * P.Z ^ 2)) ^ 2
    field_simp [hD, hZ, hE]
    ring
  have hy :
      W.addY (weightedX P) x (weightedY P) slope =
        weightedY (weightedAddBase A x y P) := by
    have haddY :
        W.addY (weightedX P) x (weightedY P) slope =
          -(slope *
              (W.addX (weightedX P) x slope -
                weightedX P) + weightedY P) := by
      simp [W, integralCurve, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.negAddY]
    rw [haddY, hx, hslope]
    simp only [weightedX, weightedY, weightedAddBase]
    let X : K := P.X
    let Y : K := P.Y
    let Z : K := P.Z
    let E : K := X - x * Z ^ 2
    let N : K := Y - y * Z ^ 3
    let D : K := Z * E
    let X' : K :=
      N ^ 2 - (A + x) * D ^ 2 - X * E ^ 2
    change
      -(N / D * (X' / D ^ 2 - X / Z ^ 2) + Y / Z ^ 3) =
        (-N * (X' - X * E ^ 2) - Y * E ^ 3) / D ^ 3
    have hZ' : Z ≠ 0 := hZ
    have hE' : E ≠ 0 := hE
    field_simp [D, hZ', hE']
    ring
  have hnew :
      W.Nonsingular
        (W.addX (weightedX P) x slope)
        (W.addY (weightedX P) x (weightedY P) slope) :=
    WeierstrassCurve.Affine.nonsingular_add
      hpoint hbase (fun h => hxBase h.left)
  have hadd :
      W.Nonsingular
        (weightedX (weightedAddBase A x y P))
        (weightedY (weightedAddBase A x y P)) := by
    rwa [← hx, ← hy]
  refine ⟨hadd, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxBase]
  congr 1

end WeightedSemantics

theorem e0_weightedDouble_represents_double
    (P : WeightedPoint GaussianRat)
    (hZ : P.Z ≠ 0) (hY : P.Y ≠ 0)
    (hpoint :
      gaussianE0.toAffine.Nonsingular
        (weightedX P) (weightedY P)) :
    ∃ hdouble :
        gaussianE0.toAffine.Nonsingular
          (weightedX (weightedDouble E0A E0B P))
          (weightedY (weightedDouble E0A E0B P)),
      2 •
          (WeierstrassCurve.Affine.Point.some
            (weightedX P) (weightedY P) hpoint) =
        .some
          (weightedX (weightedDouble E0A E0B P))
          (weightedY (weightedDouble E0A E0B P)) hdouble := by
  exact weightedDouble_represents_double E0A E0B P hZ hY hpoint

theorem e0_weightedAddBase_represents_add
    (x y : GaussianRat) (P : WeightedPoint GaussianRat)
    (hZ : P.Z ≠ 0)
    (hE : P.X - x * P.Z ^ 2 ≠ 0)
    (hpoint :
      gaussianE0.toAffine.Nonsingular
        (weightedX P) (weightedY P))
    (hbase : gaussianE0.toAffine.Nonsingular x y) :
    ∃ hadd :
        gaussianE0.toAffine.Nonsingular
          (weightedX (weightedAddBase E0A x y P))
          (weightedY (weightedAddBase E0A x y P)),
      (WeierstrassCurve.Affine.Point.some
          (weightedX P) (weightedY P) hpoint) +
          (.some x y hbase) =
        .some
          (weightedX (weightedAddBase E0A x y P))
          (weightedY (weightedAddBase E0A x y P)) hadd := by
  exact
    weightedAddBase_represents_add E0A E0B x y P
      hZ hE hpoint hbase

/-! ## The actual weighted chain for a seventh preimage -/

set_option maxHeartbeats 5000000 in
/-- If an actual Gaussian point with nonzero free coordinate is a seventh
preimage of the visible point, the complete denominator-free addition chain
is defined, represents `[7]Q`, and ends with abscissa `2`. -/
theorem exists_weighted_seven_preimage
    (e : E0Point ≃+ ℤ × ZMod 2)
    (Q : E0Point)
    (hfree : (e Q).1 ≠ 0)
    (hseven : 7 • Q = visiblePoint) :
    ∃ x : GaussianRat,
      sevenPreimageValue E0A E0B x = 0 := by
  have hQ_ne_zero : Q ≠ 0 := by
    intro h
    apply hfree
    have ht := congrArg (fun S : E0Point => (e S).1) h
    simpa using ht
  have htwo_ne_zero : 2 • Q ≠ 0 := by
    intro h
    have ht := congrArg (fun S : E0Point => (e S).1) h
    simp only [map_nsmul, map_zero] at ht
    apply hfree
    norm_num [nsmul_eq_mul] at ht ⊢
    omega
  have hsix_ne_zero : 6 • Q ≠ 0 := by
    intro h
    have ht := congrArg (fun S : E0Point => (e S).1) h
    simp only [map_nsmul, map_zero] at ht
    apply hfree
    norm_num [nsmul_eq_mul] at ht ⊢
    omega
  have htwo_ne_one : 2 • Q ≠ Q := by
    intro h
    have ht := congrArg (fun S : E0Point => (e S).1) h
    simp only [map_nsmul] at ht
    apply hfree
    norm_num [nsmul_eq_mul] at ht ⊢
    omega
  have htwo_ne_neg_one : 2 • Q ≠ -Q := by
    intro h
    have ht := congrArg (fun S : E0Point => (e S).1) h
    simp only [map_nsmul, map_neg] at ht
    apply hfree
    norm_num [nsmul_eq_mul] at ht ⊢
    omega
  have hsix_ne_one : 6 • Q ≠ Q := by
    intro h
    have ht := congrArg (fun S : E0Point => (e S).1) h
    simp only [map_nsmul] at ht
    apply hfree
    norm_num [nsmul_eq_mul] at ht ⊢
    omega
  have hsix_ne_neg_one : 6 • Q ≠ -Q := by
    intro h
    have ht := congrArg (fun S : E0Point => (e S).1) h
    simp only [map_nsmul, map_neg] at ht
    apply hfree
    norm_num [nsmul_eq_mul] at ht ⊢
    omega
  obtain ⟨x, y, hxy, hQ⟩ :
      ∃ x y : GaussianRat,
        ∃ hxy : gaussianE0.toAffine.Nonsingular x y,
          Q = .some x y hxy := by
    rcases Q with (_ | ⟨x, y, hxy⟩)
    · exact (hQ_ne_zero rfl).elim
    · exact ⟨x, y, hxy, rfl⟩
  let P1 : WeightedPoint GaussianRat := weightedOne x y
  let P2 : WeightedPoint GaussianRat := weightedTwo E0A E0B x y
  let P3 : WeightedPoint GaussianRat := weightedThree E0A E0B x y
  let P6 : WeightedPoint GaussianRat := weightedSix E0A E0B x y
  let P7 : WeightedPoint GaussianRat := weightedSeven E0A E0B x y
  have hZ1 : P1.Z ≠ 0 := by
    simp [P1, weightedOne]
  have hY1 : P1.Y ≠ 0 := by
    simp only [P1, weightedOne]
    intro hy
    apply htwo_ne_zero
    rw [two_nsmul, hQ]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    simp [gaussianE0, hy]
  have hP1 :
      gaussianE0.toAffine.Nonsingular
        (weightedX P1) (weightedY P1) := by
    simpa [P1, weightedOne, weightedX, weightedY] using hxy
  obtain ⟨hP2, hdouble⟩ :=
    e0_weightedDouble_represents_double P1 hZ1 hY1 hP1
  have htwo :
      2 • Q =
        .some (weightedX P2) (weightedY P2) hP2 := by
    simpa [hQ, P1, P2, weightedTwo, weightedOne,
      weightedX, weightedY] using hdouble
  have hZ2 : P2.Z ≠ 0 := by
    simp only [P2, weightedTwo, weightedDouble, P1, weightedOne]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hY1) hZ1
  have hE2 : P2.X - x * P2.Z ^ 2 ≠ 0 := by
    intro hE
    have hx2 : weightedX P2 = x := by
      unfold weightedX
      apply (div_eq_iff (pow_ne_zero 2 hZ2)).2
      linear_combination hE
    rcases
        (WeierstrassCurve.Affine.Point.X_eq_iff
          (W := gaussianE0.toAffine)).mp hx2 with hsame | hneg
    · apply htwo_ne_one
      exact htwo.trans (hsame.trans hQ.symm)
    · apply htwo_ne_neg_one
      exact htwo.trans (hneg.trans (congrArg Neg.neg hQ.symm))
  obtain ⟨hP3, haddThree⟩ :=
    e0_weightedAddBase_represents_add x y P2
      hZ2 hE2 hP2 hxy
  have hthree :
      3 • Q =
        .some (weightedX P3) (weightedY P3) hP3 := by
    calc
      3 • Q = (2 + 1) • Q := by norm_num
      _ = 2 • Q + 1 • Q := add_nsmul Q 2 1
      _ = 2 • Q + Q := by rw [one_nsmul]
      _ =
          .some (weightedX P2) (weightedY P2) hP2 +
            .some x y hxy := congrArg₂ (· + ·) htwo hQ
      _ = .some (weightedX P3) (weightedY P3) hP3 := by
        simpa [P3, weightedThree] using haddThree
  have hZ3 : P3.Z ≠ 0 := by
    simp only [P3, weightedThree, weightedAddBase]
    exact mul_ne_zero hZ2 hE2
  have hY3 : P3.Y ≠ 0 := by
    intro hy
    apply hsix_ne_zero
    rw [show 6 • Q = 2 • (3 • Q) by
      calc
        6 • Q = (3 * 2) • Q := by norm_num
        _ = 2 • (3 • Q) := mul_nsmul Q 3 2]
    rw [hthree, two_nsmul]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    simp [gaussianE0, weightedY, hy]
  obtain ⟨hP6, hdoubleSix⟩ :=
    e0_weightedDouble_represents_double P3 hZ3 hY3 hP3
  have hsix :
      6 • Q =
        .some (weightedX P6) (weightedY P6) hP6 := by
    calc
      6 • Q = (3 * 2) • Q := by norm_num
      _ = 2 • (3 • Q) := mul_nsmul Q 3 2
      _ = .some (weightedX P6) (weightedY P6) hP6 := by
        simpa [hthree, P6, weightedSix] using hdoubleSix
  have hZ6 : P6.Z ≠ 0 := by
    simp only [P6, weightedSix, weightedDouble]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hY3) hZ3
  have hE6 : P6.X - x * P6.Z ^ 2 ≠ 0 := by
    intro hE
    have hx6 : weightedX P6 = x := by
      unfold weightedX
      apply (div_eq_iff (pow_ne_zero 2 hZ6)).2
      linear_combination hE
    rcases
        (WeierstrassCurve.Affine.Point.X_eq_iff
          (W := gaussianE0.toAffine)).mp hx6 with hsame | hneg
    · apply hsix_ne_one
      exact hsix.trans (hsame.trans hQ.symm)
    · apply hsix_ne_neg_one
      exact hsix.trans (hneg.trans (congrArg Neg.neg hQ.symm))
  obtain ⟨hP7, haddSeven⟩ :=
    e0_weightedAddBase_represents_add x y P6
      hZ6 hE6 hP6 hxy
  have hweightedSeven :
      7 • Q =
        .some (weightedX P7) (weightedY P7) hP7 := by
    calc
      7 • Q = (6 + 1) • Q := by norm_num
      _ = 6 • Q + 1 • Q := add_nsmul Q 6 1
      _ = 6 • Q + Q := by rw [one_nsmul]
      _ =
          .some (weightedX P6) (weightedY P6) hP6 +
            .some x y hxy := congrArg₂ (· + ·) hsix hQ
      _ = .some (weightedX P7) (weightedY P7) hP7 := by
        simpa [P7, weightedSeven] using haddSeven
  have hZ7 : P7.Z ≠ 0 := by
    simp only [P7, weightedSeven, weightedAddBase]
    exact mul_ne_zero hZ6 hE6
  have hxSeven : P7.X / P7.Z ^ 2 = 2 := by
    change weightedX P7 = 2
    have hpoint :
        (WeierstrassCurve.Affine.Point.some
            (weightedX P7) (weightedY P7) hP7 :
          gaussianE0.toAffine.Point) = visiblePoint :=
      hweightedSeven.symm.trans hseven
    simpa [visiblePoint, Cuboid2.gaussianE0P,
      WeierstrassCurve.Affine.Point.mk] using
      congrArg
        (fun P : gaussianE0.toAffine.Point =>
          match P with
          | 0 => 0
          | .some x _ _ => x)
        hpoint
  have heq :
      (curve E0A E0B).toAffine.Equation x y := by
    rw [← gaussianE0_eq_curve]
    exact hxy.1
  have hfact := curve_equation_iff.mp heq
  have hcurve :
      y ^ 2 = x ^ 3 + E0A * x ^ 2 + E0B * x := by
    calc
      y ^ 2 = x * (x ^ 2 + E0A * x + E0B) := hfact
      _ = x ^ 3 + E0A * x ^ 2 + E0B * x := by ring
  have hr : psiThreeValue E0A E0B x ≠ 0 := by
    intro hr0
    apply hZ3
    change (weightedThree E0A E0B x y).Z = 0
    rw [weightedThree_Z E0A E0B x y hcurve, hr0]
    ring
  have hcross :=
    weightedSeven_cross_of_eq
      E0A E0B x y P7 rfl hcurve hr
  have hX : P7.X = 2 * P7.Z ^ 2 :=
    (div_eq_iff (pow_ne_zero 2 hZ7)).mp hxSeven
  rw [hX] at hcross
  have hmul :
      P7.Z ^ 2 * sevenPreimageValue E0A E0B x = 0 := by
    rw [sevenPreimageValue]
    linear_combination -hcross
  exact
    ⟨x, (mul_eq_zero.mp hmul).resolve_left
      (pow_ne_zero 2 hZ7)⟩

end

end GaussianP29SaturationActual
end Cuboid2
