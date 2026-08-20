import Cuboid2.QuadraticReduction.GaussianRange
import Cuboid2.QuadraticReduction.GaussianObstructionBridge
import Cuboid2.QuadraticReduction.GaussianFinite
import Cuboid2.QuadraticReduction.GaussianPrimes

/-!
# Exact upper ranges for the four Gaussian descent maps

The UFD support theorem leaves eight squareclasses for each of the four
two-isogeny descent maps.  The closed homogeneous-space computations remove
the classes with odd `1+i`-valuation, and the remaining specialized rows
remove the extra even classes.
-/

namespace Cuboid2

noncomputable section

namespace GaussianExactRanges

open GaussianDescent GaussianFraction GaussianPrimes GaussianRange
  GaussianObstructionBridge

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

private def e0AInt : GaussianInt := ⟨0, 2⟩
private def e1AInt : GaussianInt := ⟨2, 0⟩
private def e0DualAInt : GaussianInt := ⟨0, -4⟩
private def e1DualAInt : GaussianInt := ⟨-4, 0⟩

@[simp] private theorem algebraMap_e0AInt :
    algebraMap GaussianInt GaussianRat e0AInt = E0A := by
  rw [algebraMap_gaussianInt_apply]
  ext <;>
    norm_num [e0AInt, E0A, gaussianI,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

@[simp] private theorem algebraMap_e1AInt :
    algebraMap GaussianInt GaussianRat e1AInt = E1A := by
  rw [algebraMap_gaussianInt_apply]
  ext <;>
    norm_num [e1AInt, E1A, gaussianI,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

@[simp] private theorem algebraMap_e0DualAInt :
    algebraMap GaussianInt GaussianRat e0DualAInt = -2 * E0A := by
  rw [algebraMap_gaussianInt_apply]
  ext <;>
    norm_num [e0DualAInt, E0A, gaussianI,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

@[simp] private theorem algebraMap_e1DualAInt :
    algebraMap GaussianInt GaussianRat e1DualAInt = -2 * E1A := by
  rw [algebraMap_gaussianInt_apply]
  ext <;>
    norm_num [e1DualAInt, E1A, gaussianI,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

private theorem gaussianIInt_isUnit : IsUnit gaussianIInt := by
  rw [Zsqrtd.isUnit_iff_norm_isUnit]
  norm_num

private theorem e0B_prime_support
    (q : GaussianInt) (hq : Prime q) (hdiv : q ∣ e0BInt) :
    Associated q gaussianLambdaInt ∨ Associated q gaussianPiInt := by
  apply prime_dvd_unit_mul_two_prime_powers (m := 2) (n := 1)
    hq gaussianIInt_isUnit gaussianLambdaInt_prime gaussianPiInt_prime
  rw [pow_one, ← e0BInt_factorization]
  exact hdiv

private theorem e1B_prime_support
    (q : GaussianInt) (hq : Prime q) (hdiv : q ∣ e1BInt) :
    Associated q gaussianLambdaInt ∨ Associated q gaussianPiInt := by
  apply prime_dvd_unit_mul_two_prime_powers (m := 2) (n := 1)
    hq gaussianIInt_isUnit.neg gaussianLambdaInt_prime gaussianPiInt_prime
  rw [pow_one, ← e1BInt_factorization]
  exact hdiv

private theorem e0DualB_prime_support
    (q : GaussianInt) (hq : Prime q) (hdiv : q ∣ e0DualBInt) :
    Associated q gaussianLambdaInt ∨ Associated q gaussianRhoInt := by
  apply prime_dvd_unit_mul_two_prime_powers (m := 4) (n := 1)
    hq isUnit_neg_one gaussianLambdaInt_prime gaussianRhoInt_prime
  rw [pow_one, neg_one_mul, ← e0DualBInt_factorization]
  exact hdiv

private theorem e1DualB_prime_support
    (q : GaussianInt) (hq : Prime q) (hdiv : q ∣ e1DualBInt) :
    Associated q gaussianLambdaInt ∨ Associated q gaussianRhoInt := by
  apply prime_dvd_unit_mul_two_prime_powers (m := 4) (n := 1)
    hq isUnit_one gaussianLambdaInt_prime gaussianRhoInt_prime
  rw [pow_one, one_mul, ← e1DualBInt_factorization]
  exact hdiv

private theorem squareClass_ne_of_closed_row
    (n : ℕ) [NeZero n] (hn : Even n)
    (a b d e : GaussianInt) (hd : d ≠ 0) (hbe : b = d * e)
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy :
      y ^ 2 =
        x * (x ^ 2 +
          algebraMap GaussianInt GaussianRat a * x +
          algebraMap GaussianInt GaussianRat b))
    (hobs :
      GaussianFinite.hasPrimitiveHomogeneousSpaceSolution n
        (gaussianResidue n a) (gaussianResidue n d)
        (gaussianResidue n e) = false) :
    squareClassOf x hx ≠
      squareClassOf (algebraMap GaussianInt GaussianRat d)
        (by
          intro h
          apply hd
          apply FaithfulSMul.algebraMap_injective GaussianInt GaussianRat
          simpa only [map_zero] using h) := by
  apply squareClass_ne_of_localObstruction n hn a b d e hd hbe hx
  · exact curve_equation_iff.mpr hxy
  · exact hobs

private theorem e0_ne_classLambda
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy : y ^ 2 = x * (x ^ 2 + E0A * x + E0B)) :
    squareClassOf x hx ≠ classLambda := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e0AInt e0BInt gaussianLambdaInt ⟨-3, -1⟩
      gaussianLambdaInt_prime.ne_zero (by decide) hx
      (by
        rw [algebraMap_e0AInt, algebraMap_e0BInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e0AInt, gaussianLambdaInt]
        exact GaussianFinite.e0_lambda_local_obstruction)
  simpa only [classLambda] using h

private theorem e0_ne_classILambda
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy : y ^ 2 = x * (x ^ 2 + E0A * x + E0B)) :
    squareClassOf x hx ≠ classILambda := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e0AInt e0BInt (gaussianIInt * gaussianLambdaInt) ⟨-1, 3⟩
      (mul_ne_zero gaussianIInt_isUnit.ne_zero
        gaussianLambdaInt_prime.ne_zero)
      (by decide) hx
      (by
        rw [algebraMap_e0AInt, algebraMap_e0BInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e0AInt, gaussianIInt,
          gaussianLambdaInt]
        exact GaussianFinite.e0_iLambda_local_obstruction)
  simpa only [classILambda] using h

private theorem e0_ne_classLambdaPi
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy : y ^ 2 = x * (x ^ 2 + E0A * x + E0B)) :
    squareClassOf x hx ≠ classLambdaPi := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e0AInt e0BInt (gaussianLambdaInt * gaussianPiInt) ⟨-1, 1⟩
      (mul_ne_zero gaussianLambdaInt_prime.ne_zero
        gaussianPiInt_prime.ne_zero)
      (by decide) hx
      (by
        rw [algebraMap_e0AInt, algebraMap_e0BInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e0AInt, gaussianLambdaInt,
          gaussianPiInt]
        exact GaussianFinite.e0_lambdaPi_local_obstruction)
  simpa only [classLambdaPi] using h

private theorem e0_ne_classILambdaPi
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy : y ^ 2 = x * (x ^ 2 + E0A * x + E0B)) :
    squareClassOf x hx ≠ classILambdaPi := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e0AInt e0BInt
        (gaussianIInt * gaussianLambdaInt * gaussianPiInt) ⟨1, 1⟩
      (mul_ne_zero
        (mul_ne_zero gaussianIInt_isUnit.ne_zero
          gaussianLambdaInt_prime.ne_zero)
        gaussianPiInt_prime.ne_zero)
      (by decide) hx
      (by
        rw [algebraMap_e0AInt, algebraMap_e0BInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e0AInt, gaussianIInt,
          gaussianLambdaInt, gaussianPiInt]
        exact GaussianFinite.e0_iLambdaPi_local_obstruction)
  simpa only [classILambdaPi] using h

private theorem e0Dual_ne_classLambda
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy :
      y ^ 2 =
        x * (x ^ 2 + (-2 * E0A) * x + (E0A ^ 2 - 4 * E0B))) :
    squareClassOf x hx ≠ classLambda := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e0DualAInt e0DualBInt gaussianLambdaInt ⟨10, 6⟩
      gaussianLambdaInt_prime.ne_zero (by decide) hx
      (by
        rw [algebraMap_e0DualAInt, algebraMap_e0DualBInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e0DualAInt, gaussianLambdaInt]
        exact GaussianFinite.e0Dual_lambda_local_obstruction)
  simpa only [classLambda] using h

private theorem e0Dual_ne_classILambda
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy :
      y ^ 2 =
        x * (x ^ 2 + (-2 * E0A) * x + (E0A ^ 2 - 4 * E0B))) :
    squareClassOf x hx ≠ classILambda := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e0DualAInt e0DualBInt
        (gaussianIInt * gaussianLambdaInt) ⟨6, -10⟩
      (mul_ne_zero gaussianIInt_isUnit.ne_zero
        gaussianLambdaInt_prime.ne_zero)
      (by decide) hx
      (by
        rw [algebraMap_e0DualAInt, algebraMap_e0DualBInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e0DualAInt, gaussianIInt,
          gaussianLambdaInt]
        exact GaussianFinite.e0Dual_iLambda_local_obstruction)
  simpa only [classILambda] using h

private theorem e0Dual_ne_classLambdaRho
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy :
      y ^ 2 =
        x * (x ^ 2 + (-2 * E0A) * x + (E0A ^ 2 - 4 * E0B))) :
    squareClassOf x hx ≠ classLambdaRho := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e0DualAInt e0DualBInt
        (gaussianLambdaInt * gaussianRhoInt) ⟨2, -2⟩
      (mul_ne_zero gaussianLambdaInt_prime.ne_zero
        gaussianRhoInt_prime.ne_zero)
      (by decide) hx
      (by
        rw [algebraMap_e0DualAInt, algebraMap_e0DualBInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e0DualAInt, gaussianLambdaInt,
          gaussianRhoInt]
        exact GaussianFinite.e0Dual_lambdaRho_local_obstruction)
  simpa only [classLambdaRho] using h

private theorem e0Dual_ne_classILambdaRho
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy :
      y ^ 2 =
        x * (x ^ 2 + (-2 * E0A) * x + (E0A ^ 2 - 4 * E0B))) :
    squareClassOf x hx ≠ classILambdaRho := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e0DualAInt e0DualBInt
        (gaussianIInt * gaussianLambdaInt * gaussianRhoInt) ⟨-2, -2⟩
      (mul_ne_zero
        (mul_ne_zero gaussianIInt_isUnit.ne_zero
          gaussianLambdaInt_prime.ne_zero)
        gaussianRhoInt_prime.ne_zero)
      (by decide) hx
      (by
        rw [algebraMap_e0DualAInt, algebraMap_e0DualBInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e0DualAInt, gaussianIInt,
          gaussianLambdaInt, gaussianRhoInt]
        exact GaussianFinite.e0Dual_iLambdaRho_local_obstruction)
  simpa only [classILambdaRho] using h

private theorem e0Dual_ne_classI
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy :
      y ^ 2 =
        x * (x ^ 2 + (-2 * E0A) * x + (E0A ^ 2 - 4 * E0B))) :
    squareClassOf x hx ≠ classI := by
  have h :=
    squareClass_ne_of_closed_row 16 (by norm_num)
      e0DualAInt e0DualBInt gaussianIInt ⟨16, -4⟩
      gaussianIInt_isUnit.ne_zero (by decide) hx
      (by
        rw [algebraMap_e0DualAInt, algebraMap_e0DualBInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e0DualAInt, gaussianIInt]
        exact GaussianFinite.e0Dual_i_local_obstruction)
  simpa only [classI, algebraMap_gaussianIInt] using h

private theorem e0Dual_ne_classIRho
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy :
      y ^ 2 =
        x * (x ^ 2 + (-2 * E0A) * x + (E0A ^ 2 - 4 * E0B))) :
    squareClassOf x hx ≠ classIRho := by
  have h :=
    squareClass_ne_of_closed_row 16 (by norm_num)
      e0DualAInt e0DualBInt (gaussianIInt * gaussianRhoInt) ⟨0, -4⟩
      (mul_ne_zero gaussianIInt_isUnit.ne_zero
        gaussianRhoInt_prime.ne_zero)
      (by decide) hx
      (by
        rw [algebraMap_e0DualAInt, algebraMap_e0DualBInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e0DualAInt, gaussianIInt,
          gaussianRhoInt]
        exact GaussianFinite.e0Dual_iRho_local_obstruction)
  simpa only [classIRho, map_mul, algebraMap_gaussianIInt,
    algebraMap_gaussianRhoInt] using h

private theorem e1_ne_classLambda
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy : y ^ 2 = x * (x ^ 2 + E1A * x + E1B)) :
    squareClassOf x hx ≠ classLambda := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e1AInt e1BInt gaussianLambdaInt ⟨3, 1⟩
      gaussianLambdaInt_prime.ne_zero (by decide) hx
      (by
        rw [algebraMap_e1AInt, algebraMap_e1BInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e1AInt, gaussianLambdaInt]
        exact GaussianFinite.e1_lambda_local_obstruction)
  simpa only [classLambda] using h

private theorem e1_ne_classILambda
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy : y ^ 2 = x * (x ^ 2 + E1A * x + E1B)) :
    squareClassOf x hx ≠ classILambda := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e1AInt e1BInt (gaussianIInt * gaussianLambdaInt) ⟨1, -3⟩
      (mul_ne_zero gaussianIInt_isUnit.ne_zero
        gaussianLambdaInt_prime.ne_zero)
      (by decide) hx
      (by
        rw [algebraMap_e1AInt, algebraMap_e1BInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e1AInt, gaussianIInt,
          gaussianLambdaInt]
        exact GaussianFinite.e1_iLambda_local_obstruction)
  simpa only [classILambda] using h

private theorem e1_ne_classLambdaPi
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy : y ^ 2 = x * (x ^ 2 + E1A * x + E1B)) :
    squareClassOf x hx ≠ classLambdaPi := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e1AInt e1BInt (gaussianLambdaInt * gaussianPiInt) ⟨1, -1⟩
      (mul_ne_zero gaussianLambdaInt_prime.ne_zero
        gaussianPiInt_prime.ne_zero)
      (by decide) hx
      (by
        rw [algebraMap_e1AInt, algebraMap_e1BInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e1AInt, gaussianLambdaInt,
          gaussianPiInt]
        exact GaussianFinite.e1_lambdaPi_local_obstruction)
  simpa only [classLambdaPi] using h

private theorem e1_ne_classILambdaPi
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy : y ^ 2 = x * (x ^ 2 + E1A * x + E1B)) :
    squareClassOf x hx ≠ classILambdaPi := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e1AInt e1BInt
        (gaussianIInt * gaussianLambdaInt * gaussianPiInt) ⟨-1, -1⟩
      (mul_ne_zero
        (mul_ne_zero gaussianIInt_isUnit.ne_zero
          gaussianLambdaInt_prime.ne_zero)
        gaussianPiInt_prime.ne_zero)
      (by decide) hx
      (by
        rw [algebraMap_e1AInt, algebraMap_e1BInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e1AInt, gaussianIInt,
          gaussianLambdaInt, gaussianPiInt]
        exact GaussianFinite.e1_iLambdaPi_local_obstruction)
  simpa only [classILambdaPi] using h

private theorem e1_ne_classI
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy : y ^ 2 = x * (x ^ 2 + E1A * x + E1B)) :
    squareClassOf x hx ≠ classI := by
  have h :=
    squareClass_ne_of_closed_row 8 (by norm_num)
      e1AInt e1BInt gaussianIInt ⟨4, -2⟩
      gaussianIInt_isUnit.ne_zero (by decide) hx
      (by
        rw [algebraMap_e1AInt, algebraMap_e1BInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e1AInt, gaussianIInt]
        exact GaussianFinite.e1_i_local_obstruction)
  simpa only [classI, algebraMap_gaussianIInt] using h

private theorem e1_ne_classPi
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy : y ^ 2 = x * (x ^ 2 + E1A * x + E1B)) :
    squareClassOf x hx ≠ classPi := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e1AInt e1BInt gaussianPiInt ⟨2, 0⟩
      gaussianPiInt_prime.ne_zero (by decide) hx
      (by
        rw [algebraMap_e1AInt, algebraMap_e1BInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e1AInt, gaussianPiInt]
        exact GaussianFinite.e1_pi_local_obstruction)
  simpa only [classPi, algebraMap_gaussianPiInt] using h

private theorem e1Dual_ne_classLambda
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy :
      y ^ 2 =
        x * (x ^ 2 + (-2 * E1A) * x + (E1A ^ 2 - 4 * E1B))) :
    squareClassOf x hx ≠ classLambda := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e1DualAInt e1DualBInt gaussianLambdaInt ⟨-10, -6⟩
      gaussianLambdaInt_prime.ne_zero (by decide) hx
      (by
        rw [algebraMap_e1DualAInt, algebraMap_e1DualBInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e1DualAInt, gaussianLambdaInt]
        exact GaussianFinite.e1Dual_lambda_local_obstruction)
  simpa only [classLambda] using h

private theorem e1Dual_ne_classILambda
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy :
      y ^ 2 =
        x * (x ^ 2 + (-2 * E1A) * x + (E1A ^ 2 - 4 * E1B))) :
    squareClassOf x hx ≠ classILambda := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e1DualAInt e1DualBInt
        (gaussianIInt * gaussianLambdaInt) ⟨-6, 10⟩
      (mul_ne_zero gaussianIInt_isUnit.ne_zero
        gaussianLambdaInt_prime.ne_zero)
      (by decide) hx
      (by
        rw [algebraMap_e1DualAInt, algebraMap_e1DualBInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e1DualAInt, gaussianIInt,
          gaussianLambdaInt]
        exact GaussianFinite.e1Dual_iLambda_local_obstruction)
  simpa only [classILambda] using h

private theorem e1Dual_ne_classLambdaRho
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy :
      y ^ 2 =
        x * (x ^ 2 + (-2 * E1A) * x + (E1A ^ 2 - 4 * E1B))) :
    squareClassOf x hx ≠ classLambdaRho := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e1DualAInt e1DualBInt
        (gaussianLambdaInt * gaussianRhoInt) ⟨-2, 2⟩
      (mul_ne_zero gaussianLambdaInt_prime.ne_zero
        gaussianRhoInt_prime.ne_zero)
      (by decide) hx
      (by
        rw [algebraMap_e1DualAInt, algebraMap_e1DualBInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e1DualAInt, gaussianLambdaInt,
          gaussianRhoInt]
        exact GaussianFinite.e1Dual_lambdaRho_local_obstruction)
  simpa only [classLambdaRho] using h

private theorem e1Dual_ne_classILambdaRho
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy :
      y ^ 2 =
        x * (x ^ 2 + (-2 * E1A) * x + (E1A ^ 2 - 4 * E1B))) :
    squareClassOf x hx ≠ classILambdaRho := by
  have h :=
    squareClass_ne_of_closed_row 4 (by norm_num)
      e1DualAInt e1DualBInt
        (gaussianIInt * gaussianLambdaInt * gaussianRhoInt) ⟨2, 2⟩
      (mul_ne_zero
        (mul_ne_zero gaussianIInt_isUnit.ne_zero
          gaussianLambdaInt_prime.ne_zero)
        gaussianRhoInt_prime.ne_zero)
      (by decide) hx
      (by
        rw [algebraMap_e1DualAInt, algebraMap_e1DualBInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e1DualAInt, gaussianIInt,
          gaussianLambdaInt, gaussianRhoInt]
        exact GaussianFinite.e1Dual_iLambdaRho_local_obstruction)
  simpa only [classILambdaRho] using h

private theorem e1Dual_ne_classI
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy :
      y ^ 2 =
        x * (x ^ 2 + (-2 * E1A) * x + (E1A ^ 2 - 4 * E1B))) :
    squareClassOf x hx ≠ classI := by
  have h :=
    squareClass_ne_of_closed_row 32 (by norm_num)
      e1DualAInt e1DualBInt gaussianIInt ⟨-16, 4⟩
      gaussianIInt_isUnit.ne_zero (by decide) hx
      (by
        rw [algebraMap_e1DualAInt, algebraMap_e1DualBInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e1DualAInt, gaussianIInt]
        exact GaussianFinite.e1Dual_i_local_obstruction)
  simpa only [classI, algebraMap_gaussianIInt] using h

private theorem e1Dual_ne_classIRho
    {x y : GaussianRat} (hx : x ≠ 0)
    (hxy :
      y ^ 2 =
        x * (x ^ 2 + (-2 * E1A) * x + (E1A ^ 2 - 4 * E1B))) :
    squareClassOf x hx ≠ classIRho := by
  have h :=
    squareClass_ne_of_closed_row 32 (by norm_num)
      e1DualAInt e1DualBInt (gaussianIInt * gaussianRhoInt) ⟨0, 4⟩
      (mul_ne_zero gaussianIInt_isUnit.ne_zero
        gaussianRhoInt_prime.ne_zero)
      (by decide) hx
      (by
        rw [algebraMap_e1DualAInt, algebraMap_e1DualBInt]
        exact hxy)
      (by
        norm_num [gaussianResidue, e1DualAInt, gaussianIInt,
          gaussianRhoInt]
        exact GaussianFinite.e1Dual_iRho_local_obstruction)
  simpa only [classIRho, map_mul, algebraMap_gaussianIInt,
    algebraMap_gaussianRhoInt] using h

/-! ## Unconditional pointwise ranges -/

/-- The forward descent map on `E₀` has exactly the four possible upper
classes supported at `pi`; all odd-`lambda` classes are locally obstructed. -/
theorem gaussianE0_alpha_classified
    (P : (curve E0A E0B).toAffine.Point) :
    alpha E0A E0B E0B_ne_zero E0C_ne_zero P = 1 ∨
      alpha E0A E0B E0B_ne_zero E0C_ne_zero P = classI ∨
      alpha E0A E0B E0B_ne_zero E0C_ne_zero P = classPi ∨
      alpha E0A E0B E0B_ne_zero E0C_ne_zero P = classIPi := by
  rcases P with (_ | ⟨x, y, hpoint⟩)
  · exact Or.inl rfl
  · have hxy :
        y ^ 2 = x * (x ^ 2 + E0A * x + E0B) :=
      curve_equation_iff.mp hpoint.left
    by_cases hx : x = 0
    · subst x
      refine Or.inr (Or.inr (Or.inr ?_))
      simpa only [alpha, ↓reduceDIte, torsion, pointOfEquation] using
        alpha_gaussianE0T
    · have hraw :=
        curve_abscissa_pi_raw_cases e0B_prime_support hx
          (by
            rw [algebraMap_e0AInt, algebraMap_e0BInt]
            exact hxy)
      simp only [alpha, hx, ↓reduceDIte]
      rcases hraw with h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact (e0_ne_classLambda hx hxy h).elim
      · exact (e0_ne_classILambda hx hxy h).elim
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact (e0_ne_classLambdaPi hx hxy h).elim
      · exact (e0_ne_classILambdaPi hx hxy h).elim

/-- The dual descent map on `E₀` has upper range `{1,rho}`. -/
theorem gaussianE0_alphaDual_classified
    (P : (dualCurve E0A E0B).toAffine.Point) :
    alphaDual E0A E0B E0B_ne_zero E0C_ne_zero P = 1 ∨
      alphaDual E0A E0B E0B_ne_zero E0C_ne_zero P = classRho := by
  rcases P with (_ | ⟨x, y, hpoint⟩)
  · exact Or.inl rfl
  · have hxy :
      y ^ 2 =
          x * (x ^ 2 + (-2 * E0A) * x + (E0A ^ 2 - 4 * E0B)) :=
      by
        simpa [sub_eq_add_neg, mul_assoc] using
          (dualCurve_equation_iff.mp hpoint.left)
    by_cases hx : x = 0
    · subst x
      refine Or.inr ?_
      simpa only [alphaDual, ↓reduceDIte, dualTorsion,
        pointOfEquation] using alphaDual_gaussianE0T
    · have hraw :=
        curve_abscissa_rho_raw_cases e0DualB_prime_support hx
          (by
            rw [algebraMap_e0DualAInt, algebraMap_e0DualBInt]
            exact hxy)
      simp only [alphaDual, hx, ↓reduceDIte]
      rcases hraw with h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact (e0Dual_ne_classI hx hxy h).elim
      · exact (e0Dual_ne_classLambda hx hxy h).elim
      · exact (e0Dual_ne_classILambda hx hxy h).elim
      · exact Or.inr h
      · exact (e0Dual_ne_classIRho hx hxy h).elim
      · exact (e0Dual_ne_classLambdaRho hx hxy h).elim
      · exact (e0Dual_ne_classILambdaRho hx hxy h).elim

/-- The forward descent map on `E₁` has upper range `{1,i*pi}`. -/
theorem gaussianE1_alpha_classified
    (P : (curve E1A E1B).toAffine.Point) :
    alpha E1A E1B E1B_ne_zero E1C_ne_zero P = 1 ∨
      alpha E1A E1B E1B_ne_zero E1C_ne_zero P = classIPi := by
  rcases P with (_ | ⟨x, y, hpoint⟩)
  · exact Or.inl rfl
  · have hxy :
        y ^ 2 = x * (x ^ 2 + E1A * x + E1B) :=
      curve_equation_iff.mp hpoint.left
    by_cases hx : x = 0
    · subst x
      refine Or.inr ?_
      simpa only [alpha, ↓reduceDIte, torsion, pointOfEquation] using
        alpha_gaussianE1T
    · have hraw :=
        curve_abscissa_pi_raw_cases e1B_prime_support hx
          (by
            rw [algebraMap_e1AInt, algebraMap_e1BInt]
            exact hxy)
      simp only [alpha, hx, ↓reduceDIte]
      rcases hraw with h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact (e1_ne_classI hx hxy h).elim
      · exact (e1_ne_classLambda hx hxy h).elim
      · exact (e1_ne_classILambda hx hxy h).elim
      · exact (e1_ne_classPi hx hxy h).elim
      · exact Or.inr h
      · exact (e1_ne_classLambdaPi hx hxy h).elim
      · exact (e1_ne_classILambdaPi hx hxy h).elim

/-- The dual descent map on `E₁` has upper range `{1,rho}`. -/
theorem gaussianE1_alphaDual_classified
    (P : (dualCurve E1A E1B).toAffine.Point) :
    alphaDual E1A E1B E1B_ne_zero E1C_ne_zero P = 1 ∨
      alphaDual E1A E1B E1B_ne_zero E1C_ne_zero P = classRho := by
  rcases P with (_ | ⟨x, y, hpoint⟩)
  · exact Or.inl rfl
  · have hxy :
      y ^ 2 =
          x * (x ^ 2 + (-2 * E1A) * x + (E1A ^ 2 - 4 * E1B)) :=
      by
        simpa [sub_eq_add_neg, mul_assoc] using
          (dualCurve_equation_iff.mp hpoint.left)
    by_cases hx : x = 0
    · subst x
      refine Or.inr ?_
      simpa only [alphaDual, ↓reduceDIte, dualTorsion,
        pointOfEquation] using alphaDual_gaussianE1T
    · have hraw :=
        curve_abscissa_rho_raw_cases e1DualB_prime_support hx
          (by
            rw [algebraMap_e1DualAInt, algebraMap_e1DualBInt]
            exact hxy)
      simp only [alphaDual, hx, ↓reduceDIte]
      rcases hraw with h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact (e1Dual_ne_classI hx hxy h).elim
      · exact (e1Dual_ne_classLambda hx hxy h).elim
      · exact (e1Dual_ne_classILambda hx hxy h).elim
      · exact Or.inr h
      · exact (e1Dual_ne_classIRho hx hxy h).elim
      · exact (e1Dual_ne_classLambdaRho hx hxy h).elim
      · exact (e1Dual_ne_classILambdaRho hx hxy h).elim

/-! ## Exact set-theoretic ranges -/

theorem gaussianE0_alpha_range :
    Set.range (alpha E0A E0B E0B_ne_zero E0C_ne_zero) =
      ({1, classI, classPi, classIPi} : Set SquareClass) := by
  ext c
  constructor
  · rintro ⟨P, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      gaussianE0_alpha_classified P
  · intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨0, alpha_zero E0A E0B E0B_ne_zero E0C_ne_zero⟩
    · exact
        ⟨GaussianDescent.gaussianE0P,
          GaussianDescent.alpha_gaussianE0P⟩
    · exact
        ⟨GaussianDescent.gaussianE0P +
            torsion E0A E0B E0B_ne_zero E0C_ne_zero,
          GaussianDescent.alpha_gaussianE0P_add_T⟩
    · exact
        ⟨torsion E0A E0B E0B_ne_zero E0C_ne_zero,
          alpha_gaussianE0T⟩

theorem gaussianE0_alpha_range_ncard :
    (Set.range (alpha E0A E0B E0B_ne_zero E0C_ne_zero)).ncard = 4 := by
  rw [gaussianE0_alpha_range]
  have h0 :
      (1 : SquareClass) ∉
        ({classI, classPi, classIPi} : Set SquareClass) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨classI_ne_one.symm, classPi_ne_one.symm,
      classIPi_ne_one.symm⟩
  have hI :
      classI ∉ ({classPi, classIPi} : Set SquareClass) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨classI_ne_classPi, classI_ne_classIPi⟩
  have hPi : classPi ∉ ({classIPi} : Set SquareClass) := by
    simpa only [Set.mem_singleton_iff] using classPi_ne_classIPi
  rw [Set.ncard_insert_of_notMem h0,
    Set.ncard_insert_of_notMem hI,
    Set.ncard_insert_of_notMem hPi,
    Set.ncard_singleton]

theorem gaussianE0_alphaDual_range :
    Set.range (alphaDual E0A E0B E0B_ne_zero E0C_ne_zero) =
      ({1, classRho} : Set SquareClass) := by
  ext c
  constructor
  · rintro ⟨P, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      gaussianE0_alphaDual_classified P
  · intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact ⟨0, alphaDual_zero E0A E0B E0B_ne_zero E0C_ne_zero⟩
    · exact
        ⟨dualTorsion E0A E0B E0B_ne_zero E0C_ne_zero,
          GaussianDescent.alphaDual_gaussianE0T⟩

theorem gaussianE0_alphaDual_range_ncard :
    (Set.range
      (alphaDual E0A E0B E0B_ne_zero E0C_ne_zero)).ncard = 2 := by
  rw [gaussianE0_alphaDual_range]
  have h : (1 : SquareClass) ∉ ({classRho} : Set SquareClass) := by
    simpa only [Set.mem_singleton_iff] using classRho_ne_one.symm
  rw [Set.ncard_insert_of_notMem h, Set.ncard_singleton]

theorem gaussianE1_alpha_range :
    Set.range (alpha E1A E1B E1B_ne_zero E1C_ne_zero) =
      ({1, classIPi} : Set SquareClass) := by
  ext c
  constructor
  · rintro ⟨P, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      gaussianE1_alpha_classified P
  · intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact ⟨0, alpha_zero E1A E1B E1B_ne_zero E1C_ne_zero⟩
    · exact
        ⟨torsion E1A E1B E1B_ne_zero E1C_ne_zero,
          GaussianDescent.alpha_gaussianE1T⟩

theorem gaussianE1_alpha_range_ncard :
    (Set.range (alpha E1A E1B E1B_ne_zero E1C_ne_zero)).ncard = 2 := by
  rw [gaussianE1_alpha_range]
  have h : (1 : SquareClass) ∉ ({classIPi} : Set SquareClass) := by
    simpa only [Set.mem_singleton_iff] using classIPi_ne_one.symm
  rw [Set.ncard_insert_of_notMem h, Set.ncard_singleton]

theorem gaussianE1_alphaDual_range :
    Set.range (alphaDual E1A E1B E1B_ne_zero E1C_ne_zero) =
      ({1, classRho} : Set SquareClass) := by
  ext c
  constructor
  · rintro ⟨P, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      gaussianE1_alphaDual_classified P
  · intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact ⟨0, alphaDual_zero E1A E1B E1B_ne_zero E1C_ne_zero⟩
    · exact
        ⟨dualTorsion E1A E1B E1B_ne_zero E1C_ne_zero,
          GaussianDescent.alphaDual_gaussianE1T⟩

theorem gaussianE1_alphaDual_range_ncard :
    (Set.range
      (alphaDual E1A E1B E1B_ne_zero E1C_ne_zero)).ncard = 2 := by
  rw [gaussianE1_alphaDual_range]
  have h : (1 : SquareClass) ∉ ({classRho} : Set SquareClass) := by
    simpa only [Set.mem_singleton_iff] using classRho_ne_one.symm
  rw [Set.ncard_insert_of_notMem h, Set.ncard_singleton]

/-! ## Exact cardinalities of the genuine homomorphism ranges -/

private def alphaHomRangeEquivRange
    (A B : GaussianRat) (hB : B ≠ 0) (hC : A ^ 2 - 4 * B ≠ 0) :
    (alphaHom A B hB hC).range ≃
      Set.range (alpha A B hB hC) where
  toFun z := by
    refine ⟨z.1.toMul, ?_⟩
    rcases z.2 with ⟨P, hP⟩
    refine ⟨P, ?_⟩
    exact congrArg Additive.toMul hP
  invFun z := by
    refine ⟨Additive.ofMul z.1, ?_⟩
    rcases z.2 with ⟨P, hP⟩
    refine ⟨P, ?_⟩
    exact congrArg Additive.ofMul hP
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl

private def alphaDualHomRangeEquivRange
    (A B : GaussianRat) (hB : B ≠ 0) (hC : A ^ 2 - 4 * B ≠ 0) :
    (alphaDualHom A B hB hC).range ≃
      Set.range (alphaDual A B hB hC) where
  toFun z := by
    refine ⟨z.1.toMul, ?_⟩
    rcases z.2 with ⟨P, hP⟩
    refine ⟨P, ?_⟩
    exact congrArg Additive.toMul hP
  invFun z := by
    refine ⟨Additive.ofMul z.1, ?_⟩
    rcases z.2 with ⟨P, hP⟩
    refine ⟨P, ?_⟩
    exact congrArg Additive.ofMul hP
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl

theorem gaussianE0_alphaHom_range_card :
    Nat.card (alphaHom E0A E0B E0B_ne_zero E0C_ne_zero).range = 4 := by
  rw [Nat.card_congr
    (alphaHomRangeEquivRange E0A E0B E0B_ne_zero E0C_ne_zero),
    Nat.card_coe_set_eq]
  exact gaussianE0_alpha_range_ncard

theorem gaussianE0_alphaDualHom_range_card :
    Nat.card
      (alphaDualHom E0A E0B E0B_ne_zero E0C_ne_zero).range = 2 := by
  rw [Nat.card_congr
    (alphaDualHomRangeEquivRange E0A E0B E0B_ne_zero E0C_ne_zero),
    Nat.card_coe_set_eq]
  exact gaussianE0_alphaDual_range_ncard

theorem gaussianE1_alphaHom_range_card :
    Nat.card (alphaHom E1A E1B E1B_ne_zero E1C_ne_zero).range = 2 := by
  rw [Nat.card_congr
    (alphaHomRangeEquivRange E1A E1B E1B_ne_zero E1C_ne_zero),
    Nat.card_coe_set_eq]
  exact gaussianE1_alpha_range_ncard

theorem gaussianE1_alphaDualHom_range_card :
    Nat.card
      (alphaDualHom E1A E1B E1B_ne_zero E1C_ne_zero).range = 2 := by
  rw [Nat.card_congr
    (alphaDualHomRangeEquivRange E1A E1B E1B_ne_zero E1C_ne_zero),
    Nat.card_coe_set_eq]
  exact gaussianE1_alphaDual_range_ncard

instance gaussianE0_alphaHom_range_finite :
    Finite (alphaHom E0A E0B E0B_ne_zero E0C_ne_zero).range :=
  Nat.finite_of_card_ne_zero (by
    rw [gaussianE0_alphaHom_range_card]
    norm_num)

instance gaussianE0_alphaDualHom_range_finite :
    Finite (alphaDualHom E0A E0B E0B_ne_zero E0C_ne_zero).range :=
  Nat.finite_of_card_ne_zero (by
    rw [gaussianE0_alphaDualHom_range_card]
    norm_num)

instance gaussianE1_alphaHom_range_finite :
    Finite (alphaHom E1A E1B E1B_ne_zero E1C_ne_zero).range :=
  Nat.finite_of_card_ne_zero (by
    rw [gaussianE1_alphaHom_range_card]
    norm_num)

instance gaussianE1_alphaDualHom_range_finite :
    Finite (alphaDualHom E1A E1B E1B_ne_zero E1C_ne_zero).range :=
  Nat.finite_of_card_ne_zero (by
    rw [gaussianE1_alphaDualHom_range_card]
    norm_num)

end GaussianExactRanges

end

end Cuboid2
