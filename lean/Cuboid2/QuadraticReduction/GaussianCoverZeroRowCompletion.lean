import Cuboid2.QuadraticReduction.GaussianCoverZeroIndexPair
import Cuboid2.QuadraticReduction.GaussianCoverZeroTranslationActual
import Cuboid2.QuadraticReduction.GaussianIndexCoprime
import Cuboid2.QuadraticReduction.GaussianP37IndexSaturationActual
import Cuboid2.QuadraticReduction.GaussianP37SaturationActual
import Cuboid2.QuadraticReduction.GaussianRationalFormalUniqueness

/-!
# Pointwise completion of the surviving untwisted-cover rows

Assuming only the remaining `7`-saturation statement for the visible point,
this module combines the already unconditional `2`, `3`, and `37`
saturation results with the actual paired-row obstruction.  It does not
assume that the visible point is primitive: multiplication by its unknown
free coefficient is cancelled only through coprimality with `84`.
-/

namespace Cuboid2
namespace GaussianCoverZeroRowCompletion

noncomputable section

open GaussianCoverZeroIndexPair
open GaussianCoverZeroTranslationActual
open GaussianIndexCoprime
open GaussianIndexIndependent
open GaussianIndexIndependentReduction
open GaussianP37IndexSaturationActual
open GaussianP37SaturationActual
open GaussianRationalFormalUniqueness

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have hxnonneg : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance :
    Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

/-- Once the visible coefficient is known not to be divisible by `7`, every
actual point of the untwisted Gaussian cover maps to `P` or `-P`.

The normal forms are simultaneous with respect to the same abstract free
generator.  No primitivity of `P` and no representation `Q = nP + εT` is
used.
-/
theorem coverZero_toE0_eq_visible_or_neg
    (e : E0Point ≃+ ℤ × ZMod 2)
    (C : GaussianCoverZeroPoint)
    {m k : ℤ} {δ ε : ℕ}
    (hδ : δ < 2)
    (_hε : ε < 2)
    (hP :
      visiblePoint = m • freeGenerator e + δ • twoTorsionPoint)
    (hC :
      C.toE0 = k • freeGenerator e + ε • twoTorsionPoint)
    (hseven : ¬(7 : ℤ) ∣ m) :
    C.toE0 = gaussianE0P ∨ C.toE0 = -gaussianE0P := by
  have hodd : Odd m :=
    visibleCoefficient_odd e hδ hP
  have hthree : ¬(3 : ℤ) ∣ m :=
    three_not_dvd_visiblePoint_coefficient e hP
  have hthirtySeven : ¬(37 : ℤ) ∣ m :=
    thirtySeven_not_dvd_visiblePoint_coefficient e hP
  have hm84 : IsCoprime m (84 : ℤ) :=
    isCoprime_84_of_odd_of_not_dvd_three_of_not_dvd_seven
      hodd hthree hseven
  have hm37 : IsCoprime m (37 : ℤ) :=
    isCoprime_37_of_not_dvd hthirtySeven
  obtain ⟨hplain, hrow | hrow⟩ :=
    coverZero_indexIndependent_survivingRows_actual
      e C hP hC hm84
  · by_cases ha : (k - m) / 12 = 0
    · have hmod : k ≡ m [ZMOD 12] :=
        coefficient_modEq_of_inverseMod84_row_one hm84 hrow
      have hexact : ((k - m) / 12) * 12 = k - m := by
        simpa using
          parameterAtP_numerator_mul_twelve hm84 hm37 hmod
      rw [ha] at hexact
      have hk : k = m := by omega
      left
      apply zsmul_injective_of_isCoprime_84 e m hm84
      have hmul :
          m • C.toE0 = k • visiblePoint :=
        (indexIndependent_row_one
          e hP hC hm84 hrow hplain).2
      simpa only [hk] using hmul
    · exact
        (no_pairedKernelSeparated_sub_P C
          (pairSeparated_sub_visible_of_row_one
            e hP hC hm84 hthirtySeven hrow hplain ha)).elim
  · by_cases ha : (k + m) / 12 = 0
    · have hmod : k ≡ -m [ZMOD 12] :=
        coefficient_modEq_of_inverseMod84_row_eleven hm84 hrow
      have hexact : ((k + m) / 12) * 12 = k + m := by
        simpa using
          parameterAtNegP_numerator_mul_twelve hm84 hm37 hmod
      rw [ha] at hexact
      have hk : k = -m := by omega
      right
      apply zsmul_injective_of_isCoprime_84 e m hm84
      have hmul :
          m • C.toE0 = k • visiblePoint :=
        (indexIndependent_row_eleven
          e hP hC hm84 hrow hplain).2
      simpa only [hk, neg_zsmul, zsmul_neg] using hmul
    · exact
        (no_pairedKernelSeparated_sub_negP C
          (pairSeparated_sub_neg_visible_of_row_eleven
            e hP hC hm84 hthirtySeven hrow hplain ha)).elim

end

end GaussianCoverZeroRowCompletion
end Cuboid2
