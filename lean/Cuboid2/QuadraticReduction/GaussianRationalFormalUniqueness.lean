import Cuboid2.QuadraticReduction.GaussianIndexIndependent

/-!
# Rational all-level uniqueness for the index-independent route

The visible point need not be primitive.  After writing the free coefficient
of that point as `m`, the two surviving formal parameters have numerators
`(k-m)/12` and `(k+m)/12` and denominator `|m|`.  This file isolates the
arithmetic fact used after clearing that denominator: a coefficient which is
a unit modulo `37`, plus a tail visibly divisible by `37`, forces the
integral numerator to vanish at all levels.
-/

namespace Cuboid2
namespace GaussianRationalFormalUniqueness

open GaussianP37
open GaussianIndexIndependent

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

/-! ## Pure clearing-denominator arithmetic -/

/-- A rational parameter `a/b`, with `b` prime to `37`, is zero if the
cleared first-order unit congruence holds at every `37`-power precision.

The tail may depend on the precision.  No convergence, formal logarithm, or
Mordell--Weil generator is assumed.
-/
theorem numerator_eq_zero_of_cleared_unit_allLevels
    (unit a : ℤ) (b : ℕ)
    (hunit : IsCoprime (37 : ℤ) unit)
    (hb : b.Coprime 37)
    (tail : ℕ → ℤ)
    (hlevels : ∀ n : ℕ,
      (37 : ℤ) ^ (n + 1) ∣
        (unit * (b : ℤ)) * a + 37 * a * tail n) :
    a = 0 := by
  have hbInt : IsCoprime (37 : ℤ) (b : ℤ) :=
    hb.symm.isCoprime
  exact allLevel_unitLinear_unique
    (unit * (b : ℤ)) a (hunit.mul_right hbInt) tail hlevels

/-- Disk-specialized form using the certified coefficients `29` and `8`. -/
theorem rationalParameter_numerator_unique
    (disk : Disk) (q : RationalParameter)
    (tail : ℕ → ℤ)
    (hlevels : ∀ n : ℕ,
      (37 : ℤ) ^ (n + 1) ∣
        (disk.linearUnit * q.denominator) * q.numerator +
          37 * q.numerator * tail n) :
    q.numerator = 0 := by
  have hunit : IsCoprime (37 : ℤ) disk.linearUnit := by
    cases disk <;> norm_num [Disk.linearUnit]
  exact numerator_eq_zero_of_cleared_unit_allLevels
    disk.linearUnit q.numerator q.denominator hunit
      q.denominator_coprime tail hlevels

/-- Multiplication by an integer prime to `84` is injective on every group
identified with `ℤ × ZMod 2`. -/
theorem zsmul_injective_of_isCoprime_84
    (e : E0Point ≃+ ℤ × ZMod 2)
    (m : ℤ) (hm : IsCoprime m (84 : ℤ)) :
    Function.Injective (m • · : E0Point → E0Point) := by
  intro Q R hQR
  apply e.injective
  have hmap := congrArg e hQR
  rw [map_zsmul, map_zsmul] at hmap
  apply Prod.ext
  · have hfirst :
        m * (e Q).1 = m * (e R).1 := by
      simpa [zsmul_eq_mul] using congrArg Prod.fst hmap
    have hm0 : m ≠ 0 := by
      intro hmZero
      subst m
      norm_num at hm
    exact mul_left_cancel₀ hm0 hfirst
  · have hsecond :
        (m : ZMod 2) * (e Q).2 =
          (m : ZMod 2) * (e R).2 := by
      simpa [zsmul_eq_mul] using congrArg Prod.snd hmap
    have hm2 : IsCoprime m (2 : ℤ) :=
      IsCoprime.of_isCoprime_of_dvd_right hm (by norm_num)
    have hunit : IsUnit (m : ZMod 2) :=
      (ZMod.coe_int_isUnit_iff_isCoprime m 2).mpr hm2.symm
    exact hunit.mul_left_cancel hsecond

/-! ## Consumers for the two index-independent parameters -/

/-- In the `P` disk, the existing all-level predicate for the rational
index-independent parameter forces both its numerator and value to vanish,
and hence forces `k=m`. -/
theorem parameterAtP_local_unique
    {k m : ℤ}
    (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : IsCoprime m (37 : ℤ))
    (hrow : k ≡ m [ZMOD 12])
    (hformal :
      RationalXCongruentAtAllLevels .plus
        (parameterAtP k m hm84 hm37 hrow)) :
    (parameterAtP k m hm84 hm37 hrow).numerator = 0 ∧
      (parameterAtP k m hm84 hm37 hrow).value = 0 ∧
      k = m := by
  have hnum :
      (parameterAtP k m hm84 hm37 hrow).numerator = 0 :=
    rationalX_parameter_unique .plus
      (parameterAtP k m hm84 hm37 hrow) hformal
  refine ⟨hnum, ?_, ?_⟩
  · rw [RationalParameter.value, hnum]
    norm_num
  · exact eq_of_parameterAtP_numerator_eq_zero
      hm84 hm37 hrow hnum

/-- The corresponding rational uniqueness theorem in the `-P` disk. -/
theorem parameterAtNegP_local_unique
    {k m : ℤ}
    (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : IsCoprime m (37 : ℤ))
    (hrow : k ≡ -m [ZMOD 12])
    (hformal :
      RationalXCongruentAtAllLevels .minus
        (parameterAtNegP k m hm84 hm37 hrow)) :
    (parameterAtNegP k m hm84 hm37 hrow).numerator = 0 ∧
      (parameterAtNegP k m hm84 hm37 hrow).value = 0 ∧
      k = -m := by
  have hnum :
      (parameterAtNegP k m hm84 hm37 hrow).numerator = 0 :=
    rationalX_parameter_unique .minus
      (parameterAtNegP k m hm84 hm37 hrow) hformal
  refine ⟨hnum, ?_, ?_⟩
  · rw [RationalParameter.value, hnum]
    norm_num
  · exact eq_neg_of_parameterAtNegP_numerator_eq_zero
      hm84 hm37 hrow hnum

/-! ## Actual-point consumers without a primitive visible point -/

/-- A surviving plain `P` row with the rational all-level congruences is the
actual visible point.  The proof uses only simultaneous normal forms and
injectivity of multiplication by `m`; it never writes `Q=kP`. -/
theorem point_eq_visible_of_rational_allLevels
    (e : E0Point ≃+ ℤ × ZMod 2)
    (Q : E0Point) {m k : ℤ} {δ ε : ℕ}
    (hP :
      visiblePoint = m • freeGenerator e + δ • twoTorsionPoint)
    (hQ :
      Q = k • freeGenerator e + ε • twoTorsionPoint)
    (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : IsCoprime m (37 : ℤ))
    (hrow : rowResidue k (inverseMod84 m) = 1)
    (hplain :
      rowTwist k (inverseMod84 m) δ ε = .plain)
    (hformal :
      RationalXCongruentAtAllLevels .plus
        (parameterAtP k m hm84 hm37
          (coefficient_modEq_of_inverseMod84_row_one hm84 hrow))) :
    Q = visiblePoint := by
  let hmod : k ≡ m [ZMOD 12] :=
    coefficient_modEq_of_inverseMod84_row_one hm84 hrow
  have hk : k = m :=
    (parameterAtP_local_unique hm84 hm37 hmod hformal).2.2
  have hmul : m • Q = k • visiblePoint :=
    indexCleared_point_eq_of_plain e hP hQ
      (mul_inverseMod84_modEq hm84) hplain
  apply zsmul_injective_of_isCoprime_84 e m hm84
  simpa only [hk] using hmul

/-- The same index-independent conclusion in the `-P` disk. -/
theorem point_eq_neg_visible_of_rational_allLevels
    (e : E0Point ≃+ ℤ × ZMod 2)
    (Q : E0Point) {m k : ℤ} {δ ε : ℕ}
    (hP :
      visiblePoint = m • freeGenerator e + δ • twoTorsionPoint)
    (hQ :
      Q = k • freeGenerator e + ε • twoTorsionPoint)
    (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : IsCoprime m (37 : ℤ))
    (hrow : rowResidue k (inverseMod84 m) = 11)
    (hplain :
      rowTwist k (inverseMod84 m) δ ε = .plain)
    (hformal :
      RationalXCongruentAtAllLevels .minus
        (parameterAtNegP k m hm84 hm37
          (coefficient_modEq_of_inverseMod84_row_eleven hm84 hrow))) :
    Q = -visiblePoint := by
  let hmod : k ≡ -m [ZMOD 12] :=
    coefficient_modEq_of_inverseMod84_row_eleven hm84 hrow
  have hk : k = -m :=
    (parameterAtNegP_local_unique hm84 hm37 hmod hformal).2.2
  have hmul : m • Q = k • visiblePoint :=
    indexCleared_point_eq_of_plain e hP hQ
      (mul_inverseMod84_modEq hm84) hplain
  apply zsmul_injective_of_isCoprime_84 e m hm84
  simpa only [hk, neg_zsmul, zsmul_neg] using hmul

/-- Explicit cleared-denominator form for the `P` disk.  The coefficient
`29` is the certified first-order split difference. -/
theorem coefficient_eq_of_cleared_allLevels_at_P
    {k m : ℤ}
    (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : IsCoprime m (37 : ℤ))
    (hrow : k ≡ m [ZMOD 12])
    (tail : ℕ → ℤ)
    (hlevels : ∀ n : ℕ,
      (37 : ℤ) ^ (n + 1) ∣
        (29 * (m.natAbs : ℤ)) * ((k - m) / 12) +
          37 * ((k - m) / 12) * tail n) :
    k = m := by
  have hb : m.natAbs.Coprime 37 := by
    simpa using (Int.isCoprime_iff_nat_coprime.mp hm37)
  have hnum : (k - m) / 12 = 0 :=
    numerator_eq_zero_of_cleared_unit_allLevels
      29 ((k - m) / 12) m.natAbs (by norm_num) hb tail hlevels
  apply eq_of_parameterAtP_numerator_eq_zero hm84 hm37 hrow
  simpa using hnum

/-- Explicit cleared-denominator form for the `-P` disk.  Here the certified
unit coefficient is `8`. -/
theorem coefficient_eq_of_cleared_allLevels_at_negP
    {k m : ℤ}
    (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : IsCoprime m (37 : ℤ))
    (hrow : k ≡ -m [ZMOD 12])
    (tail : ℕ → ℤ)
    (hlevels : ∀ n : ℕ,
      (37 : ℤ) ^ (n + 1) ∣
        (8 * (m.natAbs : ℤ)) * ((k + m) / 12) +
          37 * ((k + m) / 12) * tail n) :
    k = -m := by
  have hb : m.natAbs.Coprime 37 := by
    simpa using (Int.isCoprime_iff_nat_coprime.mp hm37)
  have hnum : (k + m) / 12 = 0 :=
    numerator_eq_zero_of_cleared_unit_allLevels
      8 ((k + m) / 12) m.natAbs (by norm_num) hb tail hlevels
  apply eq_neg_of_parameterAtNegP_numerator_eq_zero hm84 hm37 hrow
  simpa using hnum

end GaussianRationalFormalUniqueness
end Cuboid2
