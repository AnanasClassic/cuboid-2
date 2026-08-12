import Cuboid2.LinearQuartic.DescentCertificates

/-!
# Completion certificates for the linear--quartic 2-descent

This file supplies the finite square-table exhaustion statement that is
separate from the local-basis computation in `DescentCertificates`.
-/

namespace Cuboid2

noncomputable section

open LinearQuarticRamifiedResidue
open Polynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/--
The eight displayed residues exhaust the squares of all 256 binary unit
representatives modulo `π⁹`.

This is a kernel-reduced enumeration of the exact 512-element quotient; it
does not rely on an external computation.
-/
theorem henselUnitRepresentative_square_mem
    (mask : Fin 256) :
    mul (henselUnitRepresentative mask)
          (henselUnitRepresentative mask) ∈
        henselSquareResidues := by
  rw [henselUnitRepresentative_eq_direct]
  fin_cases mask <;> decide

/--
Consequently, the eight-entry table exhausts the square of every unit residue
in the exact quotient.
-/
theorem unitResidue_square_mem_henselSquareResidues
    (a : LinearQuarticRamifiedResidue)
    (ha : IsUnitResidue a) :
    mul a a ∈ henselSquareResidues := by
  obtain ⟨mask, rfl⟩ :=
    (henselUnitRepresentative_exhausts a).mp ha
  exact henselUnitRepresentative_square_mem mask

/-!
## The finite square predicate

The table membership predicate can be related in both directions to an
actual square in the finite quotient.  This removes the finite-exhaustion
premise mentioned in `localBasisProduct_square_iff_zero`; only the
mathematical Hensel-lifting theorem from this quotient to the completion is
outside this finite calculation.
-/

/-- Being the square of a unit in the exact ramified residue quotient. -/
def IsUnitSquareResidue
    (a : LinearQuarticRamifiedResidue) : Prop :=
  ∃ u : LinearQuarticRamifiedResidue,
    IsUnitResidue u ∧ mul u u = a

/-- Every row in the displayed table has an explicit unit square root. -/
theorem mem_henselSquareResidues_isUnitSquareResidue
    {a : LinearQuarticRamifiedResidue}
    (ha : a ∈ henselSquareResidues) :
    IsUnitSquareResidue a := by
  rw [henselSquareResidues, List.mem_map] at ha
  obtain ⟨mask, _, rfl⟩ := ha
  let lifted : Fin 256 :=
    ⟨mask.val, lt_trans mask.isLt (by norm_num)⟩
  refine
    ⟨henselUnitRepresentativeDirect lifted, ?_, rfl⟩
  rw [← henselUnitRepresentative_eq_direct lifted]
  exact henselUnitRepresentative_isUnit lifted

/-- The eight rows are exactly all unit squares in the finite quotient. -/
theorem isUnitSquareResidue_iff_mem_henselSquareResidues
    (a : LinearQuarticRamifiedResidue) :
    IsUnitSquareResidue a ↔ a ∈ henselSquareResidues := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact unitResidue_square_mem_henselSquareResidues u hu
  · exact mem_henselSquareResidues_isUnitSquareResidue

/--
The genuine finite square-root formulation for a product of the six proposed
local squareclass generators.  The first bit is the separately recorded
valuation parity.
-/
def LocalBasisProductHasSquareRoot (mask : Fin 64) : Prop :=
  mask.val.testBit 0 = false ∧
    IsUnitSquareResidue (normalizedLocalBasisProduct mask)

/--
The six local generators are independent already in the exact finite
quotient: a normalized product has even valuation and a unit square root
exactly for the empty mask.
-/
theorem localBasisProduct_hasSquareRoot_iff_zero
    (mask : Fin 64) :
    LocalBasisProductHasSquareRoot mask ↔ mask.val = 0 := by
  rw [LocalBasisProductHasSquareRoot,
    isUnitSquareResidue_iff_mem_henselSquareResidues]
  exact localBasisProduct_square_iff_zero mask

/-!
## Exact order invariants

These determinant rows are the finite algebraic input to the
maximal-order/class-number argument.  They deliberately stop short of
asserting that the displayed order is the full ring of integers.
-/

open LinearQuarticDescentElt

/-- Trace of multiplication in the displayed integral power basis. -/
def linearQuarticDescentTrace
    (a : LinearQuarticDescentElt) : ℤ :=
  Matrix.trace (multiplicationMatrix a)

/-- Discriminant of the displayed basis `1,π,π²,π³`. -/
def linearQuarticPowerBasisDiscriminant : ℤ :=
  Matrix.det
    (fun i j : Fin 4 =>
      linearQuarticDescentTrace (mul (basis i) (basis j)))

/-- The exact power-basis discriminant is `-688 = -2⁴·43`. -/
theorem linearQuarticPowerBasisDiscriminant_eq :
    linearQuarticPowerBasisDiscriminant = -688 := by
  decide

/-- The discriminant has precisely the stated prime factorization. -/
theorem linearQuarticPowerBasisDiscriminant_factorization :
    linearQuarticPowerBasisDiscriminant = -(2 ^ 4 * 43) := by
  rw [linearQuarticPowerBasisDiscriminant_eq]
  norm_num

/--
Any possible index whose square divides the absolute power-basis
discriminant is `1`, `2`, or `4`.  Thus the maximal-order check has only its
2-primary part left after the discriminant calculation.
-/
theorem linearQuartic_possible_powerOrder_index
    {index : ℕ} (hindex : index ^ 2 ∣ 688) :
    index = 1 ∨ index = 2 ∨ index = 4 := by
  have hdiv := hindex
  have hindex0 : index ≠ 0 := by
    intro hzero
    subst index
    norm_num at hindex
  obtain ⟨multiple, hmultiple⟩ := hindex
  have hmultiplePos : 0 < multiple := by
    by_contra hzero
    have : multiple = 0 := Nat.eq_zero_of_not_pos hzero
    subst multiple
    simp at hmultiple
  have hsquare : index ^ 2 ≤ 688 := by
    rw [hmultiple]
    exact Nat.le_mul_of_pos_right (index ^ 2) hmultiplePos
  have hindexLe : index ≤ 26 := by nlinarith
  interval_cases index <;> norm_num at hdiv
  all_goals norm_num

/--
The translated quartic is Eisenstein at `2`.  This is the exact local
polynomial premise used to prove total ramification at `2`.
-/
theorem linearQuarticDescentField_shift_isEisenstein :
    (X ^ 4 + C 4 * X ^ 3 + C 6 * X ^ 2 + C 2 * X - 2 :
        ℤ[X]).IsEisensteinAt (Ideal.span {(2 : ℤ)}) := by
  let f : ℤ[X] :=
    X ^ 4 + C 4 * X ^ 3 + C 6 * X ^ 2 + C 2 * X - 2
  have hmonic : f.Monic := by
    unfold f
    monicity <;> norm_num
  have hdegree : f.natDegree = 4 := by
    unfold f
    compute_degree <;> norm_num
  change f.IsEisensteinAt (Ideal.span {(2 : ℤ)})
  constructor
  · rw [hmonic.leadingCoeff]
    simp [Ideal.mem_span_singleton]
  · intro n hn
    have hn' : n < 4 := by omega
    interval_cases n <;>
      norm_num [f, Ideal.mem_span_singleton, coeff_X_pow, coeff_X]
  · have hc : f.coeff 0 = -2 := by
      norm_num [f, coeff_X_pow, coeff_X]
    rw [hc, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num

/-- In particular, the translated quartic is irreducible over `ℤ`. -/
theorem linearQuarticDescentField_shift_irreducible :
    Irreducible
      (X ^ 4 + C 4 * X ^ 3 + C 6 * X ^ 2 + C 2 * X - 2 :
        ℤ[X]) := by
  let f : ℤ[X] :=
    X ^ 4 + C 4 * X ^ 3 + C 6 * X ^ 2 + C 2 * X - 2
  change Irreducible f
  apply
    (show f.IsEisensteinAt (Ideal.span {(2 : ℤ)}) by
      simpa [f] using linearQuarticDescentField_shift_isEisenstein).irreducible
  · rw [Ideal.span_singleton_prime]
    · norm_num
    · norm_num
  · have hmonic : f.Monic := by
      unfold f
      monicity <;> norm_num
    exact hmonic.isPrimitive
  · have hdegree : f.natDegree = 4 := by
      unfold f
      compute_degree <;> norm_num
    omega

/-- Translation by one as a polynomial-ring automorphism. -/
def linearQuarticTranslateOne : ℤ[X] ≃+* ℤ[X] where
  toFun p := p.comp (X + C (1 : ℤ))
  invFun p := p.comp (X - C (1 : ℤ))
  map_add' p q := by simp
  map_mul' p q := by simp
  left_inv p := by
    change
      (p.comp (X + C (1 : ℤ))).comp (X - C (1 : ℤ)) = p
    rw [comp_assoc]
    have h :
        (X + C (1 : ℤ)).comp (X - C (1 : ℤ)) =
          (X : ℤ[X]) := by simp
    rw [h, comp_X]
  right_inv p := by
    change
      (p.comp (X - C (1 : ℤ))).comp (X + C (1 : ℤ)) = p
    rw [comp_assoc]
    have h :
        (X - C (1 : ℤ)).comp (X + C (1 : ℤ)) =
          (X : ℤ[X]) := by simp
    rw [h, comp_X]

/-- The original quartic field polynomial is irreducible over `ℤ`. -/
theorem linearQuarticDescentFieldPolynomial_irreducible :
    Irreducible linearQuarticDescentFieldPolynomial := by
  have htranslate :
      linearQuarticTranslateOne linearQuarticDescentFieldPolynomial =
        (X ^ 4 + C 4 * X ^ 3 + C 6 * X ^ 2 + C 2 * X - 2 :
          ℤ[X]) := by
    change
      linearQuarticDescentFieldPolynomial.comp (X + C (1 : ℤ)) =
        (X ^ 4 + C 4 * X ^ 3 + C 6 * X ^ 2 + C 2 * X - 2 :
          ℤ[X])
    simpa using linearQuarticDescentField_shift
  have hirrTranslated :
      Irreducible
        (linearQuarticTranslateOne linearQuarticDescentFieldPolynomial) := by
    rw [htranslate]
    exact linearQuarticDescentField_shift_irreducible
  have hirrBack :
      Irreducible
        (linearQuarticTranslateOne.symm
          (linearQuarticTranslateOne
            linearQuarticDescentFieldPolynomial)) :=
    hirrTranslated.map linearQuarticTranslateOne.symm
  simpa using hirrBack

/-- The same field polynomial is irreducible over `ℚ`. -/
theorem linearQuarticDescentFieldPolynomial_irreducible_rat :
    Irreducible
      (linearQuarticDescentFieldPolynomial.map
        (Int.castRingHom ℚ)) := by
  have hmonic : linearQuarticDescentFieldPolynomial.Monic := by
    unfold linearQuarticDescentFieldPolynomial
    monicity <;> norm_num
  exact
    hmonic.irreducible_iff_irreducible_map_fraction_map.mp
      linearQuarticDescentFieldPolynomial_irreducible

/-- The quartic field polynomial has no linear factor modulo `3`. -/
theorem linearQuarticDescentField_no_root_mod_three
    (x : ZMod 3) :
    eval x
        (linearQuarticDescentFieldPolynomial.map
          (Int.castRingHom (ZMod 3))) ≠ 0 := by
  simpa [linearQuarticDescentFieldPolynomial] using
    (show x ^ 4 - 2 * x - 1 ≠ 0 by decide +revert)

/--
The numerical Minkowski bound for a quartic field of signature `(2,1)` and
absolute discriminant `688` is strictly below `4`.
-/
theorem linearQuarticMinkowski_bound_lt_four :
    ((Nat.factorial 4 : ℝ) / (4 : ℝ) ^ 4) *
        (4 / Real.pi) * Real.sqrt 688 < 4 := by
  have hsqrt : Real.sqrt (688 : ℝ) < 27 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hquotient : 4 / Real.pi < (4 : ℝ) / 3 := by
    exact
      (div_lt_div_iff_of_pos_left (by norm_num) hpi (by norm_num)).mpr
        Real.pi_gt_three
  norm_num [Nat.factorial]
  nlinarith [Real.sqrt_nonneg (688 : ℝ)]

/-!
## Finite Selmer-mask conclusion

What follows packages the exact output of the global-to-local descent in a
form that makes the remaining general theorem explicit.  A
`LinearQuarticSchaeferStollBridge` is precisely the non-finite assertion
that actual 2-Selmer classes inject into the checked global candidate masks
and satisfy the two complete local conditions.  Given that bridge, the
four-mask upper bound is purely finite.
-/

/-- A global mask satisfying both checked local conditions. -/
def LinearQuarticAdmissibleMask (mask : Fin 16) : Prop :=
  xorRowCombination linearQuarticGlobalRowsAtTwo mask.val ∈
      linearQuarticLocalImageAtTwo ∧
    xorRowCombination linearQuarticInfinityRows mask.val ∈
      linearQuarticAllowedInfinityRows

instance (mask : Fin 16) :
    Decidable (LinearQuarticAdmissibleMask mask) := by
  unfold LinearQuarticAdmissibleMask
  infer_instance

/-- The finite admissible-mask type has exactly four elements. -/
theorem card_linearQuarticAdmissibleMask :
    Fintype.card {mask : Fin 16 // LinearQuarticAdmissibleMask mask} = 4 := by
  decide

/--
The exact non-finite Schaefer--Stoll interface needed by the checked
certificate.

Its three fields say that Selmer classes have distinct global norm-kernel
masks and that every such mask belongs to the complete local images at `2`
and infinity.  Maximal-order/class-unit exhaustion, the Kummer injection,
the local dimension formula at `2`, and the good/tame-prime theorems are
exactly what is needed to construct this object for the actual Jacobian.
-/
structure LinearQuarticSchaeferStollBridge
    (SelmerClass : Type*) [Fintype SelmerClass] where
  mask : SelmerClass → Fin 16
  mask_injective : Function.Injective mask
  mask_at_two :
    ∀ c,
      xorRowCombination linearQuarticGlobalRowsAtTwo (mask c).val ∈
        linearQuarticLocalImageAtTwo
  mask_at_infinity :
    ∀ c,
      xorRowCombination linearQuarticInfinityRows (mask c).val ∈
        linearQuarticAllowedInfinityRows

/-- The checked local intersections bound the Selmer group by four classes. -/
theorem linearQuartic_selmer_card_le_four
    (SelmerClass : Type*) [Fintype SelmerClass]
    (bridge : LinearQuarticSchaeferStollBridge SelmerClass) :
    Fintype.card SelmerClass ≤ 4 := by
  let admissible :
      SelmerClass →
        {mask : Fin 16 // LinearQuarticAdmissibleMask mask} :=
    fun c =>
      ⟨bridge.mask c,
        bridge.mask_at_two c, bridge.mask_at_infinity c⟩
  have hinjective : Function.Injective admissible := by
    intro a b hab
    apply bridge.mask_injective
    exact congrArg Subtype.val hab
  rw [← card_linearQuarticAdmissibleMask]
  exact Fintype.card_le_of_injective admissible hinjective

/--
If the point class and rational 2-torsion supply the four independent known
Kummer classes, the finite upper bound is attained.
-/
theorem linearQuartic_selmer_card_eq_four
    (SelmerClass : Type*) [Fintype SelmerClass]
    (bridge : LinearQuarticSchaeferStollBridge SelmerClass)
    (knownClasses : Fin 4 → SelmerClass)
    (hknown : Function.Injective knownClasses) :
    Fintype.card SelmerClass = 4 := by
  apply le_antisymm
  · exact linearQuartic_selmer_card_le_four SelmerClass bridge
  · simpa using Fintype.card_le_of_injective knownClasses hknown

/--
The standard Kummer exact-sequence cardinality formula now turns the
four-class bound into `rank ≤ 1` when the rational 2-torsion dimension is
one.
-/
theorem linearQuartic_rank_le_one_of_selmer_card
    (SelmerClass : Type*) [Fintype SelmerClass]
    (bridge : LinearQuarticSchaeferStollBridge SelmerClass)
    (rank : ℕ)
    (hcard :
      Fintype.card SelmerClass = 2 ^ (rank + 1)) :
    rank ≤ 1 := by
  have hpow : 2 ^ (rank + 1) ≤ 2 ^ 2 := by
    rw [← hcard]
    simpa using linearQuartic_selmer_card_le_four SelmerClass bridge
  have hexponent : rank + 1 ≤ 2 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
  omega

end

end Cuboid2
