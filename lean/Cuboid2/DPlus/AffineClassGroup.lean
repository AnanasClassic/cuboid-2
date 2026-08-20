import Cuboid2.DPlus.Cantor
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# The affine ideal class attached to a `D+` Mumford pair

This file realizes the checked fixed-curve Cantor presentation in the
class group of the actual affine coordinate ring

`ℚ[X, Y] / (Y² - (4X⁵ - 8X² + 5X))`.

The construction is deliberately affine.  It does not identify this class
group with a projective Jacobian and makes no rank or completeness claim.
-/

namespace Cuboid2

open Polynomial
open scoped nonZeroDivisors

noncomputable section

/-- The equation of `D+`, viewed as a polynomial in the ordinate `Y`. -/
def dplusAffinePolynomial : ℚ[X][X] :=
  X ^ 2 - C dplusPolynomial

/-- The affine coordinate ring `ℚ[X,Y]/(Y²-dplusPolynomial)`. -/
abbrev DPlusAffineRing : Type :=
  AdjoinRoot dplusAffinePolynomial

/-- The function field of the affine `D+` coordinate ring. -/
abbrev DPlusAffineFunctionField : Type :=
  FractionRing DPlusAffineRing

private theorem dplusPolynomial_natDegree :
    dplusPolynomial.natDegree = 5 := by
  change
    (C 4 * X ^ 5 - C 8 * X ^ 2 + C 5 * X : ℚ[X]).natDegree = 5
  compute_degree <;> norm_num

private theorem dplusPolynomial_ne_zero :
    dplusPolynomial ≠ 0 := by
  intro h
  have := congrArg Polynomial.natDegree h
  simp [dplusPolynomial_natDegree] at this

private theorem dplusPolynomial_not_square_ratFunc
    (b : RatFunc ℚ) :
    b ^ 2 ≠ algebraMap ℚ[X] (RatFunc ℚ) dplusPolynomial := by
  intro h
  have hrhs :
      algebraMap ℚ[X] (RatFunc ℚ) dplusPolynomial ≠ 0 := by
    intro h
    apply dplusPolynomial_ne_zero
    apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
    simpa using h
  have hb : b ≠ 0 := by
    intro hb
    apply hrhs
    simpa [hb] using h.symm
  have hdeg := congrArg RatFunc.intDegree h
  rw [pow_two, RatFunc.intDegree_mul hb hb,
    RatFunc.intDegree_polynomial, dplusPolynomial_natDegree] at hdeg
  omega

private theorem dplusAffinePolynomial_monic :
    dplusAffinePolynomial.Monic := by
  simpa [dplusAffinePolynomial] using
    (monic_X_pow_sub_C dplusPolynomial (by decide : (2 : ℕ) ≠ 0))

private theorem dplusAffinePolynomial_irreducible :
    Irreducible dplusAffinePolynomial := by
  rw [dplusAffinePolynomial_monic.irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc ℚ)]
  have hirr :
      Irreducible
        ((X : (RatFunc ℚ)[X]) ^ 2 -
          C (algebraMap ℚ[X] (RatFunc ℚ) dplusPolynomial)) :=
    X_pow_sub_C_irreducible_of_prime (by norm_num)
      dplusPolynomial_not_square_ratFunc
  simpa [dplusAffinePolynomial] using hirr

/-- The explicit affine coordinate ring of `D+` is an integral domain. -/
noncomputable instance : IsDomain DPlusAffineRing :=
  AdjoinRoot.isDomain_of_prime dplusAffinePolynomial_irreducible.prime

private def dplusSquarefreeA : ℚ[X] :=
  C (-37 / 850) + C (45 / 17) * X + C (54 / 17) * X ^ 2 +
    C (239 / 85) * X ^ 3

private def dplusSquarefreeB : ℚ[X] :=
  C (1 / 5) + C (581 / 850) * X - C (9 / 17) * X ^ 2 -
    C (54 / 85) * X ^ 3 - C (239 / 425) * X ^ 4

/--
An exact squarefreeness certificate for the fixed degree-five right-hand
side.  It is kept as a Bézout identity because this is precisely the form
needed to prove invertibility of all admissible Mumford ideals.
-/
private theorem dplus_squarefree_bezout :
    dplusSquarefreeA * dplusPolynomial +
        dplusSquarefreeB * derivative dplusPolynomial = 1 := by
  apply Polynomial.funext
  intro x
  simp [dplusSquarefreeA, dplusSquarefreeB, dplusPolynomial]
  ring

/-- The quotient `(f-v²)/u` carried by an admissible Cantor pair. -/
private def dplusCantorQuotient (D : DPlusCantorPair) : ℚ[X] :=
  Classical.choose D.property

private theorem dplusCantorQuotient_spec (D : DPlusCantorPair) :
    dplusPolynomial - D.1.v ^ 2 =
      D.1.u * dplusCantorQuotient D :=
  Classical.choose_spec D.property

private theorem dplusCantor_u_ne_zero (D : DPlusCantorPair) :
    D.1.u ≠ 0 := by
  intro hu
  have hsquare : dplusPolynomial = D.1.v ^ 2 := by
    have h := dplusCantorQuotient_spec D
    rw [hu, zero_mul, sub_eq_zero] at h
    exact h
  have hdegree := congrArg Polynomial.natDegree hsquare
  rw [dplusPolynomial_natDegree, Polynomial.natDegree_pow] at hdegree
  omega

set_option maxHeartbeats 1000000 in
/--
The fixed squarefreeness certificate specializes to the three-generator
Bézout identity needed for the ideal `(u,Y-v)`.
-/
private theorem dplusCantor_bezout (D : DPlusCantorPair) :
    ∃ s t w : ℚ[X],
      s * D.1.u + t * (2 * D.1.v) +
        w * dplusCantorQuotient D = 1 := by
  let u := D.1.u
  let v := D.1.v
  let q := dplusCantorQuotient D
  let A := dplusSquarefreeA
  let B := dplusSquarefreeB
  refine
    ⟨A * q + B * derivative q,
      A * (C (1 / 2 : ℚ) * v) + B * derivative v,
      B * derivative u, ?_⟩
  have hcurve : dplusPolynomial = v ^ 2 + u * q := by
    dsimp [u, v, q]
    linear_combination dplusCantorQuotient_spec D
  have hderiv := congrArg derivative hcurve
  simp only [map_add, derivative_mul, derivative_pow, Nat.cast_ofNat,
    Nat.reduceSubDiff] at hderiv
  have hC2 : (C (2 : ℚ) : ℚ[X]) = 2 :=
    Polynomial.C_ofNat 2
  rw [pow_one, hC2] at hderiv
  change
    (A * q + B * derivative q) * u +
        (A * (C (1 / 2 : ℚ) * v) + B * derivative v) * (2 * v) +
        (B * derivative u) * q = 1
  calc
    _ =
        A * (v ^ 2 + u * q) +
          B * (2 * v * derivative v +
            (derivative u * q + u * derivative q)) := by
          rw [← hC2]
          have hhalf :
              (C (1 / 2 : ℚ) : ℚ[X]) * C 2 = 1 := by
            rw [← C_mul]
            norm_num
          linear_combination A * v ^ 2 * hhalf
    _ = A * dplusPolynomial + B * derivative dplusPolynomial := by
      rw [← hcurve, ← hderiv]
    _ = 1 := dplus_squarefree_bezout

/-- The image of an `X`-polynomial in the affine coordinate ring. -/
private def dplusAffineOf (p : ℚ[X]) : DPlusAffineRing :=
  AdjoinRoot.of dplusAffinePolynomial p

@[simp] private theorem dplusAffineOf_mul (p q : ℚ[X]) :
    dplusAffineOf (p * q) =
      dplusAffineOf p * dplusAffineOf q :=
  map_mul (AdjoinRoot.of dplusAffinePolynomial) p q

@[simp] private theorem dplusAffineOf_add (p q : ℚ[X]) :
    dplusAffineOf (p + q) =
      dplusAffineOf p + dplusAffineOf q :=
  map_add (AdjoinRoot.of dplusAffinePolynomial) p q

@[simp] private theorem dplusAffineOf_neg (p : ℚ[X]) :
    dplusAffineOf (-p) = -dplusAffineOf p :=
  map_neg (AdjoinRoot.of dplusAffinePolynomial) p

@[simp] private theorem dplusAffineOf_one :
    dplusAffineOf (1 : ℚ[X]) = 1 :=
  map_one (AdjoinRoot.of dplusAffinePolynomial)

/-- The ordinate class in the affine coordinate ring. -/
private def dplusAffineY : DPlusAffineRing :=
  AdjoinRoot.root dplusAffinePolynomial

private theorem dplusAffineY_sq :
    dplusAffineY ^ 2 = dplusAffineOf dplusPolynomial := by
  have h := AdjoinRoot.eval₂_root dplusAffinePolynomial
  change
    eval₂ (AdjoinRoot.of dplusAffinePolynomial)
      (AdjoinRoot.root dplusAffinePolynomial)
      (X ^ 2 - C dplusPolynomial) = 0 at h
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

private theorem dplusAffineOf_injective :
    Function.Injective dplusAffineOf :=
  AdjoinRoot.of.injective_of_degree_ne_zero
    (by
      rw [dplusAffinePolynomial,
        degree_X_pow_sub_C (by norm_num : 0 < (2 : ℕ))]
      norm_num)

private theorem dplusAffineOf_ne_zero
    {p : ℚ[X]} (hp : p ≠ 0) :
    dplusAffineOf p ≠ 0 :=
  fun h ↦ hp (dplusAffineOf_injective
    (h.trans (map_zero (AdjoinRoot.of dplusAffinePolynomial)).symm))

/-- The affine ideal `(u,Y+v)` represented by an admissible Mumford pair. -/
private def dplusMumfordIdeal (D : DPlusCantorPair) :
    Ideal DPlusAffineRing :=
  Ideal.span
    {dplusAffineOf D.1.u,
      dplusAffineY + dplusAffineOf D.1.v}

/-- The conjugate affine ideal `(u,Y-v)`. -/
private def dplusMumfordConjugateIdeal (D : DPlusCantorPair) :
    Ideal DPlusAffineRing :=
  Ideal.span
    {dplusAffineOf D.1.u,
      dplusAffineY - dplusAffineOf D.1.v}

private theorem dplusMumfordIdeal_mul_conjugate
    (D : DPlusCantorPair) :
    dplusMumfordIdeal D * dplusMumfordConjugateIdeal D =
      Ideal.span {dplusAffineOf D.1.u} := by
  let a := dplusAffineOf D.1.u
  let b := dplusAffineY
  let c := dplusAffineOf D.1.v
  let q := dplusAffineOf (dplusCantorQuotient D)
  have hlast : (b + c) * (b - c) = a * q := by
    dsimp [a, b, c, q]
    have hspec := congrArg dplusAffineOf
      (dplusCantorQuotient_spec D)
    change
      AdjoinRoot.of dplusAffinePolynomial
          (dplusPolynomial - D.1.v ^ 2) =
        AdjoinRoot.of dplusAffinePolynomial
          (D.1.u * dplusCantorQuotient D) at hspec
    simp only [map_sub, map_mul, map_pow] at hspec
    calc
      (dplusAffineY + dplusAffineOf D.1.v) *
          (dplusAffineY - dplusAffineOf D.1.v) =
        dplusAffineY ^ 2 - dplusAffineOf D.1.v ^ 2 := by ring
      _ = dplusAffineOf dplusPolynomial -
          dplusAffineOf D.1.v ^ 2 := by rw [dplusAffineY_sq]
      _ = dplusAffineOf D.1.u *
          dplusAffineOf (dplusCantorQuotient D) := hspec
  apply le_antisymm
  · rw [dplusMumfordIdeal, dplusMumfordConjugateIdeal,
      Ideal.span_pair_mul_span_pair]
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Ideal.mem_span_singleton.mpr ⟨a, by simp [a]⟩
    · exact Ideal.mem_span_singleton.mpr
        ⟨b - c, by simp only [b, c]⟩
    · exact Ideal.mem_span_singleton.mpr
        ⟨b + c, by simp only [b, c]; ring⟩
    · exact Ideal.mem_span_singleton.mpr
        ⟨q, by rw [hlast]⟩
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    have haI : a ∈ dplusMumfordIdeal D := by
      apply Ideal.subset_span
      simp [a]
    have haJ : a ∈ dplusMumfordConjugateIdeal D := by
      apply Ideal.subset_span
      simp [a]
    have hbplusI : b + c ∈ dplusMumfordIdeal D := by
      apply Ideal.subset_span
      simp [b, c]
    have hbminusJ : b - c ∈ dplusMumfordConjugateIdeal D := by
      apply Ideal.subset_span
      simp [b, c]
    let product :=
      dplusMumfordIdeal D * dplusMumfordConjugateIdeal D
    have haa : a * a ∈ product :=
      Ideal.mul_mem_mul haI haJ
    have haminus : a * (b - c) ∈ product :=
      Ideal.mul_mem_mul haI hbminusJ
    have hplusa : (b + c) * a ∈ product :=
      Ideal.mul_mem_mul hbplusI haJ
    have hatwoc : a * (2 * c) ∈ product := by
      have := product.sub_mem hplusa haminus
      convert this using 1
      all_goals ring
    have haq : a * q ∈ product := by
      rw [← hlast]
      exact Ideal.mul_mem_mul hbplusI hbminusJ
    rcases dplusCantor_bezout D with ⟨s, t, w, hbezout⟩
    have hbezout' := congrArg dplusAffineOf hbezout
    change
      AdjoinRoot.of dplusAffinePolynomial
          (s * D.1.u + t * (2 * D.1.v) +
            w * dplusCantorQuotient D) =
        AdjoinRoot.of dplusAffinePolynomial 1 at hbezout'
    simp only [map_add, map_mul, map_one] at hbezout'
    have htwo : dplusAffineOf (2 : ℚ[X]) = 2 := by
      change AdjoinRoot.of dplusAffinePolynomial (2 : ℚ[X]) = 2
      exact map_ofNat (AdjoinRoot.of dplusAffinePolynomial) 2
    change
      dplusAffineOf s * a +
          dplusAffineOf t * (dplusAffineOf (2 : ℚ[X]) * c) +
          dplusAffineOf w * q = 1 at hbezout'
    rw [htwo] at hbezout'
    have hsum :
        dplusAffineOf s * (a * a) +
            dplusAffineOf t * (a * (2 * c)) +
            dplusAffineOf w * (a * q) ∈ product :=
      product.add_mem
        (product.add_mem
          (product.mul_mem_left _ haa)
          (product.mul_mem_left _ hatwoc))
        (product.mul_mem_left _ haq)
    have haeq :
        a =
          dplusAffineOf s * (a * a) +
            dplusAffineOf t * (a * (2 * c)) +
            dplusAffineOf w * (a * q) := by
      dsimp [a, c, q] at hbezout' ⊢
      calc
        dplusAffineOf D.1.u =
            dplusAffineOf D.1.u * 1 := (mul_one _).symm
        _ =
            dplusAffineOf D.1.u *
              (dplusAffineOf s * dplusAffineOf D.1.u +
                dplusAffineOf t * (2 * dplusAffineOf D.1.v) +
                dplusAffineOf w *
                  dplusAffineOf (dplusCantorQuotient D)) := by
              rw [hbezout']
        _ = _ := by ring
    change a ∈ product
    rw [haeq]
    exact hsum

/--
The invertible fractional ideal whose integral representative is
`(u,Y+v)`.
-/
private def dplusMumfordIdealUnit (D : DPlusCantorPair) :
    (FractionalIdeal DPlusAffineRing⁰ DPlusAffineFunctionField)ˣ :=
  Units.mkOfMulEqOne
    (dplusMumfordIdeal D)
    (dplusMumfordConjugateIdeal D *
      (Ideal.span {dplusAffineOf D.1.u} :
        FractionalIdeal DPlusAffineRing⁰
          DPlusAffineFunctionField)⁻¹) <| by
    rw [← mul_assoc, ← FractionalIdeal.coeIdeal_mul,
      dplusMumfordIdeal_mul_conjugate]
    exact FractionalIdeal.coe_ideal_span_singleton_mul_inv
      DPlusAffineFunctionField
      (dplusAffineOf_ne_zero (dplusCantor_u_ne_zero D))

private theorem dplusMumfordIdealUnit_coe
    (D : DPlusCantorPair) :
    (dplusMumfordIdealUnit D :
      FractionalIdeal DPlusAffineRing⁰
        DPlusAffineFunctionField) =
      dplusMumfordIdeal D :=
  rfl

/--
The conjugate invertible ideal `(u,Y-v)`.  Its class is the inverse of the
class represented by `(u,Y+v)`.
-/
private def dplusMumfordConjugateIdealUnit (D : DPlusCantorPair) :
    (FractionalIdeal DPlusAffineRing⁰ DPlusAffineFunctionField)ˣ :=
  Units.mkOfMulEqOne
    (dplusMumfordConjugateIdeal D)
    (dplusMumfordIdeal D *
      (Ideal.span {dplusAffineOf D.1.u} :
        FractionalIdeal DPlusAffineRing⁰
          DPlusAffineFunctionField)⁻¹) <| by
    rw [← mul_assoc, ← FractionalIdeal.coeIdeal_mul,
      mul_comm (dplusMumfordConjugateIdeal D),
      dplusMumfordIdeal_mul_conjugate]
    exact FractionalIdeal.coe_ideal_span_singleton_mul_inv
      DPlusAffineFunctionField
      (dplusAffineOf_ne_zero (dplusCantor_u_ne_zero D))

private theorem dplusMumfordConjugateIdealUnit_coe
    (D : DPlusCantorPair) :
    (dplusMumfordConjugateIdealUnit D :
      FractionalIdeal DPlusAffineRing⁰
        DPlusAffineFunctionField) =
      dplusMumfordConjugateIdeal D :=
  rfl

/--
The actual affine ideal class represented by an admissible fixed-curve
Mumford pair.
-/
def dplusAffinePairClass (D : DPlusCantorPair) :
    Additive (ClassGroup DPlusAffineRing) :=
  ClassGroup.mk DPlusAffineFunctionField
    (dplusMumfordIdealUnit D)

private theorem dplusAffinePairClass_conjugate_mul
    (D : DPlusCantorPair) :
    (dplusAffinePairClass D).toMul *
        (ClassGroup.mk DPlusAffineFunctionField
          (dplusMumfordConjugateIdealUnit D)) = 1 := by
  change
    ClassGroup.mk DPlusAffineFunctionField
        (dplusMumfordIdealUnit D) *
      ClassGroup.mk DPlusAffineFunctionField
        (dplusMumfordConjugateIdealUnit D) = 1
  rw [← map_mul]
  apply
    (ClassGroup.mk_eq_one_of_coe_ideal
      (I' := dplusMumfordIdeal D *
        dplusMumfordConjugateIdeal D) ?_).mpr
  · refine
      ⟨dplusAffineOf D.1.u,
        dplusAffineOf_ne_zero (dplusCantor_u_ne_zero D),
        dplusMumfordIdeal_mul_conjugate D⟩
  · rw [Units.val_mul, dplusMumfordIdealUnit_coe,
      dplusMumfordConjugateIdealUnit_coe,
      FractionalIdeal.coeIdeal_mul]

private theorem dplusCantorComposition_congruences
    {first second output : DPlusCantorPair}
    (certificate : DPlusCantorComposition first second output) :
    ∃ k₁ k₂ : ℚ[X],
      output.1.v - first.1.v = first.1.u * k₁ ∧
      output.1.v - second.1.v = second.1.u * k₂ := by
  let A := certificate.bezoutFirst
  let B := certificate.bezoutSecond
  let C₀ := certificate.bezoutSumV
  let Q := certificate.vQuotient
  let q₁ := dplusCantorQuotient first
  let q₂ := dplusCantorQuotient second
  refine
    ⟨A * (second.1.v - first.1.v) + C₀ * q₁ - Q * second.1.u,
      B * (first.1.v - second.1.v) + C₀ * q₂ - Q * first.1.u,
      ?_, ?_⟩
  · have hcurve := dplusCantorQuotient_spec first
    have hv := certificate.v_identity
    rw [certificate.u_identity] at hv
    dsimp [A, B, C₀, Q, q₁]
    linear_combination
      -hv +
        first.1.v * certificate.bezout_identity +
        certificate.bezoutSumV * hcurve
  · have hcurve := dplusCantorQuotient_spec second
    have hv := certificate.v_identity
    rw [certificate.u_identity] at hv
    dsimp [A, B, C₀, Q, q₂]
    linear_combination
      -hv +
        second.1.v * certificate.bezout_identity +
        certificate.bezoutSumV * hcurve

private theorem dplusMumfordIdeal_compose
    {first second output : DPlusCantorPair}
    (certificate : DPlusCantorComposition first second output) :
    dplusMumfordIdeal first * dplusMumfordIdeal second =
      dplusMumfordIdeal output := by
  let a₁ := dplusAffineOf first.1.u
  let a₂ := dplusAffineOf second.1.u
  let a₃ := dplusAffineOf output.1.u
  let z₁ := dplusAffineY + dplusAffineOf first.1.v
  let z₂ := dplusAffineY + dplusAffineOf second.1.v
  let z₃ := dplusAffineY + dplusAffineOf output.1.v
  rcases dplusCantorComposition_congruences certificate with
    ⟨k₁poly, k₂poly, hk₁poly, hk₂poly⟩
  let k₁ := dplusAffineOf k₁poly
  let k₂ := dplusAffineOf k₂poly
  have hk₁ := congrArg dplusAffineOf hk₁poly
  have hk₂ := congrArg dplusAffineOf hk₂poly
  change
    AdjoinRoot.of dplusAffinePolynomial
        (output.1.v - first.1.v) =
      AdjoinRoot.of dplusAffinePolynomial
        (first.1.u * k₁poly) at hk₁
  change
    AdjoinRoot.of dplusAffinePolynomial
        (output.1.v - second.1.v) =
      AdjoinRoot.of dplusAffinePolynomial
        (second.1.u * k₂poly) at hk₂
  simp only [map_sub, map_mul] at hk₁ hk₂
  change
    dplusAffineOf output.1.v - dplusAffineOf first.1.v =
      a₁ * k₁ at hk₁
  change
    dplusAffineOf output.1.v - dplusAffineOf second.1.v =
      a₂ * k₂ at hk₂
  have haout : a₃ = a₁ * a₂ := by
    dsimp [a₁, a₂, a₃]
    rw [certificate.u_identity]
    exact map_mul (AdjoinRoot.of dplusAffinePolynomial) _ _
  have ha₁mem : a₁ ∈ dplusMumfordIdeal first := by
    apply Ideal.subset_span
    simp [a₁]
  have hz₁mem : z₁ ∈ dplusMumfordIdeal first := by
    apply Ideal.subset_span
    simp [z₁]
  have ha₂mem : a₂ ∈ dplusMumfordIdeal second := by
    apply Ideal.subset_span
    simp [a₂]
  have hz₂mem : z₂ ∈ dplusMumfordIdeal second := by
    apply Ideal.subset_span
    simp [z₂]
  let product :=
    dplusMumfordIdeal first * dplusMumfordIdeal second
  have ha₁a₂ : a₁ * a₂ ∈ product :=
    Ideal.mul_mem_mul ha₁mem ha₂mem
  have ha₁z₂ : a₁ * z₂ ∈ product :=
    Ideal.mul_mem_mul ha₁mem hz₂mem
  have hz₁a₂ : z₁ * a₂ ∈ product :=
    Ideal.mul_mem_mul hz₁mem ha₂mem
  have hz₁z₂ : z₁ * z₂ ∈ product :=
    Ideal.mul_mem_mul hz₁mem hz₂mem
  have ha₃prod : a₃ ∈ product := by
    rw [haout]
    exact ha₁a₂
  apply le_antisymm
  · rw [dplusMumfordIdeal, dplusMumfordIdeal,
      Ideal.span_pair_mul_span_pair]
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have ha₃out : a₃ ∈ dplusMumfordIdeal output := by
      apply Ideal.subset_span
      simp [a₃]
    have hz₃out : z₃ ∈ dplusMumfordIdeal output := by
      apply Ideal.subset_span
      simp [z₃]
    rcases hx with rfl | rfl | rfl | rfl
    · rw [← haout]
      exact ha₃out
    · have heq :
          a₁ * z₂ = a₁ * z₃ - a₃ * k₂ := by
        dsimp [z₂, z₃]
        rw [haout]
        linear_combination -a₁ * hk₂
      rw [heq]
      exact (dplusMumfordIdeal output).sub_mem
        ((dplusMumfordIdeal output).mul_mem_left _ hz₃out)
        ((dplusMumfordIdeal output).mul_mem_right _ ha₃out)
    · have heq :
          z₁ * a₂ = z₃ * a₂ - a₃ * k₁ := by
        dsimp [z₁, z₃]
        rw [haout]
        linear_combination -a₂ * hk₁
      rw [heq]
      exact (dplusMumfordIdeal output).sub_mem
        ((dplusMumfordIdeal output).mul_mem_right _ hz₃out)
        ((dplusMumfordIdeal output).mul_mem_right _ ha₃out)
    · have heq :
          z₁ * z₂ =
            z₃ *
                (dplusAffineY + dplusAffineOf first.1.v +
                  dplusAffineOf second.1.v -
                  dplusAffineOf output.1.v) +
              a₃ * (k₁ * k₂) := by
        have hkprod := congrArg₂ (· * ·) hk₁ hk₂
        have hkprod' :
            (dplusAffineOf output.1.v -
                dplusAffineOf first.1.v) *
              (dplusAffineOf output.1.v -
                dplusAffineOf second.1.v) =
              a₃ * (k₁ * k₂) := by
          rw [hkprod, haout]
          ring
        dsimp [z₁, z₂, z₃]
        linear_combination hkprod'
      rw [heq]
      exact (dplusMumfordIdeal output).add_mem
        ((dplusMumfordIdeal output).mul_mem_right _ hz₃out)
        ((dplusMumfordIdeal output).mul_mem_right _ ha₃out)
  · rw [dplusMumfordIdeal]
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha₃prod
    · let A := dplusAffineOf certificate.bezoutFirst
      let B := dplusAffineOf certificate.bezoutSecond
      let C₀ := dplusAffineOf certificate.bezoutSumV
      let Q := dplusAffineOf certificate.vQuotient
      have hbez := congrArg dplusAffineOf
        certificate.bezout_identity
      have hv := congrArg dplusAffineOf certificate.v_identity
      change
        AdjoinRoot.of dplusAffinePolynomial
            (certificate.bezoutFirst * first.1.u +
              certificate.bezoutSecond * second.1.u +
              certificate.bezoutSumV *
                (first.1.v + second.1.v)) =
          AdjoinRoot.of dplusAffinePolynomial 1 at hbez
      change
        AdjoinRoot.of dplusAffinePolynomial
            (certificate.bezoutFirst * first.1.u *
                second.1.v +
              certificate.bezoutSecond * second.1.u *
                first.1.v +
              certificate.bezoutSumV *
                (first.1.v * second.1.v + dplusPolynomial)) =
          AdjoinRoot.of dplusAffinePolynomial
            (output.1.v +
              certificate.vQuotient * output.1.u) at hv
      simp only [map_add, map_mul, map_one] at hbez hv
      change A * a₁ + B * a₂ +
          C₀ * (dplusAffineOf first.1.v +
            dplusAffineOf second.1.v) = 1 at hbez
      change
        A * a₁ * dplusAffineOf second.1.v +
            B * a₂ * dplusAffineOf first.1.v +
            C₀ *
              (dplusAffineOf first.1.v *
                  dplusAffineOf second.1.v +
                dplusAffineOf dplusPolynomial) =
          dplusAffineOf output.1.v + Q * a₃ at hv
      have hcombo :
          A * (a₁ * z₂) + B * (z₁ * a₂) +
              C₀ * (z₁ * z₂) ∈ product :=
        product.add_mem
          (product.add_mem
            (product.mul_mem_left _ ha₁z₂)
            (product.mul_mem_left _ hz₁a₂))
          (product.mul_mem_left _ hz₁z₂)
      have heq :
          A * (a₁ * z₂) + B * (z₁ * a₂) +
              C₀ * (z₁ * z₂) =
            z₃ + Q * a₃ := by
        have hy :
            dplusAffineY * dplusAffineY =
              dplusAffineOf dplusPolynomial := by
          simpa [pow_two] using dplusAffineY_sq
        dsimp [z₁, z₂, z₃]
        calc
          _ =
              dplusAffineY *
                  (A * a₁ + B * a₂ +
                    C₀ *
                      (dplusAffineOf first.1.v +
                        dplusAffineOf second.1.v)) +
                (A * a₁ * dplusAffineOf second.1.v +
                  B * a₂ * dplusAffineOf first.1.v +
                  C₀ *
                    (dplusAffineOf first.1.v *
                        dplusAffineOf second.1.v +
                      dplusAffineY * dplusAffineY)) := by ring
          _ =
              dplusAffineY +
                (A * a₁ * dplusAffineOf second.1.v +
                  B * a₂ * dplusAffineOf first.1.v +
                  C₀ *
                    (dplusAffineOf first.1.v *
                        dplusAffineOf second.1.v +
                      dplusAffineY * dplusAffineY)) := by rw [hbez]; ring
          _ =
              dplusAffineY +
                (A * a₁ * dplusAffineOf second.1.v +
                  B * a₂ * dplusAffineOf first.1.v +
                  C₀ *
                    (dplusAffineOf first.1.v *
                        dplusAffineOf second.1.v +
                      dplusAffineOf dplusPolynomial)) := by rw [hy]
          _ = dplusAffineY +
              (dplusAffineOf output.1.v + Q * a₃) := by rw [hv]
          _ = _ := by ring
      have : z₃ + Q * a₃ ∈ product := heq ▸ hcombo
      have hQa : Q * a₃ ∈ product :=
        product.mul_mem_left Q ha₃prod
      have hz :
          z₃ = (z₃ + Q * a₃) - Q * a₃ := by ring
      change z₃ ∈ product
      rw [hz]
      exact product.sub_mem this hQa

private theorem dplusCantorReduction_bezout
    {input output : DPlusCantorPair}
    (certificate : DPlusCantorReduction input output) :
    ∃ s t w : ℚ[X],
      s * input.1.u + t * output.1.u +
        w * input.1.v = 1 := by
  let A := dplusSquarefreeA
  let B := dplusSquarefreeB
  let c := C certificate.curveScale
  refine
    ⟨A * c * output.1.u +
        B * c * derivative output.1.u,
      B * c * derivative input.1.u,
      A * input.1.v +
        B * C 2 * derivative input.1.v, ?_⟩
  have hcurve :
      dplusPolynomial =
        input.1.v ^ 2 + c * input.1.u * output.1.u := by
    dsimp [c]
    linear_combination certificate.curve_identity
  have hderiv := congrArg derivative hcurve
  simp only [map_add, derivative_mul, derivative_pow,
    Nat.cast_ofNat, Nat.reduceSubDiff] at hderiv
  have hcderiv : derivative c = 0 := by
    simp [c]
  rw [hcderiv, zero_mul, zero_add] at hderiv
  have hC2 : (C (2 : ℚ) : ℚ[X]) = 2 :=
    Polynomial.C_ofNat 2
  rw [pow_one, hC2] at hderiv
  change
    (A * c * output.1.u +
          B * c * derivative output.1.u) *
        input.1.u +
      B * c * derivative input.1.u * output.1.u +
      (A * input.1.v +
          B * C 2 * derivative input.1.v) *
        input.1.v = 1
  rw [hC2]
  calc
    _ =
        A *
            (input.1.v ^ 2 +
              c * input.1.u * output.1.u) +
          B *
            (2 * input.1.v *
                derivative input.1.v +
              c *
                (derivative input.1.u * output.1.u +
                  input.1.u * derivative output.1.u)) := by
      ring
    _ = A * dplusPolynomial +
        B * derivative dplusPolynomial := by
      rw [← hcurve]
      congr 1
      rw [hderiv]
      ring
    _ = 1 := dplus_squarefree_bezout

set_option maxHeartbeats 1000000 in
private theorem dplusMumfordIdeal_mul_reduceConjugate
    {input output : DPlusCantorPair}
    (certificate : DPlusCantorReduction input output) :
    dplusMumfordIdeal input *
        dplusMumfordConjugateIdeal output =
      Ideal.span
        {dplusAffineY + dplusAffineOf input.1.v} := by
  let a := dplusAffineOf input.1.u
  let b := dplusAffineOf output.1.u
  let c := dplusAffineOf (C certificate.curveScale)
  let z := dplusAffineY + dplusAffineOf input.1.v
  let zbar := dplusAffineY - dplusAffineOf input.1.v
  have hout :
      dplusMumfordConjugateIdeal output =
        Ideal.span {b, z} := by
    rw [dplusMumfordConjugateIdeal]
    have hv := congrArg dplusAffineOf certificate.v_identity
    change
      AdjoinRoot.of dplusAffinePolynomial (-input.1.v) =
        AdjoinRoot.of dplusAffinePolynomial
          (output.1.v +
            certificate.vQuotient * output.1.u) at hv
    simp only [map_neg, map_add, map_mul] at hv
    have hzout :
        dplusAffineY - dplusAffineOf output.1.v =
          z +
            dplusAffineOf certificate.vQuotient * b := by
      dsimp [dplusAffineOf, z, b]
      linear_combination hv
    rw [hzout]
    exact Ideal.span_pair_add_mul_left _ _ _
  have hcurve : z * zbar = c * a * b := by
    have hc := congrArg dplusAffineOf certificate.curve_identity
    change
      AdjoinRoot.of dplusAffinePolynomial
          (dplusPolynomial - input.1.v ^ 2) =
        AdjoinRoot.of dplusAffinePolynomial
          (C certificate.curveScale * input.1.u *
            output.1.u) at hc
    simp only [map_sub, map_pow, map_mul] at hc
    dsimp [z, zbar, a, b, c]
    calc
      (dplusAffineY + dplusAffineOf input.1.v) *
          (dplusAffineY - dplusAffineOf input.1.v) =
        dplusAffineY ^ 2 -
          dplusAffineOf input.1.v ^ 2 := by ring
      _ = dplusAffineOf dplusPolynomial -
          dplusAffineOf input.1.v ^ 2 := by
            rw [dplusAffineY_sq]
      _ = _ := hc
  rw [hout, dplusMumfordIdeal,
    Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · apply Ideal.mem_span_singleton.mpr
      refine
        ⟨dplusAffineOf
            (C certificate.curveScale⁻¹) * zbar, ?_⟩
      have hcunit :
          dplusAffineOf (C certificate.curveScale⁻¹) *
              dplusAffineOf (C certificate.curveScale) = 1 := by
        rw [← dplusAffineOf_mul, ← C_mul,
          inv_mul_cancel₀ certificate.curveScale_ne_zero,
          C_1, dplusAffineOf_one]
      dsimp [z, zbar, a, b, c] at hcurve ⊢
      calc
        dplusAffineOf input.1.u *
              dplusAffineOf output.1.u =
            1 *
              (dplusAffineOf input.1.u *
                dplusAffineOf output.1.u) := by simp
        _ =
            (dplusAffineOf (C certificate.curveScale⁻¹) *
              dplusAffineOf (C certificate.curveScale)) *
              (dplusAffineOf input.1.u *
                dplusAffineOf output.1.u) := by rw [hcunit]
        _ =
            dplusAffineOf (C certificate.curveScale⁻¹) *
              ((dplusAffineY + dplusAffineOf input.1.v) *
                (dplusAffineY - dplusAffineOf input.1.v)) := by
                  rw [hcurve]
                  ring
        _ = _ := by ring
    · exact Ideal.mem_span_singleton.mpr
        ⟨a, by change a * z = z * a; exact mul_comm _ _⟩
    · exact Ideal.mem_span_singleton.mpr
        ⟨b, rfl⟩
    · exact Ideal.mem_span_singleton.mpr
        ⟨z, by simp [z]⟩
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    rcases dplusCantorReduction_bezout certificate with
      ⟨s, t, w, hbezout⟩
    have hbez := congrArg dplusAffineOf hbezout
    change
      AdjoinRoot.of dplusAffinePolynomial
          (s * input.1.u + t * output.1.u +
            w * input.1.v) =
        AdjoinRoot.of dplusAffinePolynomial 1 at hbez
    simp only [map_add, map_mul, map_one] at hbez
    let S := dplusAffineOf s
    let T := dplusAffineOf t
    let W := dplusAffineOf w
    change S * a + T * b +
        W * dplusAffineOf input.1.v = 1 at hbez
    have ha_z :
        a * z ∈
          Ideal.span {a * b, a * z, z * b, z * z} :=
      Ideal.subset_span (by simp)
    have hz_b :
        z * b ∈
          Ideal.span {a * b, a * z, z * b, z * z} :=
      Ideal.subset_span (by simp)
    have hz_z :
        z * z ∈
          Ideal.span {a * b, a * z, z * b, z * z} :=
      Ideal.subset_span (by simp)
    have hab :
        a * b ∈
          Ideal.span {a * b, a * z, z * b, z * z} :=
      Ideal.subset_span (by simp)
    let P : Ideal DPlusAffineRing :=
      Ideal.span {a * b, a * z, z * b, z * z}
    have hhalf :
        dplusAffineOf (C (1 / 2 : ℚ)) * 2 = 1 := by
      have htwo :
          dplusAffineOf (C (2 : ℚ)) =
            (2 : DPlusAffineRing) := by
        change
          AdjoinRoot.of dplusAffinePolynomial (C (2 : ℚ)) = 2
        rw [Polynomial.C_ofNat]
        exact map_ofNat (AdjoinRoot.of dplusAffinePolynomial) 2
      rw [← htwo, ← dplusAffineOf_mul, ← C_mul]
      norm_num
    have hnegative_zbar :
        -(dplusAffineOf (C (1 / 2 : ℚ)) * W *
            (z * zbar)) ∈ P := by
      apply P.neg_mem
      rw [hcurve]
      convert P.mul_mem_left
        (dplusAffineOf (C (1 / 2 : ℚ)) * W * c)
        hab using 1
      all_goals ring
    have hpositive_z2 :
        dplusAffineOf (C (1 / 2 : ℚ)) * W *
            (z * z) ∈ P :=
      P.mul_mem_left
        (dplusAffineOf (C (1 / 2 : ℚ)) * W) hz_z
    have hsum :
        S * (a * z) + T * (z * b) +
            (-(dplusAffineOf (C (1 / 2 : ℚ)) * W *
              (z * zbar))) +
            dplusAffineOf (C (1 / 2 : ℚ)) * W *
              (z * z) ∈ P :=
      P.add_mem
        (P.add_mem
          (P.add_mem (P.mul_mem_left S ha_z)
            (P.mul_mem_left T hz_b))
          hnegative_zbar)
        hpositive_z2
    have heq :
        z =
          S * (a * z) + T * (z * b) +
            (-(dplusAffineOf (C (1 / 2 : ℚ)) * W *
              (z * zbar))) +
            dplusAffineOf (C (1 / 2 : ℚ)) * W *
              (z * z) := by
      have hz_sub :
          z - zbar =
            2 * dplusAffineOf input.1.v := by
        dsimp [z, zbar]
        ring
      calc
        z = z * 1 := (mul_one z).symm
        _ = z *
            (S * a + T * b +
              W * dplusAffineOf input.1.v) := by rw [hbez]
        _ =
            S * (a * z) + T * (z * b) +
              W * dplusAffineOf input.1.v * z := by ring
        _ =
            S * (a * z) + T * (z * b) +
              dplusAffineOf (C (1 / 2 : ℚ)) * W *
                z * (z - zbar) := by
          rw [hz_sub]
          have hvhalf :
              W * dplusAffineOf input.1.v * z =
                dplusAffineOf (C (1 / 2 : ℚ)) * W *
                  z * (2 * dplusAffineOf input.1.v) := by
            calc
              W * dplusAffineOf input.1.v * z =
                  (W * dplusAffineOf input.1.v * z) * 1 := by
                    simp
              _ =
                  (W * dplusAffineOf input.1.v * z) *
                    (dplusAffineOf (C (1 / 2 : ℚ)) * 2) := by
                      rw [hhalf]
              _ = _ := by ring
          linear_combination hvhalf
        _ = _ := by ring
    change z ∈ P
    rw [heq]
    exact hsum

private theorem dplusAffineY_add_ne_zero (v : ℚ[X]) :
    dplusAffineY + dplusAffineOf v ≠ 0 := by
  have houter :
      (X + C v : ℚ[X][X]) ≠ 0 :=
    X_add_C_ne_zero v
  have hdegree :
      (X + C v : ℚ[X][X]).natDegree <
        dplusAffinePolynomial.natDegree := by
    rw [natDegree_X_add_C]
    change 1 < (X ^ 2 - C dplusPolynomial : ℚ[X][X]).natDegree
    rw [natDegree_X_pow_sub_C]
    norm_num
  have h :=
    AdjoinRoot.mk_ne_zero_of_natDegree_lt
      dplusAffinePolynomial_monic houter hdegree
  change
    AdjoinRoot.mk dplusAffinePolynomial X +
      AdjoinRoot.mk dplusAffinePolynomial (C v) ≠ 0
  rw [← map_add]
  exact h

private theorem dplusAffinePairClass_compose
    {first second output : DPlusCantorPair}
    (certificate : DPlusCantorComposition first second output) :
    dplusAffinePairClass output =
      dplusAffinePairClass first +
        dplusAffinePairClass second := by
  change
    ClassGroup.mk DPlusAffineFunctionField
        (dplusMumfordIdealUnit output) =
      ClassGroup.mk DPlusAffineFunctionField
          (dplusMumfordIdealUnit first) *
        ClassGroup.mk DPlusAffineFunctionField
          (dplusMumfordIdealUnit second)
  rw [← map_mul]
  apply congrArg (ClassGroup.mk DPlusAffineFunctionField)
  apply Units.ext
  change
    (dplusMumfordIdeal output :
      FractionalIdeal DPlusAffineRing⁰
        DPlusAffineFunctionField) =
      dplusMumfordIdeal first *
        dplusMumfordIdeal second
  rw [← FractionalIdeal.coeIdeal_mul,
    dplusMumfordIdeal_compose certificate]

private theorem dplusAffinePairClass_reduce_mul_conjugate
    {input output : DPlusCantorPair}
    (certificate : DPlusCantorReduction input output) :
    (dplusAffinePairClass input).toMul *
        ClassGroup.mk DPlusAffineFunctionField
          (dplusMumfordConjugateIdealUnit output) = 1 := by
  change
    ClassGroup.mk DPlusAffineFunctionField
        (dplusMumfordIdealUnit input) *
      ClassGroup.mk DPlusAffineFunctionField
        (dplusMumfordConjugateIdealUnit output) = 1
  rw [← map_mul]
  apply
    (ClassGroup.mk_eq_one_of_coe_ideal
      (I' := dplusMumfordIdeal input *
        dplusMumfordConjugateIdeal output) ?_).mpr
  · refine
      ⟨dplusAffineY + dplusAffineOf input.1.v,
        dplusAffineY_add_ne_zero input.1.v,
        dplusMumfordIdeal_mul_reduceConjugate certificate⟩
  · rw [Units.val_mul, dplusMumfordIdealUnit_coe,
      dplusMumfordConjugateIdealUnit_coe,
      FractionalIdeal.coeIdeal_mul]

private theorem dplusAffinePairClass_reduce
    {input output : DPlusCantorPair}
    (certificate : DPlusCantorReduction input output) :
    dplusAffinePairClass output =
      dplusAffinePairClass input := by
  change
    ClassGroup.mk DPlusAffineFunctionField
        (dplusMumfordIdealUnit output) =
      ClassGroup.mk DPlusAffineFunctionField
        (dplusMumfordIdealUnit input)
  let conjugateOutput :=
    ClassGroup.mk DPlusAffineFunctionField
      (dplusMumfordConjugateIdealUnit output)
  apply mul_right_cancel (b := conjugateOutput)
  change
    (dplusAffinePairClass output).toMul *
        conjugateOutput =
      (dplusAffinePairClass input).toMul *
        conjugateOutput
  rw [dplusAffinePairClass_conjugate_mul output,
    dplusAffinePairClass_reduce_mul_conjugate certificate]

private theorem dplusMumfordIdeal_infinity :
    dplusMumfordIdeal dplusCantorInfinity = ⊤ := by
  apply
    (dplusMumfordIdeal dplusCantorInfinity).eq_top_iff_one.mpr
  apply Ideal.subset_span
  left
  simp [dplusCantorInfinity, MumfordPair.infinity]

private theorem dplusAffinePairClass_infinity :
    dplusAffinePairClass dplusCantorInfinity = 0 := by
  change
    ClassGroup.mk DPlusAffineFunctionField
        (dplusMumfordIdealUnit dplusCantorInfinity) = 1
  apply
    (ClassGroup.mk_eq_one_of_coe_ideal
      (I' := dplusMumfordIdeal dplusCantorInfinity)
      (dplusMumfordIdealUnit_coe
        dplusCantorInfinity)).mpr
  refine ⟨1, one_ne_zero, ?_⟩
  rw [dplusMumfordIdeal_infinity, Ideal.span_singleton_one]

/--
The affine coordinate-ring class group is a sound model of every relation
admitted by the fixed `D+` Cantor presentation.
-/
def dplusAffineClassGroupModel :
    DPlusCantorModel
      (Additive (ClassGroup DPlusAffineRing)) where
  pairClass := dplusAffinePairClass
  infinity_eq := dplusAffinePairClass_infinity
  composition_eq := fun certificate ↦
    dplusAffinePairClass_compose certificate
  reduction_eq := fun certificate ↦
    dplusAffinePairClass_reduce certificate

/--
The generated `11D` certificate holds in the actual class group of the
affine coordinate ring of `D+`.
-/
theorem dplusAffinePairClass_eleven_generator :
    dplusAffinePairClass dplusElevenDCantorPair =
      11 • dplusAffinePairClass dplusGeneratorCantorPair :=
  DPlusCantorModel.dplusElevenD_eq_eleven_generator
    dplusAffineClassGroupModel

end

end Cuboid2
