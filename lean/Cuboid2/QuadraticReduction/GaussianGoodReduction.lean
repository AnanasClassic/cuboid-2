import Cuboid2.QuadraticReduction.GaussianP37Bridge
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The two split embeddings of `ℚ(i)` at 37

This file constructs the characteristic-zero local objects used by the
split-37 good-reduction argument.  In particular, the two roots of `X²+1`
in `ℤ_[37]` are obtained from Hensel's lemma at the residues `6` and `-6`,
and then give the two honest algebra homomorphisms
`ℚ(i) →ₐ[ℚ] ℚ_[37]`.

The projective normalization of arbitrary elliptic points, and hence the
inhabitants of `Split37ProjectiveReduction` and `Split37CoverReduction`,
remain downstream of these embeddings.
-/

namespace Cuboid2
namespace GaussianGoodReduction

noncomputable section

open scoped QuadraticAlgebra
open IsDedekindDomain.HeightOneSpectrum
open WithZero Multiplicative

instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

local instance : DecidableEq ℚ_[37] := Classical.decEq _

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

/-- The integral polynomial whose two 37-adic roots realize the split prime. -/
def splitPolynomial : Polynomial ℤ := Polynomial.X ^ 2 + 1

private theorem splitPolynomial_at_six :
    splitPolynomial.aeval (6 : ℤ_[37]) = 37 := by
  norm_num [splitPolynomial]

private theorem splitPolynomial_derivative_at_six :
    splitPolynomial.derivative.aeval (6 : ℤ_[37]) = 12 := by
  have hd :
      splitPolynomial.derivative = 2 * Polynomial.X := by
    ext n
    simp [splitPolynomial, Polynomial.coeff_derivative]
  rw [hd]
  rw [map_mul, Polynomial.aeval_X]
  rw [show Polynomial.aeval (6 : ℤ_[37]) (2 : Polynomial ℤ) = 2 by
    exact Polynomial.aeval_natCast 6 2]
  norm_num

private theorem splitPolynomial_hensel_at_six :
    ‖splitPolynomial.aeval (6 : ℤ_[37])‖ <
      ‖splitPolynomial.derivative.aeval (6 : ℤ_[37])‖ ^ 2 := by
  rw [splitPolynomial_at_six, splitPolynomial_derivative_at_six]
  rw [show ‖(37 : ℤ_[37])‖ = (37 : ℝ)⁻¹ by
    exact PadicInt.norm_p]
  rw [show ‖(12 : ℤ_[37])‖ = 1 by
    exact PadicInt.norm_natCast_eq_one_iff.mpr (by norm_num)]
  norm_num

/-- The Hensel root congruent to `6` modulo 37. -/
def splitRootPlus : ℤ_[37] :=
  Classical.choose (hensels_lemma splitPolynomial_hensel_at_six)

theorem splitRootPlus_sq :
    splitRootPlus ^ 2 = -1 := by
  have h :=
    (Classical.choose_spec
      (hensels_lemma splitPolynomial_hensel_at_six)).1
  have hzero : splitRootPlus ^ 2 + 1 = 0 := by
    simpa [splitRootPlus, splitPolynomial] using h
  exact eq_neg_of_add_eq_zero_left hzero

/-- The second Hensel root, congruent to `31=-6` modulo 37. -/
def splitRootMinus : ℤ_[37] := -splitRootPlus

theorem splitRootMinus_sq :
    splitRootMinus ^ 2 = -1 := by
  rw [splitRootMinus, neg_sq, splitRootPlus_sq]

/-- The plus Hensel root lies in the residue disk of `6`. -/
theorem splitRootPlus_norm_sub_six :
    ‖splitRootPlus - 6‖ < 1 := by
  have hdist :=
    (Classical.choose_spec
      (hensels_lemma splitPolynomial_hensel_at_six)).2.1
  change
    ‖splitRootPlus - 6‖ <
      ‖splitPolynomial.derivative.aeval (6 : ℤ_[37])‖ at hdist
  rw [splitPolynomial_derivative_at_six] at hdist
  rwa [show ‖(12 : ℤ_[37])‖ = 1 by
    exact PadicInt.norm_natCast_eq_one_iff.mpr (by norm_num)] at hdist

/-- Reduction of the plus Hensel root is the chosen split root `6`. -/
theorem splitRootPlus_toZMod :
    PadicInt.toZMod splitRootPlus = (6 : ZMod 37) := by
  have hdiv : (37 : ℤ_[37]) ∣ splitRootPlus - 6 :=
    (PadicInt.norm_lt_one_iff_dvd _).mp splitRootPlus_norm_sub_six
  have hmem :
      splitRootPlus - 6 ∈
        (Ideal.span {(37 : ℤ_[37])} : Ideal ℤ_[37]) :=
    (Ideal.mem_span_singleton).mpr hdiv
  have hker :
      splitRootPlus - 6 ∈
        RingHom.ker (PadicInt.toZMod : ℤ_[37] →+* ZMod 37) := by
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
    exact hmem
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hker
  simpa only [map_ofNat] using hker

/-- Reduction of the minus Hensel root is `31=-6`. -/
theorem splitRootMinus_toZMod :
    PadicInt.toZMod splitRootMinus = (31 : ZMod 37) := by
  rw [splitRootMinus, map_neg, splitRootPlus_toZMod]
  native_decide

/-- The plus split embedding `ℚ(i) → ℚ_37`, characterized by `i ↦ r₊`. -/
def gaussianToPadicPlus : GaussianRat →ₐ[ℚ] ℚ_[37] :=
  QuadraticAlgebra.lift
    ⟨(splitRootPlus : ℚ_[37]), by
      norm_num
      have hs : splitRootPlus * splitRootPlus = -1 := by
        simpa [pow_two] using splitRootPlus_sq
      have hc := congrArg (fun z : ℤ_[37] => (z : ℚ_[37])) hs
      simpa using hc⟩

/-- The minus split embedding `ℚ(i) → ℚ_37`, characterized by `i ↦ r₋`. -/
def gaussianToPadicMinus : GaussianRat →ₐ[ℚ] ℚ_[37] :=
  QuadraticAlgebra.lift
    ⟨(splitRootMinus : ℚ_[37]), by
      norm_num
      have hs : splitRootMinus * splitRootMinus = -1 := by
        simpa [pow_two] using splitRootMinus_sq
      have hc := congrArg (fun z : ℤ_[37] => (z : ℚ_[37])) hs
      simpa using hc⟩

@[simp] theorem gaussianToPadicPlus_i :
    gaussianToPadicPlus gaussianI = (splitRootPlus : ℚ_[37]) := by
  change
    (0 : ℚ) • (1 : ℚ_[37]) +
        (1 : ℚ) • (splitRootPlus : ℚ_[37]) =
      (splitRootPlus : ℚ_[37])
  simp

@[simp] theorem gaussianToPadicMinus_i :
    gaussianToPadicMinus gaussianI = (splitRootMinus : ℚ_[37]) := by
  change
    (0 : ℚ) • (1 : ℚ_[37]) +
        (1 : ℚ) • (splitRootMinus : ℚ_[37]) =
      (splitRootMinus : ℚ_[37])
  simp

@[simp] theorem gaussianToPadicPlus_natCast (n : ℕ) :
    gaussianToPadicPlus (n : GaussianRat) = (n : ℚ_[37]) :=
  map_natCast gaussianToPadicPlus n

@[simp] theorem gaussianToPadicMinus_natCast (n : ℕ) :
    gaussianToPadicMinus (n : GaussianRat) = (n : ℚ_[37]) :=
  map_natCast gaussianToPadicMinus n

@[simp] theorem gaussianToPadicPlus_two :
    gaussianToPadicPlus (2 : GaussianRat) = (2 : ℚ_[37]) :=
  gaussianToPadicPlus_natCast 2

@[simp] theorem gaussianToPadicPlus_four :
    gaussianToPadicPlus (4 : GaussianRat) = (4 : ℚ_[37]) :=
  gaussianToPadicPlus_natCast 4

@[simp] theorem gaussianToPadicMinus_two :
    gaussianToPadicMinus (2 : GaussianRat) = (2 : ℚ_[37]) :=
  gaussianToPadicMinus_natCast 2

@[simp] theorem gaussianToPadicMinus_four :
    gaussianToPadicMinus (4 : GaussianRat) = (4 : ℚ_[37]) :=
  gaussianToPadicMinus_natCast 4

/-! ## Integral and residue models -/

/-- The integral `E₀` model at the plus prime over 37. -/
def gaussianE0IntegralPlus : WeierstrassCurve ℤ_[37] where
  a₁ := 0
  a₂ := 2 * splitRootPlus
  a₃ := 0
  a₄ := -2 - 4 * splitRootPlus
  a₆ := 0

/-- The integral `E₀` model at the minus prime over 37. -/
def gaussianE0IntegralMinus : WeierstrassCurve ℤ_[37] where
  a₁ := 0
  a₂ := 2 * splitRootMinus
  a₃ := 0
  a₄ := -2 - 4 * splitRootMinus
  a₆ := 0

/-- The plus special fibre over `𝔽₃₇`. -/
def gaussianE0ResiduePlus : WeierstrassCurve (ZMod 37) :=
  gaussianE0IntegralPlus.map PadicInt.toZMod

/-- The minus special fibre over `𝔽₃₇`. -/
def gaussianE0ResidueMinus : WeierstrassCurve (ZMod 37) :=
  gaussianE0IntegralMinus.map PadicInt.toZMod

/-- The plus special fibre has exactly the coefficients used by the finite
certificate.
-/
theorem gaussianE0ResiduePlus_coefficients :
    gaussianE0ResiduePlus.a₁ = 0 ∧
      gaussianE0ResiduePlus.a₂ = 12 ∧
      gaussianE0ResiduePlus.a₃ = 0 ∧
      gaussianE0ResiduePlus.a₄ = 11 ∧
      gaussianE0ResiduePlus.a₆ = 0 := by
  simp [gaussianE0ResiduePlus, gaussianE0IntegralPlus,
    splitRootPlus_toZMod]
  simp only [map_ofNat]
  native_decide

/-- The minus special fibre has exactly the coefficients used by the finite
certificate.
-/
theorem gaussianE0ResidueMinus_coefficients :
    gaussianE0ResidueMinus.a₁ = 0 ∧
      gaussianE0ResidueMinus.a₂ = 25 ∧
      gaussianE0ResidueMinus.a₃ = 0 ∧
      gaussianE0ResidueMinus.a₄ = 22 ∧
      gaussianE0ResidueMinus.a₆ = 0 := by
  simp [gaussianE0ResidueMinus, gaussianE0IntegralMinus,
    splitRootMinus_toZMod]
  simp only [map_ofNat]
  native_decide

private theorem gaussianE0ResiduePlus_discriminant_ne_zero :
    gaussianE0ResiduePlus.Δ ≠ 0 := by
  simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    gaussianE0ResiduePlus, gaussianE0IntegralPlus, splitRootPlus_toZMod]
  simp only [map_ofNat]
  native_decide

private theorem gaussianE0ResidueMinus_discriminant_ne_zero :
    gaussianE0ResidueMinus.Δ ≠ 0 := by
  simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    gaussianE0ResidueMinus, gaussianE0IntegralMinus, splitRootMinus_toZMod]
  simp only [map_ofNat]
  native_decide

/-- The plus special fibre is nonsingular. -/
instance gaussianE0ResiduePlus_isElliptic :
    gaussianE0ResiduePlus.IsElliptic where
  isUnit :=
    isUnit_iff_ne_zero.mpr gaussianE0ResiduePlus_discriminant_ne_zero

/-- The minus special fibre is nonsingular. -/
instance gaussianE0ResidueMinus_isElliptic :
    gaussianE0ResidueMinus.IsElliptic where
  isUnit :=
    isUnit_iff_ne_zero.mpr gaussianE0ResidueMinus_discriminant_ne_zero

/-- The discriminant of the plus integral model is a 37-adic unit.  This is
the concrete good-reduction statement before choosing a minimal model.
-/
theorem gaussianE0IntegralPlus_discriminant_isUnit :
    IsUnit gaussianE0IntegralPlus.Δ := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hmem
  have hker :
      gaussianE0IntegralPlus.Δ ∈
        RingHom.ker (PadicInt.toZMod : ℤ_[37] →+* ZMod 37) := by
    rw [PadicInt.ker_toZMod]
    exact hmem
  have hzero :
      PadicInt.toZMod gaussianE0IntegralPlus.Δ = 0 :=
    RingHom.mem_ker.mp hker
  apply gaussianE0ResiduePlus_discriminant_ne_zero
  change
    (gaussianE0IntegralPlus.map PadicInt.toZMod).Δ = 0
  rw [WeierstrassCurve.map_Δ]
  exact hzero

/-- The discriminant of the minus integral model is a 37-adic unit. -/
theorem gaussianE0IntegralMinus_discriminant_isUnit :
    IsUnit gaussianE0IntegralMinus.Δ := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hmem
  have hker :
      gaussianE0IntegralMinus.Δ ∈
        RingHom.ker (PadicInt.toZMod : ℤ_[37] →+* ZMod 37) := by
    rw [PadicInt.ker_toZMod]
    exact hmem
  have hzero :
      PadicInt.toZMod gaussianE0IntegralMinus.Δ = 0 :=
    RingHom.mem_ker.mp hker
  apply gaussianE0ResidueMinus_discriminant_ne_zero
  change
    (gaussianE0IntegralMinus.map PadicInt.toZMod).Δ = 0
  rw [WeierstrassCurve.map_Δ]
  exact hzero

/-! ## Base change of the actual elliptic curve -/

/-- The plus 37-adic base change of `E₀`. -/
abbrev gaussianE0PadicPlus : WeierstrassCurve ℚ_[37] :=
  gaussianE0.map gaussianToPadicPlus.toRingHom

/-- The minus 37-adic base change of `E₀`. -/
abbrev gaussianE0PadicMinus : WeierstrassCurve ℚ_[37] :=
  gaussianE0.map gaussianToPadicMinus.toRingHom

/-- The displayed plus integral model base-changes to the actual plus
37-adic curve.
-/
theorem gaussianE0IntegralPlus_baseChange :
    gaussianE0IntegralPlus.map (algebraMap ℤ_[37] ℚ_[37]) =
      gaussianE0PadicPlus := by
  ext <;>
    simp [gaussianE0IntegralPlus, gaussianE0PadicPlus, gaussianE0,
      gaussianToPadicPlus_i, PadicInt.algebraMap_apply]
  · exact Or.inl (PadicInt.coe_natCast 2)
  · rw [show ((2 : ℤ_[37]) : ℚ_[37]) = 2 from
        PadicInt.coe_natCast 2,
      show ((4 : ℤ_[37]) : ℚ_[37]) = 4 from
        PadicInt.coe_natCast 4]

/-- The displayed minus integral model base-changes to the actual minus
37-adic curve.
-/
theorem gaussianE0IntegralMinus_baseChange :
    gaussianE0IntegralMinus.map (algebraMap ℤ_[37] ℚ_[37]) =
      gaussianE0PadicMinus := by
  ext <;>
    simp [gaussianE0IntegralMinus, gaussianE0PadicMinus, gaussianE0,
      gaussianToPadicMinus_i, PadicInt.algebraMap_apply]
  · exact Or.inl (PadicInt.coe_natCast 2)
  · rw [show ((2 : ℤ_[37]) : ℚ_[37]) = 2 from
        PadicInt.coe_natCast 2,
      show ((4 : ℤ_[37]) : ℚ_[37]) = 4 from
        PadicInt.coe_natCast 4]

/-- The actual plus 37-adic curve has an explicit integral model. -/
instance gaussianE0PadicPlus_isIntegral :
    WeierstrassCurve.IsIntegral ℤ_[37] gaussianE0PadicPlus where
  integral :=
    ⟨gaussianE0IntegralPlus,
      gaussianE0IntegralPlus_baseChange.symm⟩

/-- The actual minus 37-adic curve has an explicit integral model. -/
instance gaussianE0PadicMinus_isIntegral :
    WeierstrassCurve.IsIntegral ℤ_[37] gaussianE0PadicMinus where
  integral :=
    ⟨gaussianE0IntegralMinus,
      gaussianE0IntegralMinus_baseChange.symm⟩

/-- The plus p-adic discriminant has valuation one. -/
theorem gaussianE0PadicPlus_discriminant_valuation :
    valuation ℚ_[37] (IsDiscreteValuationRing.maximalIdeal ℤ_[37])
      gaussianE0PadicPlus.Δ = 1 := by
  rw [← gaussianE0IntegralPlus_baseChange, WeierstrassCurve.map_Δ]
  exact
    Valuation.Integers.one_of_isUnit'
      gaussianE0IntegralPlus_discriminant_isUnit
      (valuation_le_one
        (R := ℤ_[37]) (K := ℚ_[37])
        (IsDiscreteValuationRing.maximalIdeal ℤ_[37]))

/-- The minus p-adic discriminant has valuation one. -/
theorem gaussianE0PadicMinus_discriminant_valuation :
    valuation ℚ_[37] (IsDiscreteValuationRing.maximalIdeal ℤ_[37])
      gaussianE0PadicMinus.Δ = 1 := by
  rw [← gaussianE0IntegralMinus_baseChange, WeierstrassCurve.map_Δ]
  exact
    Valuation.Integers.one_of_isUnit'
      gaussianE0IntegralMinus_discriminant_isUnit
      (valuation_le_one
        (R := ℤ_[37]) (K := ℚ_[37])
        (IsDiscreteValuationRing.maximalIdeal ℤ_[37]))

/-- The displayed plus model is minimal: its discriminant already has the
maximal possible integral valuation, namely one.
-/
instance gaussianE0PadicPlus_isMinimal :
    WeierstrassCurve.IsMinimal ℤ_[37] gaussianE0PadicPlus where
  val_Δ_maximal := by
    refine ⟨?_, ?_⟩
    · simpa using gaussianE0PadicPlus_isIntegral
    intro C hC hle
    have hself :
        WeierstrassCurve.valuation_Δ_aux ℤ_[37]
          gaussianE0PadicPlus =
            (⟨1, le_rfl⟩ :
              {v : ℤᵐ⁰ // v ≤ 1}) := by
      apply Subtype.ext
      rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral,
        gaussianE0PadicPlus_discriminant_valuation]
    simp only [one_smul]
    rw [hself]
    change
      (↑(WeierstrassCurve.valuation_Δ_aux ℤ_[37]
        (C • gaussianE0PadicPlus)) : ℤᵐ⁰) ≤ 1
    exact
      (WeierstrassCurve.valuation_Δ_aux ℤ_[37]
        (C • gaussianE0PadicPlus)).property

/-- The displayed minus model is minimal for the same reason. -/
instance gaussianE0PadicMinus_isMinimal :
    WeierstrassCurve.IsMinimal ℤ_[37] gaussianE0PadicMinus where
  val_Δ_maximal := by
    refine ⟨?_, ?_⟩
    · simpa using gaussianE0PadicMinus_isIntegral
    intro C hC hle
    have hself :
        WeierstrassCurve.valuation_Δ_aux ℤ_[37]
          gaussianE0PadicMinus =
            (⟨1, le_rfl⟩ :
              {v : ℤᵐ⁰ // v ≤ 1}) := by
      apply Subtype.ext
      rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral,
        gaussianE0PadicMinus_discriminant_valuation]
    simp only [one_smul]
    rw [hself]
    change
      (↑(WeierstrassCurve.valuation_Δ_aux ℤ_[37]
        (C • gaussianE0PadicMinus)) : ℤᵐ⁰) ≤ 1
    exact
      (WeierstrassCurve.valuation_Δ_aux ℤ_[37]
        (C • gaussianE0PadicMinus)).property

/-- The actual plus local curve has good reduction at 37. -/
instance gaussianE0PadicPlus_hasGoodReduction :
    gaussianE0PadicPlus.HasGoodReduction ℤ_[37] where
  goodReduction := gaussianE0PadicPlus_discriminant_valuation

/-- The actual minus local curve has good reduction at 37. -/
instance gaussianE0PadicMinus_hasGoodReduction :
    gaussianE0PadicMinus.HasGoodReduction ℤ_[37] where
  goodReduction := gaussianE0PadicMinus_discriminant_valuation

/-- Base change of actual `E₀(ℚ(i))` points through the plus split embedding.
This is an honest group homomorphism, supplied by Mathlib's affine point
base-change theorem.
-/
def mapE0PointPlus :
    gaussianE0.toAffine.Point →+
      gaussianE0PadicPlus.toAffine.Point := by
  letI : Algebra GaussianRat ℚ_[37] :=
    gaussianToPadicPlus.toRingHom.toAlgebra
  exact
    WeierstrassCurve.Affine.Point.map
      (W' := gaussianE0.toAffine)
      (R := GaussianRat) (S := GaussianRat)
      (F := GaussianRat) (K := ℚ_[37])
      (Algebra.ofId GaussianRat ℚ_[37])

/-- Base change of actual `E₀(ℚ(i))` points through the minus split embedding. -/
def mapE0PointMinus :
    gaussianE0.toAffine.Point →+
      gaussianE0PadicMinus.toAffine.Point := by
  letI : Algebra GaussianRat ℚ_[37] :=
    gaussianToPadicMinus.toRingHom.toAlgebra
  exact
    WeierstrassCurve.Affine.Point.map
      (W' := gaussianE0.toAffine)
      (R := GaussianRat) (S := GaussianRat)
      (F := GaussianRat) (K := ℚ_[37])
      (Algebra.ofId GaussianRat ℚ_[37])

end

end GaussianGoodReduction
end Cuboid2
