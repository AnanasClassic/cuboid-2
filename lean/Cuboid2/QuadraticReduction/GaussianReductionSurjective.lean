import Cuboid2.QuadraticReduction.GaussianProjectiveReduction
import Mathlib.NumberTheory.Padics.Hensel

/-!
# Surjectivity of the split-37 point reductions

The basic input is a residue-form Hensel lemma for `ℤ_[37]`: a polynomial
value which vanishes modulo `37`, at a point where its derivative does not
vanish modulo `37`, has a root in the same residue disk.  It is then applied
to one affine coordinate of the two integral Weierstrass models.
-/

namespace Cuboid2
namespace GaussianReductionSurjective

noncomputable section

open GaussianProjectiveReduction

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

private theorem toZMod_eq_zero_of_norm_lt_one
    (z : ℤ_[37]) (hz : ‖z‖ < 1) :
    PadicInt.toZMod z = 0 := by
  have hdvd : (37 : ℤ_[37]) ∣ z :=
    (PadicInt.norm_lt_one_iff_dvd z).mp hz
  have hspan :
      z ∈ (Ideal.span {(37 : ℤ_[37])} : Ideal ℤ_[37]) :=
    (Ideal.mem_span_singleton).mpr hdvd
  have hker :
      z ∈ RingHom.ker (PadicInt.toZMod : ℤ_[37] →+* ZMod 37) := by
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
    exact hspan
  exact (RingHom.mem_ker.mp hker)

private theorem norm_lt_one_of_toZMod_eq_zero
    (z : ℤ_[37]) (hz : PadicInt.toZMod z = 0) :
    ‖z‖ < 1 := by
  apply (PadicInt.norm_lt_one_iff_dvd z).mpr
  rw [← Ideal.mem_span_singleton,
    ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod,
    RingHom.mem_ker]
  exact hz

private theorem norm_eq_one_of_toZMod_ne_zero
    (z : ℤ_[37]) (hz : PadicInt.toZMod z ≠ 0) :
    ‖z‖ = 1 := by
  apply le_antisymm z.property
  apply le_of_not_gt
  intro hlt
  exact hz (toZMod_eq_zero_of_norm_lt_one z hlt)

/-- Residue-form Hensel lifting over `ℤ_[37]`.

The conclusion records the residue disk explicitly, which is the datum needed
to prove that projective reduction returns the original special-fibre point.
-/
theorem exists_hensel_root_in_residue_disk
    (F : Polynomial ℤ_[37]) (a : ℤ_[37])
    (hvalue : PadicInt.toZMod (F.aeval a) = 0)
    (hderiv : PadicInt.toZMod (F.derivative.aeval a) ≠ 0) :
    ∃ z : ℤ_[37],
      F.aeval z = 0 ∧ PadicInt.toZMod z = PadicInt.toZMod a := by
  have hvalueNorm : ‖F.aeval a‖ < 1 :=
    norm_lt_one_of_toZMod_eq_zero _ hvalue
  have hderivNorm : ‖F.derivative.aeval a‖ = 1 :=
    norm_eq_one_of_toZMod_ne_zero _ hderiv
  have hnorm :
      ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [hderivNorm]
    simpa using hvalueNorm
  obtain ⟨z, hz, hza, _⟩ := hensels_lemma hnorm
  refine ⟨z, hz, ?_⟩
  have hderivNorm' :
      ‖Polynomial.eval a F.derivative‖ = 1 := by
    simpa [Polynomial.aeval_def] using hderivNorm
  have hza' : ‖z - a‖ < 1 := by
    simpa [hderivNorm'] using hza
  have hzero := toZMod_eq_zero_of_norm_lt_one (z - a) hza'
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-! ## Affine-coordinate lifts -/

/-- The canonical integral representative of a residue. -/
def residueLift (u : ZMod 37) : ℤ_[37] :=
  (u.val : ℤ_[37])

@[simp] theorem residueLift_toZMod (u : ZMod 37) :
    PadicInt.toZMod (residueLift u) = u := by
  rw [residueLift, map_natCast]
  exact ZMod.natCast_zmod_val u

/-- The equation in the `y` coordinate after fixing an integral `x`. -/
def yPolynomial (A B x : ℤ_[37]) : Polynomial ℤ_[37] :=
  Polynomial.X ^ 2 -
    Polynomial.C (x ^ 3 + A * x ^ 2 + B * x)

@[simp] theorem yPolynomial_aeval
    (A B x y : ℤ_[37]) :
    (yPolynomial A B x).aeval y =
      y ^ 2 - (x ^ 3 + A * x ^ 2 + B * x) := by
  simp [yPolynomial, Polynomial.aeval_def]

@[simp] theorem yPolynomial_derivative_aeval
    (A B x y : ℤ_[37]) :
    (yPolynomial A B x).derivative.aeval y = 2 * y := by
  simp only [yPolynomial, Polynomial.derivative_sub,
    Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.derivative_C, Nat.cast_ofNat, mul_one, sub_zero]
  simp [Polynomial.aeval_def]

/-- If the residue ordinate is nonzero, fixing the canonical lift of `x` and
Hensel-lifting `y` produces an integral point in the requested residue disk. -/
theorem exists_integral_lift_of_y_ne_zero
    (A B : ℤ_[37]) {xBar yBar : ZMod 37}
    (hcurve : (localResidueCurve A B).toAffine.Equation xBar yBar)
    (hy : yBar ≠ 0) :
    ∃ x y : ℤ_[37],
      PadicInt.toZMod x = xBar ∧
      PadicInt.toZMod y = yBar ∧
      (localCurve A B).toAffine.Equation x y := by
  let x₀ : ℤ_[37] := residueLift xBar
  let y₀ : ℤ_[37] := residueLift yBar
  let F : Polynomial ℤ_[37] := yPolynomial A B x₀
  have hcurve' :
      yBar ^ 2 =
        xBar ^ 3 + PadicInt.toZMod A * xBar ^ 2 +
          PadicInt.toZMod B * xBar := by
    have h := hcurve
    rw [WeierstrassCurve.Affine.equation_iff] at h
    simpa only [localResidueCurve, localCurve, WeierstrassCurve.map,
      map_zero, zero_mul, add_zero, zero_add] using h
  have hvalue : PadicInt.toZMod (F.aeval y₀) = 0 := by
    rw [show F.aeval y₀ =
        y₀ ^ 2 - (x₀ ^ 3 + A * x₀ ^ 2 + B * x₀) by
      simp [F, yPolynomial_aeval]]
    simp only [map_sub, map_add, map_pow, map_mul, x₀, y₀,
      residueLift_toZMod]
    exact sub_eq_zero.mpr hcurve'
  have hderiv : PadicInt.toZMod (F.derivative.aeval y₀) ≠ 0 := by
    rw [show F.derivative.aeval y₀ = 2 * y₀ by
      simp [F, yPolynomial_derivative_aeval]]
    rw [map_mul, map_ofNat, show PadicInt.toZMod y₀ = yBar by
      exact (residueLift_toZMod yBar)]
    apply mul_ne_zero
    · exact (by native_decide : (2 : ZMod 37) ≠ 0)
    · exact hy
  obtain ⟨y, hyRoot, hyRed⟩ :=
    exists_hensel_root_in_residue_disk F y₀ hvalue hderiv
  refine ⟨x₀, y, residueLift_toZMod xBar, ?_, ?_⟩
  · exact hyRed.trans (residueLift_toZMod yBar)
  · rw [WeierstrassCurve.Affine.equation_iff]
    simp only [localCurve, zero_mul, add_zero]
    have hyEq :
        y ^ 2 = x₀ ^ 3 + A * x₀ ^ 2 + B * x₀ := by
      have := hyRoot
      rw [show F.aeval y =
          y ^ 2 - (x₀ ^ 3 + A * x₀ ^ 2 + B * x₀) by
        simp [F, yPolynomial_aeval]] at this
      exact sub_eq_zero.mp this
    exact hyEq

/-- The equation in the `x` coordinate after fixing `y=0`. -/
def xPolynomial (A B : ℤ_[37]) : Polynomial ℤ_[37] :=
  Polynomial.X ^ 3 +
    Polynomial.C A * Polynomial.X ^ 2 +
    Polynomial.C B * Polynomial.X

@[simp] theorem xPolynomial_aeval
    (A B x : ℤ_[37]) :
    (xPolynomial A B).aeval x = x ^ 3 + A * x ^ 2 + B * x := by
  simp [xPolynomial, Polynomial.aeval_def]

@[simp] theorem xPolynomial_derivative_aeval
    (A B x : ℤ_[37]) :
    (xPolynomial A B).derivative.aeval x =
      3 * x ^ 2 + 2 * A * x + B := by
  simp only [xPolynomial, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X, Polynomial.derivative_C,
    Nat.cast_ofNat, mul_one, zero_mul, zero_add]
  simp [Polynomial.aeval_def]
  ring

/-- If the residue ordinate is zero and the `x`-partial is nonzero, fixing
`y=0` and Hensel-lifting `x` produces the required integral point. -/
theorem exists_integral_lift_of_y_eq_zero
    (A B : ℤ_[37]) {xBar : ZMod 37}
    (hcurve :
      (localResidueCurve A B).toAffine.Equation xBar 0)
    (hx :
      3 * xBar ^ 2 + 2 * PadicInt.toZMod A * xBar +
          PadicInt.toZMod B ≠ 0) :
    ∃ x y : ℤ_[37],
      PadicInt.toZMod x = xBar ∧
      PadicInt.toZMod y = 0 ∧
      (localCurve A B).toAffine.Equation x y := by
  let x₀ : ℤ_[37] := residueLift xBar
  let F : Polynomial ℤ_[37] := xPolynomial A B
  have hcurve' :
      xBar ^ 3 + PadicInt.toZMod A * xBar ^ 2 +
          PadicInt.toZMod B * xBar = 0 := by
    have h := hcurve
    rw [WeierstrassCurve.Affine.equation_iff] at h
    simp only [localResidueCurve, localCurve, WeierstrassCurve.map,
      map_zero, zero_mul, add_zero] at h
    exact h.symm
  have hvalue : PadicInt.toZMod (F.aeval x₀) = 0 := by
    rw [show F.aeval x₀ = x₀ ^ 3 + A * x₀ ^ 2 + B * x₀ by
      simp [F, xPolynomial_aeval]]
    simpa only [map_add, map_pow, map_mul, x₀,
      residueLift_toZMod] using hcurve'
  have hderiv : PadicInt.toZMod (F.derivative.aeval x₀) ≠ 0 := by
    rw [show F.derivative.aeval x₀ =
        3 * x₀ ^ 2 + 2 * A * x₀ + B by
      simp [F, xPolynomial_derivative_aeval]]
    simpa only [map_add, map_pow, map_mul, map_ofNat, x₀,
      residueLift_toZMod] using hx
  obtain ⟨x, hxRoot, hxRed⟩ :=
    exists_hensel_root_in_residue_disk F x₀ hvalue hderiv
  refine ⟨x, 0, hxRed.trans (residueLift_toZMod xBar), by simp, ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [localCurve, zero_mul, add_zero]
  have hxEq :
      x ^ 3 + A * x ^ 2 + B * x = 0 := by
    simpa [F, xPolynomial_aeval] using hxRoot
  exact hxEq.symm

private theorem xDerivative_ne_zero_of_nonsingular_y_zero
    (A B : ℤ_[37]) {xBar : ZMod 37}
    (h :
      (localResidueCurve A B).toAffine.Nonsingular xBar 0) :
    3 * xBar ^ 2 + 2 * PadicInt.toZMod A * xBar +
        PadicInt.toZMod B ≠ 0 := by
  have h' :=
    ((localResidueCurve A B).toAffine.nonsingular_iff' xBar 0).mp h
  simpa only [localResidueCurve, localCurve, WeierstrassCurve.map,
    map_zero, zero_mul, mul_zero, zero_add, add_zero, zero_sub,
    neg_ne_zero, ne_eq, eq_self, not_true_eq_false, or_false] using h'.2

/-- Every affine nonsingular special-fibre point has integral coordinates
lifting both residues and satisfying the integral Weierstrass equation. -/
theorem exists_integral_lift
    (A B : ℤ_[37]) {xBar yBar : ZMod 37}
    (h :
      (localResidueCurve A B).toAffine.Nonsingular xBar yBar) :
    ∃ x y : ℤ_[37],
      PadicInt.toZMod x = xBar ∧
      PadicInt.toZMod y = yBar ∧
      (localCurve A B).toAffine.Equation x y := by
  by_cases hy : yBar = 0
  · subst yBar
    exact exists_integral_lift_of_y_eq_zero A B h.1
      (xDerivative_ne_zero_of_nonsingular_y_zero A B h)
  · exact exists_integral_lift_of_y_ne_zero A B h.1 hy

private theorem padicNonsingular_of_integral
    (A B x y : ℤ_[37])
    (hcurve : (localCurve A B).toAffine.Equation x y)
    (hpartial :
      3 * x ^ 2 + 2 * A * x + B ≠ 0 ∨ y ≠ 0) :
    (localPadicCurve A B).toAffine.Nonsingular
      (x : ℚ_[37]) (y : ℚ_[37]) := by
  have hInt :
      (localCurve A B).toAffine.Nonsingular x y := by
    apply ((localCurve A B).toAffine.nonsingular_iff' x y).mpr
    refine ⟨hcurve, ?_⟩
    rcases hpartial with hx | hy
    · left
      simpa only [localCurve, zero_mul, zero_sub, neg_ne_zero] using hx
    · right
      simp only [localCurve, zero_mul, add_zero]
      exact mul_ne_zero (by norm_num) hy
  have hcoe :
      Function.Injective
        (PadicInt.Coe.ringHom : ℤ_[37] →+* ℚ_[37]) := by
    intro a b hab
    exact Subtype.coe_injective hab
  change
    ((localCurve A B).toAffine.map PadicInt.Coe.ringHom).Nonsingular
      (PadicInt.Coe.ringHom x) (PadicInt.Coe.ringHom y)
  exact
    ((localCurve A B).toAffine.map_nonsingular hcoe x y).mpr hInt

/-- Projective reduction on an integral two-torsion model is surjective onto
the nonsingular special-fibre point group. -/
theorem reducePoint_surjective
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic] :
    Function.Surjective (reducePoint A B) := by
  rintro (_ | ⟨xBar, yBar, hBar⟩)
  · exact ⟨0, reducePoint_zero A B⟩
  · obtain ⟨x, y, hxRed, hyRed, hcurve⟩ :=
      exists_integral_lift A B hBar
    have hpartial :
        3 * x ^ 2 + 2 * A * x + B ≠ 0 ∨ y ≠ 0 := by
      by_cases hyBar : yBar = 0
      · left
        have hxBar :=
          xDerivative_ne_zero_of_nonsingular_y_zero A B
            (hyBar ▸ hBar)
        intro hx
        apply hxBar
        have hxMap := congrArg PadicInt.toZMod hx
        rw [map_add, map_add, map_mul, map_pow, map_mul, map_mul,
          map_ofNat, map_ofNat, hxRed] at hxMap
        simpa only [map_zero] using hxMap
      · right
        intro hy
        apply hyBar
        rw [← hyRed, hy, map_zero]
    have hPadic :
        (localPadicCurve A B).toAffine.Nonsingular
          (x : ℚ_[37]) (y : ℚ_[37]) :=
      padicNonsingular_of_integral A B x y hcurve hpartial
    let Q : (localPadicCurve A B).toAffine.Point :=
      .some (x : ℚ_[37]) (y : ℚ_[37]) hPadic
    refine ⟨Q, ?_⟩
    have hxNorm : ‖(x : ℚ_[37])‖ ≤ 1 := x.property
    simp only [Q, reducePoint]
    rw [dif_pos hxNorm]
    simp only [WeierstrassCurve.Affine.Point.mk]
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · have hxInt :
          (⟨(x : ℚ_[37]), hxNorm⟩ : ℤ_[37]) = x :=
        Subtype.ext rfl
      simpa only [hxInt] using hxRed
    · have hyNorm :
          ‖(y : ℚ_[37])‖ ≤ 1 :=
        norm_y_le_one_of_norm_x_le_one A B hPadic.1 hxNorm
      have hyInt :
          (⟨(y : ℚ_[37]), hyNorm⟩ : ℤ_[37]) = y :=
        Subtype.ext rfl
      simpa only [hyInt] using hyRed

/-- Executable finite reduction hits the canonical finite representation of
every nonsingular residue point. -/
theorem finiteReducePoint_hits_residue
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (R : (localResidueCurve A B).toAffine.Point) :
    ∃ Q : (localPadicCurve A B).toAffine.Point,
      finiteReducePoint A B Q = finitePointOfResidue R := by
  obtain ⟨Q, hQ⟩ := reducePoint_surjective A B R
  refine ⟨Q, ?_⟩
  exact congrArg finitePointOfResidue hQ

/-- Surjectivity for the `i ↦ +6 (mod 37)` split model. -/
theorem reducePoint_plus_surjective :
    Function.Surjective (reducePoint plusA plusB) :=
  reducePoint_surjective plusA plusB

/-- Surjectivity for the `i ↦ -6 (mod 37)` split model. -/
theorem reducePoint_minus_surjective :
    Function.Surjective (reducePoint minusA minusB) :=
  reducePoint_surjective minusA minusB

/-- Every canonical finite plus-model residue is produced by an actual
`37`-adic point. -/
theorem finiteReducePoint_plus_hits_residue
    (R : (localResidueCurve plusA plusB).toAffine.Point) :
    ∃ Q : (localPadicCurve plusA plusB).toAffine.Point,
      finiteReducePoint plusA plusB Q = finitePointOfResidue R :=
  finiteReducePoint_hits_residue plusA plusB R

/-- Every canonical finite minus-model residue is produced by an actual
`37`-adic point. -/
theorem finiteReducePoint_minus_hits_residue
    (R : (localResidueCurve minusA minusB).toAffine.Point) :
    ∃ Q : (localPadicCurve minusA minusB).toAffine.Point,
      finiteReducePoint minusA minusB Q = finitePointOfResidue R :=
  finiteReducePoint_hits_residue minusA minusB R

end

end GaussianReductionSurjective
end Cuboid2
