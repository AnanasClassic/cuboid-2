import Cuboid2.QuadraticReduction.GaussianDescent
import Cuboid2.QuadraticReduction.GaussianHeight
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Global group-theoretic assembly for the Gaussian quotients

This file isolates the formal group theory needed after the two finite
two-isogeny Selmer computations.  It deliberately does not assert those
arithmetic computations: its hypotheses are finiteness of the two genuine
Kummer-map ranges (or, equivalently for the applications below, finite index
of the two genuine isogeny images).
-/

namespace Cuboid2

noncomputable section

namespace GaussianGlobal

open scoped DirectSum

open GaussianDescent

set_option linter.style.haveILetI false

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have hxnonneg : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

local instance gaussianRatNumberField : NumberField GaussianRat where

/-! ## Finite cokernels and composition -/

/-- A composite of additive homomorphisms with finite cokernels again has
finite cokernel.  This is the group-theoretic mechanism behind multiplying
the two two-isogeny indices. -/
theorem finiteIndex_range_comp {G H K : Type*}
    [AddCommGroup G] [AddCommGroup H] [AddCommGroup K]
    (f : G →+ H) (g : H →+ K)
    [f.range.FiniteIndex] [g.range.FiniteIndex] :
    (g.comp f).range.FiniteIndex := by
  classical
  let Qg := K ⧸ g.range
  let Qf := H ⧸ f.range
  let Qgf := K ⧸ (g.comp f).range
  let reps : Qg × Qf → Qgf :=
    fun q ↦ QuotientAddGroup.mk (q.1.out + g q.2.out)
  have hreps : Function.Surjective reps := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective q
    let qg : Qg := QuotientAddGroup.mk k
    have hkg : k - qg.out ∈ g.range := by
      apply QuotientAddGroup.eq_iff_sub_mem.mp
      simpa only [qg] using (QuotientAddGroup.out_eq' qg).symm
    obtain ⟨h, hh⟩ := hkg
    let qf : Qf := QuotientAddGroup.mk h
    have hhf : h - qf.out ∈ f.range := by
      apply QuotientAddGroup.eq_iff_sub_mem.mp
      simpa only [qf] using (QuotientAddGroup.out_eq' qf).symm
    obtain ⟨x, hx⟩ := hhf
    refine ⟨(qg, qf), ?_⟩
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    refine ⟨-x, ?_⟩
    dsimp only [reps]
    change g (f (-x)) = qg.out + g qf.out - k
    rw [map_neg, map_neg, hx, map_sub, hh]
    abel
  letI : Finite Qg := inferInstance
  letI : Finite Qf := inferInstance
  letI : Finite Qgf := Finite.of_surjective reps hreps
  exact AddSubgroup.finiteIndex_of_finite_quotient

/-! ## From finite Kummer images to finite isogeny cokernels -/

/-- A finite homomorphic classifier has finite-index kernel; if an actual
isogeny has exactly that kernel as its image, its cokernel is finite. -/
theorem finiteIndex_range_of_finite_classifier
    {G H A : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup A]
    (α : G →+ A) (ψ : H →+ G) [Finite α.range]
    (hexact : ∀ P : G, α P = 0 ↔ ∃ Q : H, ψ Q = P) :
    ψ.range.FiniteIndex := by
  have hrange : ψ.range = α.ker := by
    ext P
    change (∃ Q, ψ Q = P) ↔ α P = 0
    exact (hexact P).symm
  rw [hrange]
  infer_instance

/-- A pointwise finite candidate list makes the genuine homomorphism range
finite.  This is the direct consumer for Gaussian PID/valuation support
certificates. -/
theorem finite_range_of_mem_finset
    {G A : Type*} [AddCommGroup G] [AddCommGroup A]
    (α : G →+ A) (s : Finset A) (hmem : ∀ P, α P ∈ s) :
    Finite α.range := by
  let embed : α.range → s :=
    fun y ↦ ⟨y.1, by
      rw [← y.2.choose_spec]
      exact hmem y.2.choose⟩
  apply Finite.of_injective embed
  intro x y hxy
  apply Subtype.ext
  simpa only [embed] using (congrArg Subtype.val hxy)

/-! ## The conditional Mordell--Weil endpoint -/

/-- Two finite genuine Kummer images, exactness at both isogenies, and the
actual isogeny composition law imply finite index of doubling. -/
theorem finiteIndex_two_of_finite_classifiers
    {G H A B : Type*}
    [AddCommGroup G] [AddCommGroup H] [AddCommGroup A] [AddCommGroup B]
    (φ : G →+ H) (φhat : H →+ G) (α : G →+ A) (αdual : H →+ B)
    [Finite α.range] [Finite αdual.range]
    (hexact : ∀ P : G, α P = 0 ↔ ∃ Q : H, φhat Q = P)
    (hexactDual : ∀ Q : H, αdual Q = 0 ↔ ∃ P : G, φ P = Q)
    (hcomp : φhat.comp φ = nsmulAddMonoidHom 2) :
    (nsmulAddMonoidHom (α := G) 2).range.FiniteIndex := by
  haveI : φhat.range.FiniteIndex :=
    finiteIndex_range_of_finite_classifier α φhat hexact
  haveI : φ.range.FiniteIndex :=
    finiteIndex_range_of_finite_classifier αdual φ hexactDual
  rw [← hcomp]
  exact finiteIndex_range_comp φ φhat

/-- Specialized assembly for the genuine Gaussian two-isogeny descent maps.
The two homomorphism arguments certify only that the already-defined rational
isogeny formulas preserve addition; the arithmetic hypotheses are exactly
finiteness of the two genuine squareclass images. -/
theorem finiteIndex_two_of_gaussian_descent
    (A B : GaussianRat) (hB : B ≠ 0) (hC : A ^ 2 - 4 * B ≠ 0)
    (φhom :
      (curve A B).toAffine.Point →+
        (dualCurve A B).toAffine.Point)
    (φhatHom :
      (dualCurve A B).toAffine.Point →+
        (curve A B).toAffine.Point)
    (hφ : ∀ P, φhom P = phi A B hB hC P)
    (hφhat : ∀ Q, φhatHom Q = phiHat A B hB hC Q)
    [Finite (alphaHom A B hB hC).range]
    [Finite (alphaDualHom A B hB hC).range] :
    (nsmulAddMonoidHom
      (α := (curve A B).toAffine.Point) 2).range.FiniteIndex := by
  apply finiteIndex_two_of_finite_classifiers
    φhom φhatHom (alphaHom A B hB hC) (alphaDualHom A B hB hC)
  · intro P
    rw [alphaHom_apply]
    change alpha A B hB hC P = 1 ↔ _
    rw [alpha_eq_one_iff_phiHat_image]
    constructor
    · rintro ⟨Q, rfl⟩
      exact ⟨Q, hφhat Q⟩
    · rintro ⟨Q, hQ⟩
      exact ⟨Q, (hφhat Q).symm.trans hQ⟩
  · intro Q
    rw [alphaDualHom_apply]
    change alphaDual A B hB hC Q = 1 ↔ _
    rw [alphaDual_eq_one_iff_phi_image]
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P, hφ P⟩
    · rintro ⟨P, hP⟩
      exact ⟨P, (hφ P).symm.trans hP⟩
  · ext P
    simp only [AddMonoidHom.comp_apply, hφ, hφhat, phiHat_phi,
      nsmulAddMonoidHom_apply]

/-- Finite explicit candidate lists for the two genuine Gaussian descent maps
are sufficient for finite index of doubling. -/
theorem finiteIndex_two_of_gaussian_candidate_sets
    (A B : GaussianRat) (hB : B ≠ 0) (hC : A ^ 2 - 4 * B ≠ 0)
    (φhom :
      (curve A B).toAffine.Point →+
        (dualCurve A B).toAffine.Point)
    (φhatHom :
      (dualCurve A B).toAffine.Point →+
        (curve A B).toAffine.Point)
    (hφ : ∀ P, φhom P = phi A B hB hC P)
    (hφhat : ∀ Q, φhatHom Q = phiHat A B hB hC Q)
    (sourceCandidates dualCandidates : Finset (Additive SquareClass))
    (hsource :
      ∀ P, alphaHom A B hB hC P ∈ sourceCandidates)
    (hdual :
      ∀ Q, alphaDualHom A B hB hC Q ∈ dualCandidates) :
    (nsmulAddMonoidHom
      (α := (curve A B).toAffine.Point) 2).range.FiniteIndex := by
  haveI : Finite (alphaHom A B hB hC).range :=
    finite_range_of_mem_finset _ sourceCandidates hsource
  haveI : Finite (alphaDualHom A B hB hC).range :=
    finite_range_of_mem_finset _ dualCandidates hdual
  exact finiteIndex_two_of_gaussian_descent
    A B hB hC φhom φhatHom hφ hφhat

/-! ## The conditional Mordell--Weil endpoint -/

/-- If two additive degree-two isogenies have finite cokernel and compose to
doubling, then doubling has finite-index image. -/
theorem finiteIndex_two_of_isogeny_pair {G H : Type*}
    [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (φhat : H →+ G)
    [φ.range.FiniteIndex] [φhat.range.FiniteIndex]
    (hcomp : φhat.comp φ = nsmulAddMonoidHom 2) :
    (nsmulAddMonoidHom (α := G) 2).range.FiniteIndex := by
  rw [← hcomp]
  exact finiteIndex_range_comp φ φhat

/-- Once the two specialized isogeny cokernels are known to be finite,
Mathlib's height descent gives finite generation of the source curve. -/
theorem fg_of_isogeny_pair
    {F : Type*} [Field F] [NumberField F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (H : Type*) [AddCommGroup H]
    (φ : W.toAffine.Point →+ H) (φhat : H →+ W.toAffine.Point)
    [φ.range.FiniteIndex] [φhat.range.FiniteIndex]
    (hcomp : φhat.comp φ = nsmulAddMonoidHom 2) :
    AddGroup.FG W.toAffine.Point := by
  haveI : (nsmulAddMonoidHom
      (α := W.toAffine.Point) 2).range.FiniteIndex :=
    finiteIndex_two_of_isogeny_pair φ φhat hcomp
  exact GaussianHeight.Point.fg_of_finiteIndex_two W (by infer_instance)

/-- The specialized conditional Mordell--Weil theorem over `ℚ(i)`, consuming
the exact finite-index conclusion assembled from the two genuine descent
maps. -/
theorem fg_of_gaussian_descent
    (A B : GaussianRat) (hB : B ≠ 0) (hC : A ^ 2 - 4 * B ≠ 0)
    (φhom :
      (curve A B).toAffine.Point →+
        (dualCurve A B).toAffine.Point)
    (φhatHom :
      (dualCurve A B).toAffine.Point →+
        (curve A B).toAffine.Point)
    (hφ : ∀ P, φhom P = phi A B hB hC P)
    (hφhat : ∀ Q, φhatHom Q = phiHat A B hB hC Q)
    [Finite (alphaHom A B hB hC).range]
    [Finite (alphaDualHom A B hB hC).range] :
    AddGroup.FG (curve A B).toAffine.Point := by
  haveI : (curve A B).IsElliptic :=
    { isUnit := isUnit_iff_ne_zero.mpr
        (curve_discriminant_ne_zero hB hC) }
  exact GaussianHeight.Point.fg_of_finiteIndex_two (curve A B)
    (finiteIndex_two_of_gaussian_descent
      A B hB hC φhom φhatHom hφ hφhat)

/-! ## The two named Gaussian models -/

/-- Conditional finite generation of `E₀(ℚ(i))` from its two finite genuine
descent images and additivity of the explicit isogeny formulas. -/
theorem gaussianE0_fg_of_descent
    (φhom : gaussianE0.toAffine.Point →+ gaussianE0Dual.toAffine.Point)
    (φhatHom : gaussianE0Dual.toAffine.Point →+ gaussianE0.toAffine.Point)
    (hφ : ∀ P, φhom P = gaussianE0Phi P)
    (hφhat : ∀ Q, φhatHom Q = gaussianE0PhiHat Q)
    [Finite (alphaHom E0A E0B E0B_ne_zero E0C_ne_zero).range]
    [Finite (alphaDualHom E0A E0B E0B_ne_zero E0C_ne_zero).range] :
    AddGroup.FG gaussianE0.toAffine.Point :=
  fg_of_gaussian_descent E0A E0B E0B_ne_zero E0C_ne_zero
    φhom φhatHom hφ hφhat

/-- Conditional finite generation of `E₁(ℚ(i))` from its two finite genuine
descent images and additivity of the explicit isogeny formulas. -/
theorem gaussianE1_fg_of_descent
    (φhom : gaussianE1.toAffine.Point →+ gaussianE1Dual.toAffine.Point)
    (φhatHom : gaussianE1Dual.toAffine.Point →+ gaussianE1.toAffine.Point)
    (hφ : ∀ P, φhom P = gaussianE1Phi P)
    (hφhat : ∀ Q, φhatHom Q = gaussianE1PhiHat Q)
    [Finite (alphaHom E1A E1B E1B_ne_zero E1C_ne_zero).range]
    [Finite (alphaDualHom E1A E1B E1B_ne_zero E1C_ne_zero).range] :
    AddGroup.FG gaussianE1.toAffine.Point :=
  fg_of_gaussian_descent E1A E1B E1B_ne_zero E1C_ne_zero
    φhom φhatHom hφ hφhat

/-! ## Honest structure-theorem endpoints -/

/-- The exact general structural output available from finite generation:
a free lattice of finite rank times a finite direct sum of prime-power cyclic
groups.  Determining the rank and torsion invariants is a separate arithmetic
certificate. -/
theorem structure_of_fg {G : Type*} [AddCommGroup G]
    (hfg : AddGroup.FG G) :
    ∃ (n : ℕ) (ι : Type) (_ : Fintype ι) (p : ι → ℕ)
      (_ : ∀ i, Nat.Prime <| p i) (e : ι → ℕ),
      Nonempty <| G ≃+ (Fin n →₀ ℤ) × ⨁ i : ι, ZMod (p i ^ e i) :=
  @AddCommGroup.equiv_free_prod_directSum_zmod G _ hfg

/-- An explicit rank-zero, two-torsion structure certificate classifies every
group element as zero or the distinguished nonzero two-torsion element. -/
theorem eq_zero_or_torsion_of_equiv_zmod_two {G : Type*} [AddCommGroup G]
    (e : G ≃+ ZMod 2) :
    let T := e.symm 1
    ∀ P : G, P = 0 ∨ P = T := by
  dsimp only
  intro P
  have hval : (e P).val < 2 := ZMod.val_lt _
  interval_cases h : (e P).val
  · left
    apply e.injective
    rw [map_zero]
    apply ZMod.val_injective
    simpa using h
  · right
    apply e.injective
    rw [e.apply_symm_apply]
    apply ZMod.val_injective
    simpa [ZMod.val_one 2] using h

/-- Version of the rank-zero classification with a previously named
two-torsion point, once the structure equivalence sends it to `1`. -/
theorem eq_zero_or_named_torsion_of_equiv_zmod_two
    {G : Type*} [AddCommGroup G]
    (e : G ≃+ ZMod 2) (T : G) (hT : e T = 1) (P : G) :
    P = 0 ∨ P = T := by
  rcases eq_zero_or_torsion_of_equiv_zmod_two e P with hP | hP
  · exact Or.inl hP
  · right
    rw [hP]
    apply e.injective
    simpa using hT.symm

/-- An explicit rank-one plus two-torsion structure certificate gives the
normal form used by the elliptic-Chabauty step.  The torsion coefficient is
literally either `0` or `1`. -/
theorem exists_rank_one_two_torsion_normal_form
    {G : Type*} [AddCommGroup G]
    (e : G ≃+ ℤ × ZMod 2) :
    let P₀ := e.symm (1, 0)
    let T := e.symm (0, 1)
    ∀ P : G, ∃ m : ℤ, ∃ ε : ℕ, ε < 2 ∧ P = m • P₀ + ε • T := by
  dsimp only
  intro P
  refine ⟨(e P).1, (e P).2.val, ZMod.val_lt _, ?_⟩
  apply e.injective
  rw [map_add, map_zsmul, map_nsmul, e.apply_symm_apply,
    e.apply_symm_apply]
  apply Prod.ext
  · simp
  · apply ZMod.val_injective
    simp

/-- Version of the rank-one normal form for already named points `P₀,T`,
once the structure equivalence identifies them with the standard generators.
-/
theorem exists_named_rank_one_two_torsion_normal_form
    {G : Type*} [AddCommGroup G]
    (e : G ≃+ ℤ × ZMod 2) (P₀ T : G)
    (hP₀ : e P₀ = (1, 0)) (hT : e T = (0, 1)) (P : G) :
    ∃ m : ℤ, ∃ ε : ℕ, ε < 2 ∧ P = m • P₀ + ε • T := by
  refine ⟨(e P).1, (e P).2.val, ZMod.val_lt _, ?_⟩
  apply e.injective
  rw [map_add, map_zsmul, map_nsmul, hP₀, hT]
  apply Prod.ext
  · simp
  · apply ZMod.val_injective
    simp

/-!
The remaining arithmetic inputs are intentionally visible at this boundary:

* additive-homomorphism certificates for the explicit `phi` and `phiHat`
  formulas;
* finite candidate-list membership for `alphaHom` and `alphaDualHom`;
* identification of the structure-theorem invariants as `ZMod 2` for `E₁`
  and `ℤ × ZMod 2` for `E₀`, including identification of the chosen generator
  and two-torsion point.

No one of these conclusions is encoded as a hidden field of a certificate
structure in this file.
-/

end GaussianGlobal

end

end Cuboid2
