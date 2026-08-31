import Cuboid2.QuadraticReduction.GaussianArithmetic
import Cuboid2.QuadraticReduction.GaussianGlobal
import Cuboid2.QuadraticReduction.GaussianTwoTorsion
import Cuboid2.QuadraticReduction.GaussianWeakMW
import Mathlib.GroupTheory.Torsion

/-!
# Rank extraction for the Gaussian Mordell--Weil groups

This file packages the exact group arithmetic already proved for a finitely
generated abelian group with a two-element doubling kernel.  Its conclusions
retain the whole finite summand: excluding odd torsion is a separate
good-reduction argument and is not assumed here.
-/

namespace Cuboid2

noncomputable section

namespace GaussianRankArithmetic

open scoped DirectSum

open GaussianArithmetic GaussianDescent

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

/-! ## Generic exact-index consumers -/

/-- A named exhaustive two-torsion classification, finite generation, and
doubling index two force free rank zero.  No claim is made about the odd part
of the finite summand. -/
theorem rankZeroStructure_of_exactDoubling
    {G : Type*} [AddCommGroup G]
    (T : G) (hT : 2 • T = 0) (hTne : T ≠ 0)
    (hclassified : ∀ P : G, 2 • P = 0 → P = 0 ∨ P = T)
    (hfg : AddGroup.FG G)
    (hindex : (nsmulAddMonoidHom (α := G) 2).range.index = 2) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ)
      (_ : ∀ i, Nat.Prime <| p i) (exponent : ι → ℕ),
      Nonempty <| G ≃+ (⨁ i : ι, ZMod (p i ^ exponent i)) := by
  apply rank_zero_structure_of_fg hfg hindex
  exact doubling_ker_card_eq_two_of_classified T hT hTne hclassified

/-- A named exhaustive two-torsion classification, finite generation, and
doubling index four force free rank one.  The finite summand is deliberately
left intact until odd torsion is excluded independently. -/
theorem rankOneStructure_of_exactDoubling
    {G : Type*} [AddCommGroup G]
    (T : G) (hT : 2 • T = 0) (hTne : T ≠ 0)
    (hclassified : ∀ P : G, 2 • P = 0 → P = 0 ∨ P = T)
    (hfg : AddGroup.FG G)
    (hindex : (nsmulAddMonoidHom (α := G) 2).range.index = 4) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ)
      (_ : ∀ i, Nat.Prime <| p i) (exponent : ι → ℕ),
      Nonempty <| G ≃+
        (ℤ × (⨁ i : ι, ZMod (p i ^ exponent i))) := by
  apply rank_one_structure_of_fg hfg hindex
  exact doubling_ker_card_eq_two_of_classified T hT hTne hclassified

/-! ## Numerical free rank -/

private theorem addGroup_rank_int : AddGroup.rank ℤ = 1 := by
  apply le_antisymm
  · have hle :
        AddGroup.rank ℤ ≤ ({1} : Finset ℤ).card := by
      apply AddGroup.rank_le
      rw [eq_top_iff]
      intro z
      have h1 :
          (1 : ℤ) ∈ AddSubgroup.closure ({1} : Set ℤ) :=
        AddSubgroup.subset_closure (by simp)
      have hz :
          z • (1 : ℤ) ∈ AddSubgroup.closure ({1} : Set ℤ) :=
        (AddSubgroup.closure ({1} : Set ℤ)).zsmul_mem h1 z
      simpa using hz
    simpa using hle
  · have hpos := AddGroup.rank_pos ℤ
    omega

private theorem torsion_int_prod_finite
    (D : Type*) [AddCommGroup D] [Finite D] :
    AddCommGroup.torsion (ℤ × D) =
      (AddMonoidHom.fst ℤ D).ker := by
  ext x
  rw [AddCommGroup.mem_torsion, IsOfFinAddOrder.prod_iff]
  change
    (IsOfFinAddOrder x.1 ∧ IsOfFinAddOrder x.2) ↔ x.1 = 0
  constructor
  · rintro ⟨hx, -⟩
    by_contra hne
    exact not_isOfFinAddOrder_of_isAddTorsionFree hne hx
  · intro hx
    constructor
    · simpa [hx] using
        (IsOfFinAddOrder.zero : IsOfFinAddOrder (0 : ℤ))
    · exact isAddTorsion_of_finite _

/-- Modding `ℤ × D` by its torsion subgroup recovers `ℤ` whenever `D` is
finite. -/
private def quotientTorsionIntProdEquiv
    (D : Type*) [AddCommGroup D] [Finite D] :
    (ℤ × D) ⧸ AddCommGroup.torsion (ℤ × D) ≃+ ℤ := by
  rw [torsion_int_prod_finite D]
  exact
    (QuotientAddGroup.quotientKerEquivRange
      (AddMonoidHom.fst ℤ D)).trans
      { toFun := fun x => x.1
        invFun := fun z => ⟨z, ⟨(z, 0), rfl⟩⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }

/-- A product of `ℤ` with a finite abelian group has free rank exactly one. -/
theorem freeRank_int_prod_finite
    (D : Type*) [AddCommGroup D] [Finite D] :
    AddCommGroup.freeRank (ℤ × D) = 1 := by
  rw [AddCommGroup.freeRank_def]
  calc
    AddGroup.rank
          ((ℤ × D) ⧸ AddCommGroup.torsion (ℤ × D)) =
        AddGroup.rank ℤ :=
      AddGroup.rank_congr (quotientTorsionIntProdEquiv D)
    _ = 1 := addGroup_rank_int

/-- The exact-index hypotheses of `rankZeroStructure_of_exactDoubling`
numerically force `AddCommGroup.freeRank G = 0`. -/
theorem freeRank_eq_zero_of_exactDoubling
    {G : Type*} [AddCommGroup G]
    (T : G) (hT : 2 • T = 0) (hTne : T ≠ 0)
    (hclassified : ∀ P : G, 2 • P = 0 → P = 0 ∨ P = T)
    (hfg : AddGroup.FG G)
    (hindex : (nsmulAddMonoidHom (α := G) 2).range.index = 2) :
    @AddCommGroup.freeRank G _ hfg = 0 := by
  letI : AddGroup.FG G := hfg
  change AddCommGroup.freeRank G = 0
  obtain ⟨ι, _, p, hp, exponent, ⟨e⟩⟩ :=
    rankZeroStructure_of_exactDoubling
      T hT hTne hclassified hfg hindex
  let D := ⨁ i : ι, ZMod (p i ^ exponent i)
  letI : Finite D := by
    dsimp only [D]
    letI : ∀ i : ι, NeZero (p i ^ exponent i) :=
      fun i ↦ ⟨pow_ne_zero _ (hp i).ne_zero⟩
    have : ∀ i : ι, Finite (ZMod (p i ^ exponent i)) :=
      fun _ ↦ inferInstance
    exact Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  letI : Finite G := Finite.of_injective e e.injective
  exact AddCommGroup.freeRank_eq_zero_of_finite

/-- The exact-index hypotheses of `rankOneStructure_of_exactDoubling`
numerically force `AddCommGroup.freeRank G = 1`, while retaining all odd
torsion in the independent finite summand. -/
theorem freeRank_eq_one_of_exactDoubling
    {G : Type*} [AddCommGroup G]
    (T : G) (hT : 2 • T = 0) (hTne : T ≠ 0)
    (hclassified : ∀ P : G, 2 • P = 0 → P = 0 ∨ P = T)
    (hfg : AddGroup.FG G)
    (hindex : (nsmulAddMonoidHom (α := G) 2).range.index = 4) :
    @AddCommGroup.freeRank G _ hfg = 1 := by
  letI : AddGroup.FG G := hfg
  change AddCommGroup.freeRank G = 1
  obtain ⟨ι, _, p, hp, exponent, ⟨e⟩⟩ :=
    rankOneStructure_of_exactDoubling
      T hT hTne hclassified hfg hindex
  let D := ⨁ i : ι, ZMod (p i ^ exponent i)
  letI : Finite D := by
    dsimp only [D]
    letI : ∀ i : ι, NeZero (p i ^ exponent i) :=
      fun i ↦ ⟨pow_ne_zero _ (hp i).ne_zero⟩
    have : ∀ i : ι, Finite (ZMod (p i ^ exponent i)) :=
      fun _ ↦ inferInstance
    exact Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  calc
    AddCommGroup.freeRank G =
        AddCommGroup.freeRank (ℤ × D) :=
      AddCommGroup.freeRank_congr e
    _ = 1 := freeRank_int_prod_finite D

/-! ## The actual Gaussian two-torsion points -/

/-- The displayed point `(0,0)` on `E₀` is nonzero. -/
theorem gaussianE0T_ne_zero : gaussianE0T ≠ 0 := by
  change
    WeierstrassCurve.Affine.Point.some 0 0 _ ≠
      WeierstrassCurve.Affine.Point.zero
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-- The displayed point `(0,0)` on `E₁` is nonzero. -/
theorem gaussianE1T_ne_zero : gaussianE1T ≠ 0 := by
  change
    WeierstrassCurve.Affine.Point.some 0 0 _ ≠
      WeierstrassCurve.Affine.Point.zero
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-- The displayed point `(0,0)` on `E₀` is killed by doubling. -/
theorem two_nsmul_gaussianE0T : 2 • gaussianE0T = 0 := by
  change gaussianE0T + gaussianE0T = 0
  have htY :
      (0 : GaussianRat) = gaussianE0.toAffine.negY 0 0 := by
    simp [gaussianE0]
  change
    WeierstrassCurve.Affine.Point.some 0 0 _ +
      WeierstrassCurve.Affine.Point.some 0 0 _ = 0
  exact WeierstrassCurve.Affine.Point.add_of_Y_eq rfl htY

/-- The displayed point `(0,0)` on `E₁` is killed by doubling. -/
theorem two_nsmul_gaussianE1T : 2 • gaussianE1T = 0 := by
  change gaussianE1T + gaussianE1T = 0
  have htY :
      (0 : GaussianRat) = gaussianE1.toAffine.negY 0 0 := by
    simp [gaussianE1]
  change
    WeierstrassCurve.Affine.Point.some 0 0 _ +
      WeierstrassCurve.Affine.Point.some 0 0 _ = 0
  exact WeierstrassCurve.Affine.Point.add_of_Y_eq rfl htY

/-! ## Actual exact-index endpoints -/

/-- For the actual `E₀(ℚ(i))` point group, finite generation and exact
doubling index four give the honest rank-one-plus-finite structure. -/
theorem gaussianE0_rankOneStructure_of_fg_and_index
    (hfg : AddGroup.FG gaussianE0.toAffine.Point)
    (hindex :
      (nsmulAddMonoidHom
        (α := gaussianE0.toAffine.Point) 2).range.index = 4) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ)
      (_ : ∀ i, Nat.Prime <| p i) (exponent : ι → ℕ),
      Nonempty <| gaussianE0.toAffine.Point ≃+
        (ℤ × (⨁ i : ι, ZMod (p i ^ exponent i))) :=
  rankOneStructure_of_exactDoubling
    gaussianE0T two_nsmul_gaussianE0T gaussianE0T_ne_zero
    GaussianTwoTorsion.gaussianE0_two_torsion_classified hfg hindex

/-- For the actual `E₁(ℚ(i))` point group, finite generation and exact
doubling index two give the honest finite (free-rank-zero) structure. -/
theorem gaussianE1_rankZeroStructure_of_fg_and_index
    (hfg : AddGroup.FG gaussianE1.toAffine.Point)
    (hindex :
      (nsmulAddMonoidHom
        (α := gaussianE1.toAffine.Point) 2).range.index = 2) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ)
      (_ : ∀ i, Nat.Prime <| p i) (exponent : ι → ℕ),
      Nonempty <| gaussianE1.toAffine.Point ≃+
        (⨁ i : ι, ZMod (p i ^ exponent i)) :=
  rankZeroStructure_of_exactDoubling
    gaussianE1T two_nsmul_gaussianE1T gaussianE1T_ne_zero
    GaussianTwoTorsion.gaussianE1_two_torsion_classified hfg hindex

/-- Numerical form of the actual `E₀` result: its free rank is one. -/
theorem gaussianE0_freeRank_eq_one_of_fg_and_index
    (hfg : AddGroup.FG gaussianE0.toAffine.Point)
    (hindex :
      (nsmulAddMonoidHom
        (α := gaussianE0.toAffine.Point) 2).range.index = 4) :
    @AddCommGroup.freeRank gaussianE0.toAffine.Point _ hfg = 1 :=
  freeRank_eq_one_of_exactDoubling
    gaussianE0T two_nsmul_gaussianE0T gaussianE0T_ne_zero
    GaussianTwoTorsion.gaussianE0_two_torsion_classified hfg hindex

/-- Numerical form of the actual `E₁` result: its free rank is zero. -/
theorem gaussianE1_freeRank_eq_zero_of_fg_and_index
    (hfg : AddGroup.FG gaussianE1.toAffine.Point)
    (hindex :
      (nsmulAddMonoidHom
        (α := gaussianE1.toAffine.Point) 2).range.index = 2) :
    @AddCommGroup.freeRank gaussianE1.toAffine.Point _ hfg = 0 :=
  freeRank_eq_zero_of_exactDoubling
    gaussianE1T two_nsmul_gaussianE1T gaussianE1T_ne_zero
    GaussianTwoTorsion.gaussianE1_two_torsion_classified hfg hindex

/-! ## Weak Mordell--Weil consumers -/

/-- The genuine weak Mordell--Weil theorem supplies finite generation for
`E₀`; together with its exact doubling index this yields the rank-one
structure. -/
theorem gaussianE0_rankOneStructure_of_weakMW
    (hdual :
      ∀ Q : (dualCurve E0A E0B).toAffine.Point,
        alphaDual E0A E0B E0B_ne_zero E0C_ne_zero Q = 1 ∨
          alphaDual E0A E0B E0B_ne_zero E0C_ne_zero Q =
            alphaDual E0A E0B E0B_ne_zero E0C_ne_zero
              (dualTorsion E0A E0B E0B_ne_zero E0C_ne_zero))
    [Finite (alphaHom E0A E0B E0B_ne_zero E0C_ne_zero).range]
    (hindex :
      (nsmulAddMonoidHom
        (α := gaussianE0.toAffine.Point) 2).range.index = 4) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ)
      (_ : ∀ i, Nat.Prime <| p i) (exponent : ι → ℕ),
      Nonempty <| gaussianE0.toAffine.Point ≃+
        (ℤ × (⨁ i : ι, ZMod (p i ^ exponent i))) := by
  apply gaussianE0_rankOneStructure_of_fg_and_index _ hindex
  exact
    GaussianWeakMW.fg_of_finite_alpha_and_dual_classification
      E0A E0B E0B_ne_zero E0C_ne_zero hdual

/-- The genuine weak Mordell--Weil theorem supplies finite generation for
`E₁`; together with its exact doubling index this yields the
free-rank-zero structure. -/
theorem gaussianE1_rankZeroStructure_of_weakMW
    (hdual :
      ∀ Q : (dualCurve E1A E1B).toAffine.Point,
        alphaDual E1A E1B E1B_ne_zero E1C_ne_zero Q = 1 ∨
          alphaDual E1A E1B E1B_ne_zero E1C_ne_zero Q =
            alphaDual E1A E1B E1B_ne_zero E1C_ne_zero
              (dualTorsion E1A E1B E1B_ne_zero E1C_ne_zero))
    [Finite (alphaHom E1A E1B E1B_ne_zero E1C_ne_zero).range]
    (hindex :
      (nsmulAddMonoidHom
        (α := gaussianE1.toAffine.Point) 2).range.index = 2) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ)
      (_ : ∀ i, Nat.Prime <| p i) (exponent : ι → ℕ),
      Nonempty <| gaussianE1.toAffine.Point ≃+
        (⨁ i : ι, ZMod (p i ^ exponent i)) := by
  apply gaussianE1_rankZeroStructure_of_fg_and_index _ hindex
  exact
    GaussianWeakMW.fg_of_finite_alpha_and_dual_classification
      E1A E1B E1B_ne_zero E1C_ne_zero hdual

/-- Pointwise containment of the genuine source Kummer map in a finite set,
the exact two-class dual classification, and doubling index four give the
actual `E₀` rank-one structure. -/
theorem gaussianE0_rankOneStructure_of_candidates
    (sourceCandidates : Finset (Additive SquareClass))
    (hsource :
      ∀ P : (curve E0A E0B).toAffine.Point,
        alphaHom E0A E0B E0B_ne_zero E0C_ne_zero P ∈
          sourceCandidates)
    (hdual :
      ∀ Q : (dualCurve E0A E0B).toAffine.Point,
        alphaDual E0A E0B E0B_ne_zero E0C_ne_zero Q = 1 ∨
          alphaDual E0A E0B E0B_ne_zero E0C_ne_zero Q =
            alphaDual E0A E0B E0B_ne_zero E0C_ne_zero
              (dualTorsion E0A E0B E0B_ne_zero E0C_ne_zero))
    (hindex :
      (nsmulAddMonoidHom
        (α := gaussianE0.toAffine.Point) 2).range.index = 4) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ)
      (_ : ∀ i, Nat.Prime <| p i) (exponent : ι → ℕ),
      Nonempty <| gaussianE0.toAffine.Point ≃+
        (ℤ × (⨁ i : ι, ZMod (p i ^ exponent i))) := by
  letI : Finite
      (alphaHom E0A E0B E0B_ne_zero E0C_ne_zero).range :=
    GaussianGlobal.finite_range_of_mem_finset
      _ sourceCandidates hsource
  exact gaussianE0_rankOneStructure_of_weakMW hdual hindex

/-- Pointwise containment of the genuine source Kummer map in a finite set,
the exact two-class dual classification, and doubling index two give the
actual `E₁` free-rank-zero structure. -/
theorem gaussianE1_rankZeroStructure_of_candidates
    (sourceCandidates : Finset (Additive SquareClass))
    (hsource :
      ∀ P : (curve E1A E1B).toAffine.Point,
        alphaHom E1A E1B E1B_ne_zero E1C_ne_zero P ∈
          sourceCandidates)
    (hdual :
      ∀ Q : (dualCurve E1A E1B).toAffine.Point,
        alphaDual E1A E1B E1B_ne_zero E1C_ne_zero Q = 1 ∨
          alphaDual E1A E1B E1B_ne_zero E1C_ne_zero Q =
            alphaDual E1A E1B E1B_ne_zero E1C_ne_zero
              (dualTorsion E1A E1B E1B_ne_zero E1C_ne_zero))
    (hindex :
      (nsmulAddMonoidHom
        (α := gaussianE1.toAffine.Point) 2).range.index = 2) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ)
      (_ : ∀ i, Nat.Prime <| p i) (exponent : ι → ℕ),
      Nonempty <| gaussianE1.toAffine.Point ≃+
        (⨁ i : ι, ZMod (p i ^ exponent i)) := by
  letI : Finite
      (alphaHom E1A E1B E1B_ne_zero E1C_ne_zero).range :=
    GaussianGlobal.finite_range_of_mem_finset
      _ sourceCandidates hsource
  exact gaussianE1_rankZeroStructure_of_weakMW hdual hindex

end GaussianRankArithmetic

end

end Cuboid2
