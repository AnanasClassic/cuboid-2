import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.IndexNSmul

/-!
# Exact arithmetic assembly for the Gaussian Mordell--Weil groups

This file records the exact (rather than merely finite-index) group theory
behind a two-isogeny descent.  The correction factor in the index formula is
the image of the kernel of the dual isogeny in the dual Kummer quotient.
Keeping this factor explicit prevents the usual spurious factor of two.
-/

namespace Cuboid2

noncomputable section

namespace GaussianArithmetic

open scoped DirectSum

/-! ## The exact two-isogeny index formula -/

/-- The image of the kernel of the dual isogeny in the genuine dual Kummer
image.  This is the correction term in the exact doubling-index formula. -/
abbrev dualKernelKummerImage
    {G H B : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup B]
    (φhat : H →+ G) (αdual : H →+ B) : Type _ :=
  (αdual.rangeRestrict.domRestrict φhat.ker).range

/-- Exact cardinal formula for a pair of degree-two isogenies.

If the two Kummer kernels are the two isogeny images and the composite is
doubling, then

`|αdual(ker φhat)| · [G : 2G] = |im α| · |im αdual|`.

The first factor is essential: for the Gaussian models it has cardinality
two, so the naive product of the two Kummer-image cardinalities overcounts
the doubling index by a factor of two.
-/
theorem dualKernel_card_mul_doubling_index
    {G H A B : Type*}
    [AddCommGroup G] [AddCommGroup H] [AddCommGroup A] [AddCommGroup B]
    (φ : G →+ H) (φhat : H →+ G) (α : G →+ A) (αdual : H →+ B)
    (hker : α.ker = φhat.range)
    (hkerDual : αdual.ker = φ.range)
    (hcomp : φhat.comp φ = nsmulAddMonoidHom 2)
    [Finite α.range] [Finite αdual.range] :
    Nat.card (dualKernelKummerImage φhat αdual) *
        (nsmulAddMonoidHom (α := G) 2).range.index =
      Nat.card α.range * Nat.card αdual.range := by
  classical
  let L : AddSubgroup G := (φhat.comp φ).range
  let K : AddSubgroup G := φhat.range
  let S : AddSubgroup H := φ.range ⊔ φhat.ker
  let β : H →+ αdual.range := αdual.rangeRestrict
  have hLK : L ≤ K := by
    rintro x ⟨g, rfl⟩
    exact ⟨φ g, rfl⟩
  have hLmap : L = φ.range.map φhat := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨φ g, ⟨g, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
  have hKmap : K = (⊤ : AddSubgroup H).map φhat := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, trivial, rfl⟩
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩
  have hrel : L.relIndex K = S.index := by
    rw [hLmap, hKmap, AddSubgroup.relIndex_map_map]
    change S.relIndex (⊤ ⊔ φhat.ker) = S.index
    simp only [top_sup_eq, AddSubgroup.relIndex_top_right]
  have hβsurj : Function.Surjective β := αdual.rangeRestrict_surjective
  have hβker : β.ker = αdual.ker := by
    ext x
    simp [β]
  have hker_le_S : β.ker ≤ S := by
    rw [hβker, hkerDual]
    exact le_sup_left
  have hindexS : (S.map β).index = S.index :=
    AddSubgroup.index_map_eq S hβsurj hker_le_S
  have hmapS :
      S.map β = φhat.ker.map β := by
    change (φ.range ⊔ φhat.ker).map β = φhat.ker.map β
    rw [AddSubgroup.map_sup, ← hkerDual]
    have hz : αdual.ker.map β = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      apply Subtype.ext
      simpa [β] using hx
    rw [hz, bot_sup_eq]
  have hcardMap :
      Nat.card (S.map β) =
        Nat.card (dualKernelKummerImage φhat αdual) := by
    rw [hmapS]
    change Nat.card (φhat.ker.map β) =
      Nat.card (β.domRestrict φhat.ker).range
    rw [AddMonoidHom.domRestrict_range]
  have hdualCard :
      Nat.card (dualKernelKummerImage φhat αdual) * S.index =
        Nat.card αdual.range := by
    calc
      Nat.card (dualKernelKummerImage φhat αdual) * S.index =
          Nat.card (S.map β) * (S.map β).index := by
            rw [hcardMap, hindexS]
      _ = Nat.card αdual.range := AddSubgroup.card_mul_index (S.map β)
  have hsourceIndex : K.index = Nat.card α.range := by
    change φhat.range.index = Nat.card α.range
    rw [← hker, AddSubgroup.index_ker]
  rw [← hcomp]
  change Nat.card (dualKernelKummerImage φhat αdual) * L.index =
    Nat.card α.range * Nat.card αdual.range
  rw [← AddSubgroup.relIndex_mul_index hLK, hrel, hsourceIndex,
    ← hdualCard]
  ac_rfl

/-- The numerical specialization used for `E₀`: Kummer image cardinalities
`4` and `2`, with the nontrivial dual-kernel correction of cardinality `2`,
give doubling index `4`. -/
theorem doubling_index_eq_four_of_kummer_cards
    {G H A B : Type*}
    [AddCommGroup G] [AddCommGroup H] [AddCommGroup A] [AddCommGroup B]
    (φ : G →+ H) (φhat : H →+ G) (α : G →+ A) (αdual : H →+ B)
    (hker : α.ker = φhat.range)
    (hkerDual : αdual.ker = φ.range)
    (hcomp : φhat.comp φ = nsmulAddMonoidHom 2)
    [Finite α.range] [Finite αdual.range]
    (hsource : Nat.card α.range = 4)
    (hdual : Nat.card αdual.range = 2)
    (hcorrection : Nat.card (dualKernelKummerImage φhat αdual) = 2) :
    (nsmulAddMonoidHom (α := G) 2).range.index = 4 := by
  have h := dualKernel_card_mul_doubling_index
    φ φhat α αdual hker hkerDual hcomp
  rw [hsource, hdual, hcorrection] at h
  omega

/-- The numerical specialization used for `E₁`: both Kummer images and the
dual-kernel correction have cardinality `2`, so the doubling index is `2`. -/
theorem doubling_index_eq_two_of_kummer_cards
    {G H A B : Type*}
    [AddCommGroup G] [AddCommGroup H] [AddCommGroup A] [AddCommGroup B]
    (φ : G →+ H) (φhat : H →+ G) (α : G →+ A) (αdual : H →+ B)
    (hker : α.ker = φhat.range)
    (hkerDual : αdual.ker = φ.range)
    (hcomp : φhat.comp φ = nsmulAddMonoidHom 2)
    [Finite α.range] [Finite αdual.range]
    (hsource : Nat.card α.range = 2)
    (hdual : Nat.card αdual.range = 2)
    (hcorrection : Nat.card (dualKernelKummerImage φhat αdual) = 2) :
    (nsmulAddMonoidHom (α := G) 2).range.index = 2 := by
  have h := dualKernel_card_mul_doubling_index
    φ φhat α αdual hker hkerDual hcomp
  rw [hsource, hdual, hcorrection] at h
  omega

/-! ## Rank extraction from the exact doubling index -/

/-- An additive equivalence identifies the kernels of multiplication by the
same natural number. -/
def nsmulKerEquiv
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (n : ℕ) :
    (nsmulAddMonoidHom (α := G) n).ker ≃+
      (nsmulAddMonoidHom (α := H) n).ker where
  toFun x :=
    ⟨e x.1, by
      change n • e x.1 = 0
      simpa using congrArg e x.2⟩
  invFun y :=
    ⟨e.symm y.1, by
      change n • e.symm y.1 = 0
      simpa using congrArg e.symm y.2⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y.1
  map_add' x y := by
    apply Subtype.ext
    exact e.map_add x.1 y.1

/-- Multiplication-by-`n` on a product has kernel the product of the two
kernels. -/
def nsmulProdKerEquiv
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] (n : ℕ) :
    (nsmulAddMonoidHom (α := G × H) n).ker ≃+
      (nsmulAddMonoidHom (α := G) n).ker ×
        (nsmulAddMonoidHom (α := H) n).ker where
  toFun x :=
    (⟨x.1.1, congrArg Prod.fst x.2⟩,
      ⟨x.1.2, congrArg Prod.snd x.2⟩)
  invFun x :=
    ⟨(x.1.1, x.2.1), by
      apply Prod.ext
      · exact x.1.2
      · exact x.2.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := rfl
  map_add' x y := rfl

/-- The exact doubling-index formula on a free lattice times a finite group:
the index is `2^rank` times the cardinality of the two-torsion kernel. -/
theorem doubling_index_free_prod_finite
    (n : ℕ) (D : Type*) [AddCommGroup D] [Finite D] :
    (nsmulAddMonoidHom (α := (Fin n →₀ ℤ) × D) 2).range.index =
      2 ^ n *
        Nat.card
          (nsmulAddMonoidHom (α := (Fin n →₀ ℤ) × D) 2).ker := by
  classical
  let F := Fin n →₀ ℤ
  let twoF : F →+ F := nsmulAddMonoidHom 2
  let twoD : D →+ D := nsmulAddMonoidHom 2
  have hrange :
      (nsmulAddMonoidHom (α := F × D) 2).range =
        twoF.range.prod twoD.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y.1, rfl⟩, ⟨y.2, rfl⟩⟩
    · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
      refine ⟨(u, v), ?_⟩
      apply Prod.ext
      · exact hu
      · exact hv
  have hfreeIndex : twoF.range.index = 2 ^ n := by
    simpa [F, twoF] using AddSubgroup.index_range_nsmul F 2
  haveI : twoD.ker.FiniteIndex := by infer_instance
  have hfiniteIndex : twoD.range.index = Nat.card twoD.ker :=
    AddSubgroup.index_range
  have hfreeKer : Nat.card twoF.ker = 1 := by
    have hinj : Function.Injective twoF := by
      dsimp only [twoF, F]
      exact AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree
        (by norm_num)
    have hbot : twoF.ker = ⊥ := twoF.ker_eq_bot hinj
    rw [hbot]
    simp
  have hkerCard :
      Nat.card
          (nsmulAddMonoidHom (α := F × D) 2).ker =
        Nat.card twoD.ker := by
    calc
      _ = Nat.card (twoF.ker × twoD.ker) :=
        Nat.card_congr (nsmulProdKerEquiv (G := F) (H := D) 2).toEquiv
      _ = Nat.card twoF.ker * Nat.card twoD.ker := by
        rw [Nat.card_prod]
      _ = Nat.card twoD.ker := by rw [hfreeKer, one_mul]
  rw [hrange, AddSubgroup.index_prod, hfreeIndex, hfiniteIndex, hkerCard]

/-- Transported form of `doubling_index_free_prod_finite`.  This is the
rank equation consumed after the finite-generation structure theorem. -/
theorem doubling_index_eq_pow_mul_kernel_card_of_equiv
    {G D : Type*} [AddCommGroup G] [AddCommGroup D] [Finite D]
    (n : ℕ) (e : G ≃+ (Fin n →₀ ℤ) × D) :
    (nsmulAddMonoidHom (α := G) 2).range.index =
      2 ^ n * Nat.card (nsmulAddMonoidHom (α := G) 2).ker := by
  have hindex :
      (nsmulAddMonoidHom (α := G) 2).range.index =
        (nsmulAddMonoidHom
          (α := (Fin n →₀ ℤ) × D) 2).range.index := by
    simpa [AddEquiv.map_range_nsmulAddMonoidHom] using
      (AddSubgroup.index_map_equiv
        (nsmulAddMonoidHom (α := G) 2).range e).symm
  have hker :
      Nat.card
          (nsmulAddMonoidHom
            (α := (Fin n →₀ ℤ) × D) 2).ker =
        Nat.card (nsmulAddMonoidHom (α := G) 2).ker :=
    Nat.card_congr (nsmulKerEquiv e 2).symm.toEquiv
  rw [hindex, doubling_index_free_prod_finite, hker]

/-- If zero and a named nonzero two-torsion element exhaust the kernel of
doubling, that kernel has cardinality exactly two. -/
theorem doubling_ker_card_eq_two_of_classified
    {G : Type*} [AddCommGroup G] (T : G)
    (hT : 2 • T = 0) (hTne : T ≠ 0)
    (hclassified : ∀ P : G, 2 • P = 0 → P = 0 ∨ P = T) :
    Nat.card (nsmulAddMonoidHom (α := G) 2).ker = 2 := by
  apply Nat.card_eq_two_iff.mpr
  refine ⟨⟨0, by simp⟩, ⟨T, hT⟩, ?_, ?_⟩
  · intro h
    apply hTne
    exact congrArg Subtype.val h.symm
  · ext P
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_univ, iff_true]
    rcases hclassified P.1 P.2 with hP | hP
    · exact Or.inl (Subtype.ext hP)
    · exact Or.inr (Subtype.ext hP)

/-- Finite generation, doubling index two, and a two-element doubling kernel
force free rank zero.  The finite factor is kept explicit because excluding
odd torsion is a logically separate arithmetic step. -/
theorem rank_zero_structure_of_fg
    {G : Type*} [AddCommGroup G]
    (hfg : AddGroup.FG G)
    (hindex : (nsmulAddMonoidHom (α := G) 2).range.index = 2)
    (hker : Nat.card (nsmulAddMonoidHom (α := G) 2).ker = 2) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ)
      (_ : ∀ i, Nat.Prime <| p i) (exponent : ι → ℕ),
      Nonempty <| G ≃+ (⨁ i : ι, ZMod (p i ^ exponent i)) := by
  letI : AddGroup.FG G := hfg
  obtain ⟨n, ι, fι, p, hp, exponent, ⟨e⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod G
  let D := ⨁ i : ι, ZMod (p i ^ exponent i)
  letI : Finite D := by
    dsimp only [D]
    letI : ∀ i : ι, NeZero (p i ^ exponent i) :=
      fun i ↦ ⟨pow_ne_zero _ (hp i).ne_zero⟩
    have : ∀ i : ι, Finite (ZMod (p i ^ exponent i)) :=
      fun _ ↦ inferInstance
    exact Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have heq :=
    doubling_index_eq_pow_mul_kernel_card_of_equiv
      (G := G) (D := D) n e
  rw [hindex, hker] at heq
  have hpow : 2 ^ n = 2 ^ 0 := by
    norm_num at heq ⊢
    omega
  have hn : n = 0 := Nat.pow_right_injective (by norm_num) hpow
  subst n
  refine ⟨ι, fι, p, hp, exponent, ?_⟩
  exact ⟨e.trans AddEquiv.uniqueProd⟩

/-- Finite generation, doubling index four, and a two-element doubling kernel
force free rank one.  The conclusion is the exact free-plus-finite normal
form before the independent odd-torsion elimination. -/
theorem rank_one_structure_of_fg
    {G : Type*} [AddCommGroup G]
    (hfg : AddGroup.FG G)
    (hindex : (nsmulAddMonoidHom (α := G) 2).range.index = 4)
    (hker : Nat.card (nsmulAddMonoidHom (α := G) 2).ker = 2) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ)
      (_ : ∀ i, Nat.Prime <| p i) (exponent : ι → ℕ),
      Nonempty <| G ≃+ (ℤ × (⨁ i : ι, ZMod (p i ^ exponent i))) := by
  letI : AddGroup.FG G := hfg
  obtain ⟨n, ι, fι, p, hp, exponent, ⟨e⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod G
  let D := ⨁ i : ι, ZMod (p i ^ exponent i)
  letI : Finite D := by
    dsimp only [D]
    letI : ∀ i : ι, NeZero (p i ^ exponent i) :=
      fun i ↦ ⟨pow_ne_zero _ (hp i).ne_zero⟩
    have : ∀ i : ι, Finite (ZMod (p i ^ exponent i)) :=
      fun _ ↦ inferInstance
    exact Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have heq :=
    doubling_index_eq_pow_mul_kernel_card_of_equiv
      (G := G) (D := D) n e
  rw [hindex, hker] at heq
  have hpow : 2 ^ n = 2 ^ 1 := by
    norm_num at heq ⊢
    omega
  have hn : n = 1 := Nat.pow_right_injective (by norm_num) hpow
  subst n
  refine ⟨ι, fι, p, hp, exponent, ?_⟩
  exact
    ⟨e.trans
      (AddEquiv.finsuppUnique.prodCongr
        (AddEquiv.refl (⨁ i : ι, ZMod (p i ^ exponent i))))⟩

end GaussianArithmetic

end

end Cuboid2
