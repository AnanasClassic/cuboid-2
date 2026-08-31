import Cuboid2.QuadraticReduction.GaussianExactRanges
import Cuboid2.QuadraticReduction.GaussianWeakMW
import Cuboid2.QuadraticReduction.GaussianRankArithmetic

/-!
# Unconditional Mordell--Weil ranks for the two Gaussian curves

The exact Kummer ranges give weak Mordell--Weil finite generation.  The
two-class dual ranges identify the kernel of the source Kummer map with the
image of doubling, so the source range cardinalities compute the two exact
doubling indices.  The existing exhaustive two-torsion classification then
determines only the free ranks; odd torsion is deliberately left open here.
-/

namespace Cuboid2

noncomputable section

namespace GaussianMordellWeil

open GaussianDescent GaussianExactRanges GaussianWeakMW
  GaussianRankArithmetic

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

private theorem gaussianE0_dual_two_class
    (Q : (dualCurve E0A E0B).toAffine.Point) :
    alphaDual E0A E0B E0B_ne_zero E0C_ne_zero Q = 1 ∨
      alphaDual E0A E0B E0B_ne_zero E0C_ne_zero Q =
        alphaDual E0A E0B E0B_ne_zero E0C_ne_zero
          (dualTorsion E0A E0B E0B_ne_zero E0C_ne_zero) := by
  rcases gaussianE0_alphaDual_classified Q with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans alphaDual_gaussianE0T.symm)

private theorem gaussianE1_dual_two_class
    (Q : (dualCurve E1A E1B).toAffine.Point) :
    alphaDual E1A E1B E1B_ne_zero E1C_ne_zero Q = 1 ∨
      alphaDual E1A E1B E1B_ne_zero E1C_ne_zero Q =
        alphaDual E1A E1B E1B_ne_zero E1C_ne_zero
          (dualTorsion E1A E1B E1B_ne_zero E1C_ne_zero) := by
  rcases gaussianE1_alphaDual_classified Q with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans alphaDual_gaussianE1T.symm)

/-- The actual Gaussian curve `E₀` has finitely generated point group. -/
theorem gaussianE0_fg : AddGroup.FG gaussianE0.toAffine.Point := by
  rw [gaussianE0_eq_curve]
  exact
    fg_of_finite_alpha_and_dual_classification
      E0A E0B E0B_ne_zero E0C_ne_zero gaussianE0_dual_two_class

/-- The actual Gaussian curve `E₁` has finitely generated point group. -/
theorem gaussianE1_fg : AddGroup.FG gaussianE1.toAffine.Point := by
  rw [gaussianE1_eq_curve]
  exact
    fg_of_finite_alpha_and_dual_classification
      E1A E1B E1B_ne_zero E1C_ne_zero gaussianE1_dual_two_class

private theorem gaussianE0_two_range_eq_alpha_ker :
    (nsmulAddMonoidHom
      (α := (curve E0A E0B).toAffine.Point) 2).range =
        (alphaHom E0A E0B E0B_ne_zero E0C_ne_zero).ker := by
  ext P
  change
    (∃ U : (curve E0A E0B).toAffine.Point, 2 • U = P) ↔
      alpha E0A E0B E0B_ne_zero E0C_ne_zero P = 1
  rw [alpha_eq_one_iff_two_smul_of_dual_classification
    E0A E0B E0B_ne_zero E0C_ne_zero gaussianE0_dual_two_class P]
  constructor <;> rintro ⟨U, hU⟩
  · exact ⟨U, hU.symm⟩
  · exact ⟨U, hU.symm⟩

private theorem gaussianE1_two_range_eq_alpha_ker :
    (nsmulAddMonoidHom
      (α := (curve E1A E1B).toAffine.Point) 2).range =
        (alphaHom E1A E1B E1B_ne_zero E1C_ne_zero).ker := by
  ext P
  change
    (∃ U : (curve E1A E1B).toAffine.Point, 2 • U = P) ↔
      alpha E1A E1B E1B_ne_zero E1C_ne_zero P = 1
  rw [alpha_eq_one_iff_two_smul_of_dual_classification
    E1A E1B E1B_ne_zero E1C_ne_zero gaussianE1_dual_two_class P]
  constructor <;> rintro ⟨U, hU⟩
  · exact ⟨U, hU.symm⟩
  · exact ⟨U, hU.symm⟩

/-- The image of doubling on `E₀(ℚ(i))` has exact index four. -/
theorem gaussianE0_doubling_index :
    (nsmulAddMonoidHom
      (α := gaussianE0.toAffine.Point) 2).range.index = 4 := by
  rw [gaussianE0_eq_curve, gaussianE0_two_range_eq_alpha_ker,
    AddSubgroup.index_ker, gaussianE0_alphaHom_range_card]

/-- The image of doubling on `E₁(ℚ(i))` has exact index two. -/
theorem gaussianE1_doubling_index :
    (nsmulAddMonoidHom
      (α := gaussianE1.toAffine.Point) 2).range.index = 2 := by
  rw [gaussianE1_eq_curve, gaussianE1_two_range_eq_alpha_ker,
    AddSubgroup.index_ker, gaussianE1_alphaHom_range_card]

/-- The free rank of the actual Gaussian curve `E₀` is one. -/
theorem gaussianE0_freeRank :
    @AddCommGroup.freeRank gaussianE0.toAffine.Point _ gaussianE0_fg = 1 :=
  gaussianE0_freeRank_eq_one_of_fg_and_index
    gaussianE0_fg gaussianE0_doubling_index

/-- The free rank of the actual Gaussian curve `E₁` is zero. -/
theorem gaussianE1_freeRank :
    @AddCommGroup.freeRank gaussianE1.toAffine.Point _ gaussianE1_fg = 0 :=
  gaussianE1_freeRank_eq_zero_of_fg_and_index
    gaussianE1_fg gaussianE1_doubling_index

end GaussianMordellWeil

end

end Cuboid2
