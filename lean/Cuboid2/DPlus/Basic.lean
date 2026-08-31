import Mathlib

/-!
# The explicit genus-two curve `D+`

Only exact algebra is developed here.  Rank, local logarithm, and rational
point classification enter through separate, explicitly tracked theorems.
-/

namespace Cuboid2

noncomputable section

/-- Right-hand side of `D+ : R^2 = 4 a^5 - 8 a^2 + 5 a`. -/
def dplusRhs (a : ℚ) : ℚ :=
  4 * a ^ 5 - 8 * a ^ 2 + 5 * a

/-- Right-hand side of the octic cover used in the `2+3` reduction. -/
def octicRhs (u : ℚ) : ℚ :=
  4 * u ^ 8 - 8 * u ^ 2 + 5

/-- An affine rational point on `D+`. -/
structure DPlusAffinePoint where
  a : ℚ
  R : ℚ
  onCurve : R ^ 2 = dplusRhs a

/-- A rational point on the octic cover. -/
structure OcticPoint where
  u : ℚ
  r : ℚ
  onCurve : r ^ 2 = octicRhs u

/-- Squarehood of the affine abscissa. -/
def DPlusAffinePoint.HasSquareAbscissa (P : DPlusAffinePoint) : Prop :=
  ∃ u : ℚ, P.a = u ^ 2

/-- The polynomial identity behind `(u,r) ↦ (u^2,u r)`. -/
theorem dplus_pullback_identity (u : ℚ) :
    dplusRhs (u ^ 2) = u ^ 2 * octicRhs u := by
  simp [dplusRhs, octicRhs]
  ring

/-- Exact map from the octic cover to `D+`. -/
def OcticPoint.toDPlus (P : OcticPoint) : DPlusAffinePoint where
  a := P.u ^ 2
  R := P.u * P.r
  onCurve := by
    calc
      (P.u * P.r) ^ 2 = P.u ^ 2 * P.r ^ 2 := by ring
      _ = P.u ^ 2 * octicRhs P.u := by rw [P.onCurve]
      _ = dplusRhs (P.u ^ 2) := (dplus_pullback_identity P.u).symm

/-- The image of the octic map has square abscissa by construction. -/
theorem OcticPoint.toDPlus_hasSquareAbscissa (P : OcticPoint) :
    P.toDPlus.HasSquareAbscissa := by
  exact ⟨P.u, rfl⟩

/-- The known Weierstrass point `(0,0)`. -/
def dplusZero : DPlusAffinePoint where
  a := 0
  R := 0
  onCurve := by norm_num [dplusRhs]

/-- The known point `(1,1)`. -/
def dplusOnePlus : DPlusAffinePoint where
  a := 1
  R := 1
  onCurve := by norm_num [dplusRhs]

/-- The known point `(1,-1)`. -/
def dplusOneMinus : DPlusAffinePoint where
  a := 1
  R := -1
  onCurve := by norm_num [dplusRhs]

@[simp] theorem dplusZero_hasSquareAbscissa :
    dplusZero.HasSquareAbscissa := by
  exact ⟨0, by norm_num [dplusZero]⟩

@[simp] theorem dplusOnePlus_hasSquareAbscissa :
    dplusOnePlus.HasSquareAbscissa := by
  exact ⟨1, by norm_num [dplusOnePlus]⟩

@[simp] theorem dplusOneMinus_hasSquareAbscissa :
    dplusOneMinus.HasSquareAbscissa := by
  exact ⟨1, by norm_num [dplusOneMinus]⟩

/-- The exact infinity-chart relation from `clean3`. -/
def infinityRelation (t w : ℚ) : Prop :=
  w = t ^ 2 * (1 - 2 * w ^ 3 + (5 / 4 : ℚ) * w ^ 4)

/-- The origin is on the implicit infinity chart and its `w`-linear coefficient is a unit. -/
theorem infinityRelation_origin : infinityRelation 0 0 := by
  norm_num [infinityRelation]

/--
The stored truncation `w=t^2-2t^8+5t^10/4` satisfies the implicit equation
through degree thirteen; the residual has the explicit factor `t^14`.
-/
theorem infinity_series_residual_order (t : ℚ) :
    let w := t ^ 2 - 2 * t ^ 8 + (5 / 4 : ℚ) * t ^ 10
    w - t ^ 2 * (1 - 2 * w ^ 3 + (5 / 4 : ℚ) * w ^ 4) =
      t ^ 14 *
        (-12 + (35 / 2 : ℚ) * t ^ 2 - (25 / 4 : ℚ) * t ^ 4 +
          24 * t ^ 6 - 60 * t ^ 8 + (375 / 8 : ℚ) * t ^ 10 -
          (887 / 32 : ℚ) * t ^ 12 + 70 * t ^ 14 -
          (375 / 4 : ℚ) * t ^ 16 + (1625 / 32 : ℚ) * t ^ 18 -
          (1905 / 64 : ℚ) * t ^ 20 + 50 * t ^ 22 -
          (375 / 8 : ℚ) * t ^ 24 + (625 / 32 : ℚ) * t ^ 26 -
          (3125 / 1024 : ℚ) * t ^ 28) := by
  dsimp
  ring

end

end Cuboid2
