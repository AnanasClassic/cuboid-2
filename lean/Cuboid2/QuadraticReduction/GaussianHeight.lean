import Cuboid2.QuadraticReduction.GaussianCover
import Mathlib.GroupTheory.Descent
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization

/-!
# Heights on the Gaussian elliptic quotients

This file supplies the part of the height argument that is independent of the
two particular Gaussian Weierstrass models.  In particular, it proves that the
homogeneous `addSubMap` really sends the symmetric pair `(P,Q)` to
`(P+Q,P-Q)`, including the points at infinity and the vertical/tangent
degeneracies.  The resulting approximate parallelogram law and Northcott
property feed directly into Mathlib's abstract descent theorem.
-/

namespace Cuboid2.GaussianHeight

noncomputable section

open Height MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace Point

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

abbrev CurvePoint := W.toAffine.Point

/-- The symmetric pair of two affine Weierstrass points, as a point of `ℙ²`. -/
def sym2xProjective (P Q : CurvePoint W) :
    Projectivization K (Fin 3 → K) :=
  Projectivization.mk K (P.sym2x Q) (P.sym2x_ne_zero Q)

/-- The projective value of `W.addSubMap` on the symmetric pair `(P,Q)`. -/
def addSubMapProjective (P Q : CurvePoint W) :
    Projectivization K (Fin 3 → K) :=
  Projectivization.mk K
    (fun i ↦ (W.addSubMap i).eval (P.sym2x Q))
    (W.addSubMap_ne_zero (P.sym2x_ne_zero Q))

private lemma sym2xProjective_comm (P Q : CurvePoint W) :
    sym2xProjective W P Q = sym2xProjective W Q P := by
  unfold sym2xProjective
  apply (Projectivization.mk_eq_mk_iff' K _ _
    (P.sym2x_ne_zero Q) (Q.sym2x_ne_zero P)).mpr
  exact ⟨1, by simpa using (P.sym2x_comm Q).symm⟩

private lemma addSubMapProjective_neg_right (P Q : CurvePoint W) :
    addSubMapProjective W P (-Q) = addSubMapProjective W P Q := by
  unfold addSubMapProjective
  apply (Projectivization.mk_eq_mk_iff' K _ _
    (W.addSubMap_ne_zero (P.sym2x_ne_zero (-Q)))
    (W.addSubMap_ne_zero (P.sym2x_ne_zero Q))).mpr
  refine ⟨1, ?_⟩
  rw [one_smul]
  funext i
  rw [WeierstrassCurve.Affine.Point.sym2x_neg_right]

private lemma addSubMap_eval_zero_zero :
    (fun i ↦ (W.addSubMap i).eval
      ((0 : CurvePoint W).sym2x 0)) =
        (0 : CurvePoint W).sym2x 0 := by
  ext i
  fin_cases i <;> simp [WeierstrassCurve.addSubMap]

private lemma addSubMap_eval_zero_some {x y : K}
    (h : W.toAffine.Nonsingular x y) :
    (fun i ↦ (W.addSubMap i).eval
      ((0 : CurvePoint W).sym2x (.some x y h))) =
        (.some x y h : CurvePoint W).sym2x (-.some x y h) := by
  ext i
  fin_cases i <;> simp [WeierstrassCurve.addSubMap] <;> ring

private lemma addSubMap_eval_some_zero {x y : K}
    (h : W.toAffine.Nonsingular x y) :
    (fun i ↦ (W.addSubMap i).eval
      ((.some x y h : CurvePoint W).sym2x 0)) =
        (.some x y h : CurvePoint W).sym2x (.some x y h) := by
  ext i
  fin_cases i <;> simp [WeierstrassCurve.addSubMap] <;> ring

private lemma diagonal_second {x y : K}
    (h : W.toAffine.Nonsingular x y) :
    (W.addSubMap 1).eval
        ((.some x y h : CurvePoint W).sym2x (.some x y h)) =
      (y - W.toAffine.negY x y) ^ 2 := by
  have heq := h.left
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  change
    y ^ 2 + W.a₁ * x * y + W.a₃ * y =
      x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ at heq
  simp only [WeierstrassCurve.Affine.Point.sym2x_some_some,
    WeierstrassCurve.addSubMap, Fin.isValue, Fin.mk_one,
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val,
    Fin.zero_eta, Fin.reduceFinMk, eval_add, eval_mul, eval_C,
    eval_X, eval_pow]
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.Affine.negY]
  linear_combination -4 * heq

private lemma diagonal_third {x y : K}
    (h : W.toAffine.Nonsingular x y) :
    (W.addSubMap 2).eval
        ((.some x y h : CurvePoint W).sym2x (.some x y h)) = 0 := by
  simp [WeierstrassCurve.addSubMap]
  ring

private lemma diagonal_first [DecidableEq K] {x y : K}
    (h : W.toAffine.Nonsingular x y)
    (hy : y ≠ W.toAffine.negY x y) :
    (W.addSubMap 0).eval
        ((.some x y h : CurvePoint W).sym2x (.some x y h)) =
      (W.addSubMap 1).eval
          ((.some x y h : CurvePoint W).sym2x (.some x y h)) *
        W.toAffine.addX x x (W.toAffine.slope x x y y) := by
  let d := y - W.toAffine.negY x y
  let n := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
  have hd : d ≠ 0 := sub_ne_zero.mpr hy
  have heq := h.left
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  change
    y ^ 2 + W.a₁ * x * y + W.a₃ * y =
      x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ at heq
  have hslope : W.toAffine.slope x x y y = n / d := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
  have hclear :
      d ^ 2 * ((n / d) ^ 2 + W.a₁ * (n / d) - W.a₂ - x - x) =
        n ^ 2 + W.a₁ * n * d - (W.a₂ + 2 * x) * d ^ 2 := by
    field_simp [hd]
    ring
  rw [diagonal_second W h]
  rw [hslope]
  calc
    (W.addSubMap 0).eval
          ((.some x y h : CurvePoint W).sym2x (.some x y h)) =
        x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
          simp [WeierstrassCurve.addSubMap]
          ring
    _ = n ^ 2 + W.a₁ * n * d - (W.a₂ + 2 * x) * d ^ 2 := by
      dsimp only [n, d]
      simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      linear_combination (W.a₁ ^ 2 + 4 * W.a₂ + 8 * x) * heq
    _ = d ^ 2 * ((n / d) ^ 2 + W.a₁ * (n / d) - W.a₂ - x - x) :=
      hclear.symm
    _ = d ^ 2 * W.toAffine.addX x x (n / d) := by
      simp only [WeierstrassCurve.Affine.addX]

private lemma addSubMap_sym2x_diagonal [DecidableEq K] (P : CurvePoint W) :
    addSubMapProjective W P P = sym2xProjective W (P + P) 0 := by
  classical
  rcases P with _ | ⟨x, y, h⟩
  · change addSubMapProjective W (0 : CurvePoint W) 0 =
      sym2xProjective W 0 0
    unfold addSubMapProjective sym2xProjective
    apply (Projectivization.mk_eq_mk_iff' K _ _
      (W.addSubMap_ne_zero ((0 : CurvePoint W).sym2x_ne_zero 0))
      ((0 : CurvePoint W).sym2x_ne_zero 0)).mpr
    exact ⟨1, by simpa using (addSubMap_eval_zero_zero W).symm⟩
  · by_cases hy : y = W.toAffine.negY x y
    · rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
      unfold addSubMapProjective sym2xProjective
      apply (Projectivization.mk_eq_mk_iff' K _ _
        (W.addSubMap_ne_zero
          ((.some x y h : CurvePoint W).sym2x_ne_zero (.some x y h)))
        ((0 : CurvePoint W).sym2x_ne_zero 0)).mpr
      refine ⟨(W.addSubMap 0).eval
        ((.some x y h : CurvePoint W).sym2x (.some x y h)), ?_⟩
      ext i
      fin_cases i
      all_goals
        simp only [Pi.smul_apply, smul_eq_mul,
          WeierstrassCurve.Affine.Point.sym2x_zero_zero,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
      · change
          (W.addSubMap 0).eval
              ((.some x y h : CurvePoint W).sym2x (.some x y h)) * 1 =
            (W.addSubMap 0).eval
              ((.some x y h : CurvePoint W).sym2x (.some x y h))
        exact mul_one _
      · change
          (W.addSubMap 0).eval
              ((.some x y h : CurvePoint W).sym2x (.some x y h)) * 0 =
            (W.addSubMap 1).eval
              ((.some x y h : CurvePoint W).sym2x (.some x y h))
        rw [mul_zero, diagonal_second W h, hy,
          WeierstrassCurve.Affine.negY_negY, ← hy, sub_self]
        norm_num
      · change
          (W.addSubMap 0).eval
              ((.some x y h : CurvePoint W).sym2x (.some x y h)) * 0 =
            (W.addSubMap 2).eval
              ((.some x y h : CurvePoint W).sym2x (.some x y h))
        rw [mul_zero, diagonal_third W h]
    · rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
      unfold addSubMapProjective sym2xProjective
      apply (Projectivization.mk_eq_mk_iff' K _ _
        (W.addSubMap_ne_zero
          ((.some x y h : CurvePoint W).sym2x_ne_zero (.some x y h)))
        ((.some _ _ _ : CurvePoint W).sym2x_ne_zero 0)).mpr
      refine ⟨(W.addSubMap 1).eval
        ((.some x y h : CurvePoint W).sym2x (.some x y h)), ?_⟩
      ext i
      fin_cases i
      all_goals
        simp only [Pi.smul_apply, smul_eq_mul,
          WeierstrassCurve.Affine.Point.sym2x_some_zero,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
      · change
          (W.addSubMap 1).eval
                ((.some x y h : CurvePoint W).sym2x (.some x y h)) *
              W.toAffine.addX x x (W.toAffine.slope x x y y) =
            (W.addSubMap 0).eval
              ((.some x y h : CurvePoint W).sym2x (.some x y h))
        exact (diagonal_first W h hy).symm
      · change
          (W.addSubMap 1).eval
              ((.some x y h : CurvePoint W).sym2x (.some x y h)) * 1 =
            (W.addSubMap 1).eval
              ((.some x y h : CurvePoint W).sym2x (.some x y h))
        exact mul_one _
      · change
          (W.addSubMap 1).eval
              ((.some x y h : CurvePoint W).sym2x (.some x y h)) * 0 =
            (W.addSubMap 2).eval
              ((.some x y h : CurvePoint W).sym2x (.some x y h))
        rw [mul_zero, diagonal_third W h]

private lemma distinct_third {x₁ x₂ y₁ y₂ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    (W.addSubMap 2).eval
        ((.some x₁ y₁ h₁ : CurvePoint W).sym2x (.some x₂ y₂ h₂)) =
      (x₁ - x₂) ^ 2 := by
  simp [WeierstrassCurve.addSubMap]
  ring

private lemma distinct_second [DecidableEq K] {x₁ x₂ y₁ y₂ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    (W.addSubMap 1).eval
        ((.some x₁ y₁ h₁ : CurvePoint W).sym2x (.some x₂ y₂ h₂)) =
      (x₁ - x₂) ^ 2 *
        (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) +
          W.toAffine.addX x₁ x₂
            (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))) := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have heq₁ := h₁.left
  have heq₂ := h₂.left
  rw [WeierstrassCurve.Affine.equation_iff] at heq₁ heq₂
  change
    y₁ ^ 2 + W.a₁ * x₁ * y₁ + W.a₃ * y₁ =
      x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆ at heq₁
  change
    y₂ ^ 2 + W.a₁ * x₂ * y₂ + W.a₃ * y₂ =
      x₂ ^ 3 + W.a₂ * x₂ ^ 2 + W.a₄ * x₂ + W.a₆ at heq₂
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx,
    WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.Point.sym2x_some_some,
    WeierstrassCurve.addSubMap, Fin.isValue, Fin.mk_one,
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val,
    Fin.zero_eta, Fin.reduceFinMk, eval_add, eval_mul, eval_C,
    eval_X, eval_pow, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  field_simp [hd]
  linear_combination -2 * heq₁ - 2 * heq₂

private lemma distinct_first [DecidableEq K] {x₁ x₂ y₁ y₂ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    (W.addSubMap 0).eval
        ((.some x₁ y₁ h₁ : CurvePoint W).sym2x (.some x₂ y₂ h₂)) =
      (x₁ - x₂) ^ 2 *
        (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) *
          W.toAffine.addX x₁ x₂
            (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))) := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have heq₁ := h₁.left
  have heq₂ := h₂.left
  rw [WeierstrassCurve.Affine.equation_iff] at heq₁ heq₂
  change
    y₁ ^ 2 + W.a₁ * x₁ * y₁ + W.a₃ * y₁ =
      x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆ at heq₁
  change
    y₂ ^ 2 + W.a₁ * x₂ * y₂ + W.a₃ * y₂ =
      x₂ ^ 3 + W.a₂ * x₂ ^ 2 + W.a₄ * x₂ + W.a₆ at heq₂
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx,
    WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.Point.sym2x_some_some,
    WeierstrassCurve.addSubMap, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Fin.zero_eta,
    Fin.reduceFinMk, eval_sub, eval_mul, eval_pow, eval_X, eval_C,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  field_simp [hd]
  let q₁ :=
    x₁ ^ 3 - 2 * x₁ ^ 2 * x₂ + x₁ ^ 2 * W.a₂ -
      2 * x₁ * x₂ ^ 2 - x₁ * x₂ * W.a₁ ^ 2 -
      4 * x₁ * x₂ * W.a₂ - x₁ * y₁ * W.a₁ -
      x₁ * W.a₁ * W.a₃ - x₁ * W.a₄ + 2 * x₂ ^ 3 +
      x₂ ^ 2 * W.a₁ ^ 2 + 2 * x₂ ^ 2 * W.a₂ +
      2 * x₂ * y₂ * W.a₁ + x₂ * W.a₁ * W.a₃ -
      y₁ ^ 2 - y₁ * W.a₃ + 2 * y₂ ^ 2 + 2 * y₂ * W.a₃ -
      W.a₆
  let q₂ :=
    4 * x₁ ^ 3 - 2 * x₁ ^ 2 * x₂ + x₁ ^ 2 * W.a₁ ^ 2 +
      4 * x₁ ^ 2 * W.a₂ - 2 * x₁ * x₂ ^ 2 -
      x₁ * x₂ * W.a₁ ^ 2 - 4 * x₁ * x₂ * W.a₂ +
      x₁ * W.a₁ * W.a₃ + 2 * x₁ * W.a₄ + x₂ ^ 3 +
      x₂ ^ 2 * W.a₂ - x₂ * y₂ * W.a₁ -
      x₂ * W.a₁ * W.a₃ - x₂ * W.a₄ - y₂ ^ 2 -
      y₂ * W.a₃ + W.a₆
  linear_combination q₁ * heq₁ + q₂ * heq₂

/-- `addSubMap` sends the symmetric pair `(P,Q)` to `(P+Q,P-Q)` in `ℙ²`.

The proof includes both points at infinity, the vertical and tangent cases,
and the ordinary distinct-`x` addition case. -/
theorem addSubMap_sym2x_projective [DecidableEq K] (P Q : CurvePoint W) :
    addSubMapProjective W P Q =
      sym2xProjective W (P + Q) (P - Q) := by
  classical
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rcases Q with _ | ⟨x₂, y₂, h₂⟩
    · change addSubMapProjective W (0 : CurvePoint W) 0 =
        sym2xProjective W 0 0
      exact addSubMap_sym2x_diagonal W (0 : CurvePoint W)
    · change addSubMapProjective W 0 (.some x₂ y₂ h₂) =
        sym2xProjective W (.some x₂ y₂ h₂) (-.some x₂ y₂ h₂)
      unfold addSubMapProjective sym2xProjective
      apply (Projectivization.mk_eq_mk_iff' K _ _
        (W.addSubMap_ne_zero
          ((0 : CurvePoint W).sym2x_ne_zero (.some x₂ y₂ h₂)))
        ((.some x₂ y₂ h₂ : CurvePoint W).sym2x_ne_zero
          (-.some x₂ y₂ h₂))).mpr
      exact ⟨1, by simpa using (addSubMap_eval_zero_some W h₂).symm⟩
  · rcases Q with _ | ⟨x₂, y₂, h₂⟩
    · change addSubMapProjective W (.some x₁ y₁ h₁) 0 =
        sym2xProjective W (.some x₁ y₁ h₁) (.some x₁ y₁ h₁)
      unfold addSubMapProjective sym2xProjective
      apply (Projectivization.mk_eq_mk_iff' K _ _
        (W.addSubMap_ne_zero
          ((.some x₁ y₁ h₁ : CurvePoint W).sym2x_ne_zero 0))
        ((.some x₁ y₁ h₁ : CurvePoint W).sym2x_ne_zero
          (.some x₁ y₁ h₁))).mpr
      exact ⟨1, by simpa using (addSubMap_eval_some_zero W h₁).symm⟩
    · by_cases hx : x₁ = x₂
      · have hpoints :
            (.some x₁ y₁ h₁ : CurvePoint W) = .some x₂ y₂ h₂ ∨
              (.some x₁ y₁ h₁ : CurvePoint W) = -.some x₂ y₂ h₂ :=
          WeierstrassCurve.Affine.Point.X_eq_iff.mp hx
        rcases hpoints with hpoints | hpoints
        · rw [← hpoints]
          rw [sub_self]
          exact addSubMap_sym2x_diagonal W _
        · have hQ :
              (.some x₂ y₂ h₂ : CurvePoint W) =
                -(.some x₁ y₁ h₁ : CurvePoint W) := by
            exact (neg_neg (.some x₂ y₂ h₂ : CurvePoint W)).symm.trans
              (congrArg Neg.neg hpoints).symm
          rw [hQ]
          rw [add_neg_cancel, sub_neg_eq_add]
          calc
            addSubMapProjective W (.some x₁ y₁ h₁) (-.some x₁ y₁ h₁) =
                addSubMapProjective W (.some x₁ y₁ h₁) (.some x₁ y₁ h₁) :=
              addSubMapProjective_neg_right W _ _
            _ = sym2xProjective W
                ((.some x₁ y₁ h₁ : CurvePoint W) + .some x₁ y₁ h₁) 0 :=
              addSubMap_sym2x_diagonal W _
            _ = sym2xProjective W 0
                ((.some x₁ y₁ h₁ : CurvePoint W) + .some x₁ y₁ h₁) :=
              sym2xProjective_comm W _ _
      · rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
        rw [sub_eq_add_neg, WeierstrassCurve.Affine.Point.neg_some,
          WeierstrassCurve.Affine.Point.add_of_X_ne hx]
        unfold addSubMapProjective sym2xProjective
        apply (Projectivization.mk_eq_mk_iff' K _ _
          (W.addSubMap_ne_zero
            ((.some x₁ y₁ h₁ : CurvePoint W).sym2x_ne_zero
              (.some x₂ y₂ h₂)))
          ((.some _ _ _ : CurvePoint W).sym2x_ne_zero (.some _ _ _))).mpr
        refine ⟨(x₁ - x₂) ^ 2, ?_⟩
        ext i
        fin_cases i
        all_goals
          simp only [Pi.smul_apply, smul_eq_mul,
            WeierstrassCurve.Affine.Point.sym2x_some_some,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
            Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
        · simpa only [WeierstrassCurve.Affine.Point.sym2x_some_some] using
            (distinct_first W h₁ h₂ hx).symm
        · simpa only [WeierstrassCurve.Affine.Point.sym2x_some_some] using
            (distinct_second W h₁ h₂ hx).symm
        · simpa using (distinct_third W h₁ h₂).symm

/-- The naive logarithmic height of a point is the projective height of its
`x`-coordinate.  In particular, the point at infinity has height zero. -/
def naiveHeight [AdmissibleAbsValues K] (P : CurvePoint W) : ℝ :=
  Height.logHeight P.xRep

@[simp]
lemma naiveHeight_zero [AdmissibleAbsValues K] :
    naiveHeight W (0 : CurvePoint W) = 0 := by
  rw [naiveHeight, WeierstrassCurve.Affine.Point.xRep_zero,
    ← Height.logHeight₁_div_eq_logHeight]
  simp

@[simp]
lemma naiveHeight_some [AdmissibleAbsValues K] {x y : K}
    (h : W.toAffine.Nonsingular x y) :
    naiveHeight W (.some x y h) = Height.logHeight₁ x := by
  rw [naiveHeight, WeierstrassCurve.Affine.Point.xRep_some,
    Height.logHeight₁_eq_logHeight]

lemma naiveHeight_nonneg [AdmissibleAbsValues K] (P : CurvePoint W) :
    0 ≤ naiveHeight W P :=
  Height.logHeight_nonneg _

private lemma logHeight_addSubMap_sym2x [AdmissibleAbsValues K]
    [DecidableEq K] (P Q : CurvePoint W) :
    Height.logHeight
        (fun i ↦ (W.addSubMap i).eval (P.sym2x Q)) =
      Height.logHeight ((P + Q).sym2x (P - Q)) := by
  have h := congrArg Projectivization.logHeight
    (addSubMap_sym2x_projective W P Q)
  simpa only [addSubMapProjective, sym2xProjective,
    Projectivization.logHeight_mk] using h

private theorem exists_abs_logHeight_sym2x_sub [AdmissibleAbsValues K] :
    ∃ C, ∀ P Q : CurvePoint W,
      |Height.logHeight (P.sym2x Q) -
          (naiveHeight W P + naiveHeight W Q)| ≤ C := by
  obtain ⟨C, hC⟩ := Height.abs_logHeight_sym2_sub_le (K := K)
  refine ⟨C, fun P Q ↦ ?_⟩
  have hPcoords : ![P.xRep 0, P.xRep 1] = P.xRep := by
    ext i
    fin_cases i <;> rfl
  have hQcoords : ![Q.xRep 0, Q.xRep 1] = Q.xRep := by
    ext i
    fin_cases i <;> rfl
  have hPne : ![P.xRep 0, P.xRep 1] ≠ 0 := by
    rw [hPcoords]
    exact P.xRep_ne_zero
  have hQne : ![Q.xRep 0, Q.xRep 1] ≠ 0 := by
    rw [hQcoords]
    exact Q.xRep_ne_zero
  have hbound :=
    hC (a := P.xRep 0) (b := P.xRep 1)
      (c := Q.xRep 0) (d := Q.xRep 1) hPne hQne
  rw [hPcoords, hQcoords] at hbound
  simpa only [naiveHeight, WeierstrassCurve.Affine.Point.sym2x] using
    hbound

/-- The naive height satisfies the parallelogram law up to a constant depending
only on the Weierstrass model. -/
theorem exists_naiveHeight_parallelogram [AdmissibleAbsValues K]
    [DecidableEq K] :
    ∃ C, ∀ P Q : CurvePoint W,
      |naiveHeight W (P + Q) + naiveHeight W (P - Q) -
          2 * (naiveHeight W P + naiveHeight W Q)| ≤ C := by
  obtain ⟨A, hA⟩ :=
    W.abs_logHeight_addSubMap_sub_two_mul_logHeight_le
  obtain ⟨B, hB⟩ := exists_abs_logHeight_sym2x_sub W
  refine ⟨A + 3 * B, fun P Q ↦ ?_⟩
  have hmap := hA (P.sym2x Q)
  rw [logHeight_addSubMap_sym2x W P Q] at hmap
  have hout := hB (P + Q) (P - Q)
  have hin := hB P Q
  rw [abs_le] at hmap hout hin ⊢
  constructor <;> linarith

/-- Over a number field, bounded naive height contains only finitely many
points.  The only geometric input is that an `x`-coordinate has at most the
two preimages `P` and `-P`. -/
instance instNorthcottNaiveHeight [NumberField K] :
    Northcott (naiveHeight W) where
  finite_le B := by
    let S : Set (CurvePoint W) := {P | naiveHeight W P ≤ B}
    have hx : ({x : K | Height.logHeight₁ x ≤ B} : Set K).Finite :=
      NumberField.finite_setOfPred_logHeight₁_le K B
    refine Set.Finite.of_finite_fibers
      (fun P : CurvePoint W ↦ P.xRep) ?_ ?_
    · refine ((Set.finite_singleton (![1, 0] : Fin 2 → K)).union
          (hx.image fun x : K ↦ ![x, 1])).subset ?_
      rintro _ ⟨P, hP, rfl⟩
      rcases P with _ | ⟨x, y, h⟩
      · exact Set.mem_union_left _ (by
          simpa only [← WeierstrassCurve.Affine.Point.zero_def,
            WeierstrassCurve.Affine.Point.xRep_zero] using
              (Set.mem_singleton (![1, 0] : Fin 2 → K)))
      · refine Set.mem_union_right _ ?_
        refine ⟨x, ?_, by simp⟩
        simpa only [Set.mem_setOf_eq, naiveHeight_some W h] using hP
    · intro _ hr
      obtain ⟨P, hP, rfl⟩ := hr
      refine ((Set.finite_singleton (-P)).insert P).subset ?_
      rintro Q ⟨_, hQ⟩
      have hrep : Q.xRep = P.xRep := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hQ
      rcases
          WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hrep with
        hQP | hQP
      · simp [hQP]
      · simp [hQP]

/-- Conditional Mordell--Weil endpoint: finite index of the doubling image,
together with the height facts proved above, implies finite generation. -/
theorem fg_of_finiteIndex_two [NumberField K] [DecidableEq K]
    (hindex :
      (nsmulAddMonoidHom (α := CurvePoint W) 2).range.FiniteIndex) :
    AddGroup.FG (CurvePoint W) := by
  obtain ⟨C, hpar⟩ := exists_naiveHeight_parallelogram W
  exact AddCommGroup.fg_of_descent' hindex (naiveHeight_nonneg W) hpar

end Point

end

end Cuboid2.GaussianHeight
