import Cuboid2.QuadraticReduction.GaussianFraction
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# The algebraic Gaussian two-isogeny descent

This file develops the part of the Gaussian descent which is independent of
Mordell--Weil finite generation and elliptic heights.  In particular, the
degree-two maps below are total maps on Mathlib's actual affine point type:
the point at infinity and the rational two-torsion point are handled
explicitly, rather than being hidden behind a rational-map convention.

No rank, finite-generation, or analytic-rank hypothesis is introduced here.
-/

namespace Cuboid2

noncomputable section

open scoped QuadraticAlgebra

namespace GaussianDescent

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

/-! ## The two-isogeny models -/

/-- The Weierstrass model `E(A,B) : y² = x(x² + Ax + B)`. -/
def curve (A B : GaussianRat) : WeierstrassCurve GaussianRat where
  a₁ := 0
  a₂ := A
  a₃ := 0
  a₄ := B
  a₆ := 0

/-- The standard two-isogenous model
`E'(A,B) : y² = x(x² - 2Ax + (A² - 4B))`. -/
def dualCurve (A B : GaussianRat) : WeierstrassCurve GaussianRat :=
  curve (-2 * A) (A ^ 2 - 4 * B)

@[simp] theorem curve_a₁ (A B : GaussianRat) : (curve A B).a₁ = 0 := rfl
@[simp] theorem curve_a₂ (A B : GaussianRat) : (curve A B).a₂ = A := rfl
@[simp] theorem curve_a₃ (A B : GaussianRat) : (curve A B).a₃ = 0 := rfl
@[simp] theorem curve_a₄ (A B : GaussianRat) : (curve A B).a₄ = B := rfl
@[simp] theorem curve_a₆ (A B : GaussianRat) : (curve A B).a₆ = 0 := rfl

@[simp] theorem dualCurve_a₂ (A B : GaussianRat) :
    (dualCurve A B).a₂ = -2 * A := rfl

@[simp] theorem dualCurve_a₄ (A B : GaussianRat) :
    (dualCurve A B).a₄ = A ^ 2 - 4 * B := rfl

/-- The exact discriminant of the two-torsion model. -/
theorem curve_discriminant (A B : GaussianRat) :
    (curve A B).Δ = 16 * B ^ 2 * (A ^ 2 - 4 * B) := by
  simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- The exact discriminant of the dual model. -/
theorem dualCurve_discriminant (A B : GaussianRat) :
    (dualCurve A B).Δ = 256 * B * (A ^ 2 - 4 * B) ^ 2 := by
  rw [dualCurve, curve_discriminant]
  ring

/-- Nonsingularity criterion for `E(A,B)`. -/
theorem curve_discriminant_ne_zero {A B : GaussianRat}
    (hB : B ≠ 0) (hC : A ^ 2 - 4 * B ≠ 0) :
    (curve A B).Δ ≠ 0 := by
  rw [curve_discriminant]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hB)) hC

/-- Nonsingularity criterion for the dual model. -/
theorem dualCurve_discriminant_ne_zero {A B : GaussianRat}
    (hB : B ≠ 0) (hC : A ^ 2 - 4 * B ≠ 0) :
    (dualCurve A B).Δ ≠ 0 := by
  rw [dualCurve_discriminant]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hB) (pow_ne_zero 2 hC)

/-- The source curve equation in its factored form. -/
theorem curve_equation_iff {A B x y : GaussianRat} :
    (curve A B).toAffine.Equation x y ↔
      y ^ 2 = x * (x ^ 2 + A * x + B) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [curve, zero_mul, zero_add, add_zero]
  ring_nf

/-- The dual curve equation in its factored form. -/
theorem dualCurve_equation_iff {A B X Y : GaussianRat} :
    (dualCurve A B).toAffine.Equation X Y ↔
      Y ^ 2 = X * (X ^ 2 - 2 * A * X + (A ^ 2 - 4 * B)) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [dualCurve, curve, zero_mul, zero_add, add_zero]
  ring_nf

/-- Turn an equation proof into an actual affine point, using a separately
verified nonzero discriminant. -/
def pointOfEquation (W : WeierstrassCurve GaussianRat) (hΔ : W.Δ ≠ 0)
    {x y : GaussianRat} (h : W.toAffine.Equation x y) :
    W.toAffine.Point :=
  .some x y ((W.toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp h)

/-- The rational two-torsion point on `E(A,B)`. -/
def torsion (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0) :
    (curve A B).toAffine.Point :=
  pointOfEquation (curve A B) (curve_discriminant_ne_zero hB hC)
    (x := 0) (y := 0) (by rw [curve_equation_iff]; ring)

/-- The rational two-torsion point on the dual curve. -/
def dualTorsion (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0) :
    (dualCurve A B).toAffine.Point :=
  pointOfEquation (dualCurve A B) (dualCurve_discriminant_ne_zero hB hC)
    (x := 0) (y := 0) (by rw [dualCurve_equation_iff]; ring)

/-! ## Total formulas for the two degree-two maps -/

private theorem phi_equation {A B x y : GaussianRat}
    (hx : x ≠ 0)
    (hxy : y ^ 2 = x * (x ^ 2 + A * x + B)) :
    (dualCurve A B).toAffine.Equation
      (y ^ 2 / x ^ 2) (y * (B - x ^ 2) / x ^ 2) := by
  rw [dualCurve_equation_iff]
  field_simp [hx]
  rw [hxy]
  ring

/-- The standard degree-two map `E(A,B) → E'(A,B)`.

It maps both infinity and `(0,0)` to infinity.  On every other affine
point it is
`(x,y) ↦ (y²/x², y(B-x²)/x²)`.
-/
def phi (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0) :
    (curve A B).toAffine.Point → (dualCurve A B).toAffine.Point
  | .zero => 0
  | .some x y h =>
      if hx : x = 0 then 0
      else
        pointOfEquation (dualCurve A B)
          (dualCurve_discriminant_ne_zero hB hC)
          (phi_equation hx (curve_equation_iff.mp h.left))

private theorem phiHat_equation {A B X Y : GaussianRat}
    (hX : X ≠ 0)
    (hXY : Y ^ 2 = X * (X ^ 2 - 2 * A * X + (A ^ 2 - 4 * B))) :
    (curve A B).toAffine.Equation
      (Y ^ 2 / (4 * X ^ 2))
      (Y * ((A ^ 2 - 4 * B) - X ^ 2) / (8 * X ^ 2)) := by
  rw [curve_equation_iff]
  field_simp [hX]
  rw [hXY]
  ring

/-- The normalized dual degree-two map `E'(A,B) → E(A,B)`.

It maps both infinity and `(0,0)` to infinity.  On every other affine
point it is
`(X,Y) ↦ (Y²/(4X²), Y((A²-4B)-X²)/(8X²))`.
-/
def phiHat (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0) :
    (dualCurve A B).toAffine.Point → (curve A B).toAffine.Point
  | .zero => 0
  | .some X Y h =>
      if hX : X = 0 then 0
      else
        pointOfEquation (curve A B)
          (curve_discriminant_ne_zero hB hC)
          (phiHat_equation hX (dualCurve_equation_iff.mp h.left))

private theorem phiHat_phi_x {A B x y : GaussianRat}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hneg : y ≠ (curve A B).toAffine.negY x y)
    (hxy : y ^ 2 = x * (x ^ 2 + A * x + B)) :
    let X := y ^ 2 / x ^ 2
    let Y := y * (B - x ^ 2) / x ^ 2
    Y ^ 2 / (4 * X ^ 2) =
      (curve A B).toAffine.addX x x
        ((curve A B).toAffine.slope x x y y) := by
  dsimp only
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  simp only [curve, zero_mul, sub_zero, add_zero,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY]
  field_simp [hx, hy]
  rw [hxy]
  ring

private theorem phiHat_phi_y {A B x y : GaussianRat}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hneg : y ≠ (curve A B).toAffine.negY x y)
    (hxy : y ^ 2 = x * (x ^ 2 + A * x + B)) :
    let X := y ^ 2 / x ^ 2
    let Y := y * (B - x ^ 2) / x ^ 2
    Y * ((A ^ 2 - 4 * B) - X ^ 2) / (8 * X ^ 2) =
      (curve A B).toAffine.addY x x y
        ((curve A B).toAffine.slope x x y y) := by
  dsimp only
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  simp only [curve, zero_mul, sub_zero, add_zero,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX]
  have hy4 : y ^ 4 = (x * (x ^ 2 + A * x + B)) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = _ := by rw [hxy]
  field_simp [hx, hy]
  rw [hy4, hxy]
  ring

private theorem phi_phiHat_x {A B X Y : GaussianRat}
    (hX : X ≠ 0) (hY : Y ≠ 0)
    (hneg : Y ≠ (dualCurve A B).toAffine.negY X Y)
    (hXY : Y ^ 2 =
      X * (X ^ 2 - 2 * A * X + (A ^ 2 - 4 * B))) :
    let x := Y ^ 2 / (4 * X ^ 2)
    let y := Y * ((A ^ 2 - 4 * B) - X ^ 2) / (8 * X ^ 2)
    y ^ 2 / x ^ 2 =
      (dualCurve A B).toAffine.addX X X
        ((dualCurve A B).toAffine.slope X X Y Y) := by
  dsimp only
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  simp only [dualCurve, curve, zero_mul, sub_zero, add_zero,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY]
  field_simp [hX, hY]
  rw [hXY]
  ring

private theorem phi_phiHat_y {A B X Y : GaussianRat}
    (hX : X ≠ 0) (hY : Y ≠ 0)
    (hneg : Y ≠ (dualCurve A B).toAffine.negY X Y)
    (hXY : Y ^ 2 =
      X * (X ^ 2 - 2 * A * X + (A ^ 2 - 4 * B))) :
    let x := Y ^ 2 / (4 * X ^ 2)
    let y := Y * ((A ^ 2 - 4 * B) - X ^ 2) / (8 * X ^ 2)
    y * (B - x ^ 2) / x ^ 2 =
      (dualCurve A B).toAffine.addY X X Y
        ((dualCurve A B).toAffine.slope X X Y Y) := by
  dsimp only
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  simp only [dualCurve, curve, zero_mul, sub_zero, add_zero,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX]
  have hY4 : Y ^ 4 =
      (X * (X ^ 2 - 2 * A * X + (A ^ 2 - 4 * B))) ^ 2 := by
    calc
      Y ^ 4 = (Y ^ 2) ^ 2 := by ring
      _ = _ := by rw [hXY]
  field_simp [hX, hY]
  rw [hY4, hXY]
  ring

@[simp] theorem phi_zero (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0) :
    phi A B hB hC 0 = 0 := rfl

@[simp] theorem phiHat_zero (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0) :
    phiHat A B hB hC 0 = 0 := rfl

/-- The normalized dual map composed with the forward map is doubling on
Mathlib's actual point group, including both exceptional branches. -/
theorem phiHat_phi (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0)
    (P : (curve A B).toAffine.Point) :
    phiHat A B hB hC (phi A B hB hC P) = 2 • P := by
  rcases P with (_ | ⟨x, y, h⟩)
  · rw [two_nsmul]
    rfl
  · have hxy : y ^ 2 = x * (x ^ 2 + A * x + B) :=
      curve_equation_iff.mp h.left
    by_cases hx : x = 0
    · have hy : y = 0 := by
        rw [hx] at hxy
        have hy2 : y ^ 2 = 0 := by simpa using hxy
        exact sq_eq_zero_iff.mp hy2
      subst x
      subst y
      simp only [phi, ↓reduceDIte, phiHat]
      rw [two_nsmul]
      symm
      apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
      simp [curve]
    · by_cases hy : y = 0
      · subst y
        simp only [phi, hx, ↓reduceDIte, pointOfEquation, phiHat,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]
        rw [two_nsmul]
        symm
        apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
        simp [curve]
      · have hX : y ^ 2 / x ^ 2 ≠ 0 :=
          div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx)
        have hneg : y ≠ (curve A B).toAffine.negY x y := by
          simp only [curve, WeierstrassCurve.Affine.negY, zero_mul,
            sub_zero]
          intro hEq
          apply hy
          have htwo : (2 : GaussianRat) * y = 0 := by
            linear_combination hEq
          exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
        rw [two_nsmul,
          WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
        simp only [phi, hx, ↓reduceDIte, pointOfEquation, phiHat, hX]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨phiHat_phi_x hx hy hneg hxy,
          phiHat_phi_y hx hy hneg hxy⟩

/-- The forward map composed with the normalized dual map is doubling on the
dual point group, including both exceptional branches. -/
theorem phi_phiHat (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0)
    (Q : (dualCurve A B).toAffine.Point) :
    phi A B hB hC (phiHat A B hB hC Q) = 2 • Q := by
  rcases Q with (_ | ⟨X, Y, h⟩)
  · rw [two_nsmul]
    rfl
  · have hXY : Y ^ 2 =
        X * (X ^ 2 - 2 * A * X + (A ^ 2 - 4 * B)) :=
      dualCurve_equation_iff.mp h.left
    by_cases hX : X = 0
    · have hY : Y = 0 := by
        rw [hX] at hXY
        have hY2 : Y ^ 2 = 0 := by simpa using hXY
        exact sq_eq_zero_iff.mp hY2
      subst X
      subst Y
      simp only [phiHat, ↓reduceDIte, phi]
      rw [two_nsmul]
      symm
      apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
      simp [dualCurve, curve]
    · by_cases hY : Y = 0
      · subst Y
        simp only [phiHat, hX, ↓reduceDIte, pointOfEquation, phi,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]
        rw [two_nsmul]
        symm
        apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
        simp [dualCurve, curve]
      · have hx : Y ^ 2 / (4 * X ^ 2) ≠ 0 :=
          div_ne_zero (pow_ne_zero 2 hY)
            (mul_ne_zero (by norm_num) (pow_ne_zero 2 hX))
        have hneg : Y ≠ (dualCurve A B).toAffine.negY X Y := by
          simp only [dualCurve, curve, WeierstrassCurve.Affine.negY,
            zero_mul, sub_zero]
          intro hEq
          apply hY
          have htwo : (2 : GaussianRat) * Y = 0 := by
            linear_combination hEq
          exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
        rw [two_nsmul,
          WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
        simp only [phiHat, hX, ↓reduceDIte, pointOfEquation, phi, hx]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨phi_phiHat_x hX hY hneg hXY,
          phi_phiHat_y hX hY hneg hXY⟩

/-- The set-theoretic kernel of the forward degree-two map consists exactly
of infinity and `(0,0)`. -/
theorem phi_eq_zero_iff (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0)
    (P : (curve A B).toAffine.Point) :
    phi A B hB hC P = 0 ↔
      P = 0 ∨ P = torsion A B hB hC := by
  rcases P with (_ | ⟨x, y, h⟩)
  · constructor
    · intro
      exact Or.inl rfl
    · intro
      rfl
  · have hxy : y ^ 2 = x * (x ^ 2 + A * x + B) :=
      curve_equation_iff.mp h.left
    by_cases hx : x = 0
    · have hy : y = 0 := by
        rw [hx] at hxy
        have hy2 : y ^ 2 = 0 := by simpa using hxy
        exact sq_eq_zero_iff.mp hy2
      subst x
      subst y
      simp [phi, torsion, pointOfEquation]
    · simp [phi, hx, pointOfEquation, torsion]

/-- The set-theoretic kernel of the normalized dual map also consists
exactly of infinity and `(0,0)`. -/
theorem phiHat_eq_zero_iff (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0)
    (Q : (dualCurve A B).toAffine.Point) :
    phiHat A B hB hC Q = 0 ↔
      Q = 0 ∨ Q = dualTorsion A B hB hC := by
  rcases Q with (_ | ⟨X, Y, h⟩)
  · constructor
    · intro
      exact Or.inl rfl
    · intro
      rfl
  · have hXY : Y ^ 2 =
        X * (X ^ 2 - 2 * A * X + (A ^ 2 - 4 * B)) :=
      dualCurve_equation_iff.mp h.left
    by_cases hX : X = 0
    · have hY : Y = 0 := by
        rw [hX] at hXY
        have hY2 : Y ^ 2 = 0 := by simpa using hXY
        exact sq_eq_zero_iff.mp hY2
      subst X
      subst Y
      simp [phiHat, dualTorsion, pointOfEquation]
    · simp [phiHat, hX, pointOfEquation, dualTorsion]

/-- The forward degree-two map commutes with inversion. -/
theorem phi_neg (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0)
    (P : (curve A B).toAffine.Point) :
    phi A B hB hC (-P) = -phi A B hB hC P := by
  rcases P with (_ | ⟨x, y, h⟩)
  · rfl
  · have hxy : y ^ 2 = x * (x ^ 2 + A * x + B) :=
      curve_equation_iff.mp h.left
    by_cases hx : x = 0
    · have hy : y = 0 := by
        rw [hx] at hxy
        exact sq_eq_zero_iff.mp (by simpa using hxy)
      subst x
      subst y
      rfl
    · rw [WeierstrassCurve.Affine.Point.neg_some]
      simp only [phi, hx, ↓reduceDIte, pointOfEquation,
        WeierstrassCurve.Affine.Point.neg_some]
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      simp only [curve, dualCurve, WeierstrassCurve.Affine.negY,
        zero_mul, sub_zero]
      constructor <;> ring

/-! ## The Kummer squareclass and descent maps -/

/-- The genuine multiplicative squareclass group
`Kˣ / (Kˣ)²` for `K = ℚ(i)`. -/
abbrev SquareClass :=
  GaussianRatˣ ⧸ (powMonoidHom (α := GaussianRatˣ) 2).range

/-- The squareclass of a nonzero Gaussian rational. -/
def squareClassOf (x : GaussianRat) (hx : x ≠ 0) : SquareClass :=
  QuotientGroup.mk (Units.mk0 x hx)

theorem squareClassOf_congr {x y : GaussianRat} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x = y) :
    squareClassOf x hx = squareClassOf y hy := by
  subst y
  rfl

@[simp] theorem squareClassOf_one :
    squareClassOf 1 one_ne_zero = 1 := by
  simp [squareClassOf, Units.mk0_one]

/-- A nonzero element has trivial squareclass exactly when it is a square in
the field. -/
theorem squareClassOf_eq_one_iff {x : GaussianRat} (hx : x ≠ 0) :
    squareClassOf x hx = 1 ↔ IsSquare x := by
  constructor
  · intro h
    have hmem :
        Units.mk0 x hx ∈
          (powMonoidHom (α := GaussianRatˣ) 2).range :=
      (QuotientGroup.eq_one_iff _).mp h
    rcases hmem with ⟨u, hu⟩
    refine ⟨(u : GaussianRat), ?_⟩
    have hval := congrArg Units.val hu
    have hval' : (u : GaussianRat) ^ 2 = x := by
      simpa only [powMonoidHom_apply, Units.val_pow_eq_pow_val,
        Units.val_mk0] using hval
    simpa only [pow_two] using hval'.symm
  · rintro ⟨z, hz⟩
    have hz0 : z ≠ 0 := by
      intro hz0
      apply hx
      calc
        x = z * z := hz
        _ = 0 := by simp [hz0]
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨Units.mk0 z hz0, ?_⟩
    apply Units.ext
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val,
      Units.val_mk0]
    simpa only [pow_two] using hz.symm

/-- Equality of field squareclasses is multiplication by an explicit square. -/
theorem squareClassOf_eq_iff {x y : GaussianRat} (hx : x ≠ 0) (hy : y ≠ 0) :
    squareClassOf x hx = squareClassOf y hy ↔
      ∃ z : GaussianRat, z ≠ 0 ∧ x = y * z ^ 2 := by
  constructor
  · intro h
    change
      QuotientGroup.mk (Units.mk0 x hx) =
        (QuotientGroup.mk (Units.mk0 y hy) : SquareClass) at h
    have hq :
        QuotientGroup.mk (Units.mk0 x hx / Units.mk0 y hy) =
          (1 : SquareClass) := by
      calc
        QuotientGroup.mk (Units.mk0 x hx / Units.mk0 y hy) =
            QuotientGroup.mk (Units.mk0 x hx) /
              (QuotientGroup.mk (Units.mk0 y hy) : SquareClass) :=
          QuotientGroup.mk_div
            (powMonoidHom (α := GaussianRatˣ) 2).range _ _
        _ = QuotientGroup.mk (Units.mk0 y hy) /
              (QuotientGroup.mk (Units.mk0 y hy) : SquareClass) := by rw [h]
        _ = 1 := div_self' _
    rcases (QuotientGroup.eq_one_iff _).mp hq with ⟨u, hu⟩
    refine ⟨(u : GaussianRat), u.ne_zero, ?_⟩
    have hval := congrArg Units.val hu
    change (u : GaussianRat) ^ 2 = x / y at hval
    calc
      x = y * (x / y) := by field_simp [hy]
      _ = y * (u : GaussianRat) ^ 2 := by rw [hval]
  · rintro ⟨z, hz, rfl⟩
    change
      QuotientGroup.mk (Units.mk0 (y * z ^ 2) hx) =
        (QuotientGroup.mk (Units.mk0 y hy) : SquareClass)
    rw [show Units.mk0 (y * z ^ 2) hx =
        Units.mk0 y hy * (Units.mk0 z hz) ^ 2 by
      apply Units.ext
      simp]
    rw [QuotientGroup.mk_mul]
    have hsquare :
        (QuotientGroup.mk ((Units.mk0 z hz) ^ 2) : SquareClass) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr
        ⟨Units.mk0 z hz, by simp [powMonoidHom_apply]⟩
    rw [hsquare, mul_one]

/-- Multiplication of representatives agrees with multiplication in the
squareclass quotient. -/
theorem squareClassOf_mul {x y : GaussianRat} (hx : x ≠ 0) (hy : y ≠ 0) :
    squareClassOf (x * y) (mul_ne_zero hx hy) =
      squareClassOf x hx * squareClassOf y hy := by
  change
    QuotientGroup.mk (Units.mk0 (x * y) (mul_ne_zero hx hy)) =
      QuotientGroup.mk (Units.mk0 x hx) *
        (QuotientGroup.mk (Units.mk0 y hy) : SquareClass)
  rw [show Units.mk0 (x * y) (mul_ne_zero hx hy) =
      Units.mk0 x hx * Units.mk0 y hy by
    apply Units.ext
    rfl]
  exact QuotientGroup.mk_mul
    (powMonoidHom (α := GaussianRatˣ) 2).range _ _

/-- Every Gaussian squareclass has exponent two. -/
theorem squareClass_mul_self (d : SquareClass) : d * d = 1 := by
  refine QuotientGroup.induction_on d ?_
  intro u
  rw [← QuotientGroup.mk_mul
    (powMonoidHom (α := GaussianRatˣ) 2).range]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨u, by simp [powMonoidHom_apply, pow_two]⟩

private theorem curve_addX_product {A B x₁ y₁ x₂ y₂ : GaussianRat}
    (h₁ : (curve A B).toAffine.Equation x₁ y₁)
    (h₂ : (curve A B).toAffine.Equation x₂ y₂)
    (hvert : ¬(x₁ = x₂ ∧
      y₁ = (curve A B).toAffine.negY x₂ y₂)) :
    x₁ * x₂ *
        (curve A B).toAffine.addX x₁ x₂
          ((curve A B).toAffine.slope x₁ x₂ y₁ y₂) =
      (y₁ - (curve A B).toAffine.slope x₁ x₂ y₁ y₂ * x₁) ^ 2 := by
  have heq₁ := curve_equation_iff.mp h₁
  have heq₂ := curve_equation_iff.mp h₂
  by_cases hx : x₁ = x₂
  · have hyneg : y₁ ≠ (curve A B).toAffine.negY x₂ y₂ :=
      fun hy => hvert ⟨hx, hy⟩
    have hy : y₁ = y₂ :=
      WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ hx hyneg
    subst x₂
    subst y₂
    have hy0 : y₁ ≠ 0 := by
      intro hy0
      apply hyneg
      subst y₁
      simp [curve]
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyneg]
    simp only [curve, WeierstrassCurve.Affine.negY, zero_mul,
      sub_zero, add_zero, WeierstrassCurve.Affine.addX]
    field_simp [hy0]
    rw [heq₁]
    ring
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    simp only [curve, WeierstrassCurve.Affine.addX, zero_mul,
      add_zero]
    field_simp [hx]
    ring_nf
    rw [heq₁, heq₂]
    ring

private theorem torsion_addX {A B x y : GaussianRat} (hx : x ≠ 0)
    (hxy : y ^ 2 = x * (x ^ 2 + A * x + B)) :
    (curve A B).toAffine.addX 0 x
        ((curve A B).toAffine.slope 0 x 0 y) = B / x := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (Ne.symm hx)]
  simp only [curve, WeierstrassCurve.Affine.addX, zero_sub,
    zero_mul, zero_add]
  field_simp [hx]
  rw [hxy]
  ring

private theorem torsion_addY {A B x y : GaussianRat} (hx : x ≠ 0)
    (hxy : y ^ 2 = x * (x ^ 2 + A * x + B)) :
    (curve A B).toAffine.addY 0 x 0
        ((curve A B).toAffine.slope 0 x 0 y) =
      -(B * y / x ^ 2) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (Ne.symm hx)]
  simp only [curve, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.addX, zero_sub, zero_mul, zero_add,
    sub_zero]
  field_simp [hx]
  rw [hxy]
  ring

/-- Translation by the kernel point does not change the forward
degree-two map. -/
theorem phi_torsion_add (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0)
    (P : (curve A B).toAffine.Point) :
    phi A B hB hC (torsion A B hB hC + P) =
      phi A B hB hC P := by
  rcases P with (_ | ⟨x, y, h⟩)
  · change phi A B hB hC
        (torsion A B hB hC +
          (0 : (curve A B).toAffine.Point)) =
      phi A B hB hC 0
    rw [add_zero]
    rfl
  · have hxy : y ^ 2 = x * (x ^ 2 + A * x + B) :=
      curve_equation_iff.mp h.left
    by_cases hx : x = 0
    · have hy : y = 0 := by
        rw [hx] at hxy
        exact sq_eq_zero_iff.mp (by simpa using hxy)
      subst x
      subst y
      rw [show WeierstrassCurve.Affine.Point.some 0 0 h =
          torsion A B hB hC by
        simp [torsion, pointOfEquation]]
      have htY :
          (0 : GaussianRat) =
            (curve A B).toAffine.negY 0 0 := by simp [curve]
      have htadd :
          torsion A B hB hC + torsion A B hB hC = 0 := by
        change
          WeierstrassCurve.Affine.Point.some 0 0 _ +
              WeierstrassCurve.Affine.Point.some 0 0 _ = 0
        exact WeierstrassCurve.Affine.Point.add_of_Y_eq rfl htY
      rw [htadd]
      rfl
    · have haddX :
          (curve A B).toAffine.addX 0 x
              ((curve A B).toAffine.slope 0 x 0 y) = B / x :=
        torsion_addX hx hxy
      have haddY :
          (curve A B).toAffine.addY 0 x 0
              ((curve A B).toAffine.slope 0 x 0 y) =
            -(B * y / x ^ 2) :=
        torsion_addY hx hxy
      have hBx : B / x ≠ 0 := div_ne_zero hB hx
      have hAddX :
          (curve A B).toAffine.addX 0 x
              ((curve A B).toAffine.slope 0 x 0 y) ≠ 0 := by
        rw [haddX]
        exact hBx
      rw [torsion, pointOfEquation,
        WeierstrassCurve.Affine.Point.add_of_X_ne (Ne.symm hx)]
      simp only [phi, hAddX, hx, ↓reduceDIte, pointOfEquation]
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      constructor
      · rw [haddX, haddY]
        field_simp [hB, hx]
      · rw [haddX, haddY]
        field_simp [hB, hx]
        ring

/-- The usual two-isogeny descent map on `E(A,B)`.

It takes infinity to `1`, `(0,0)` to the class of `B`, and every affine
point with nonzero `x` to the class of `x`.
-/
def alpha (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0) :
    (curve A B).toAffine.Point → SquareClass
  | .zero => 1
  | .some x _ _ =>
      if hx : x = 0 then squareClassOf B hB else squareClassOf x hx

/-- The corresponding descent map on the dual curve. -/
def alphaDual (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0) :
    (dualCurve A B).toAffine.Point → SquareClass
  | .zero => 1
  | .some X _ _ =>
      if hX : X = 0 then squareClassOf (A ^ 2 - 4 * B) hC
      else squareClassOf X hX

@[simp] theorem alpha_zero (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0) :
    alpha A B hB hC 0 = 1 := rfl

@[simp] theorem alphaDual_zero (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0) :
    alphaDual A B hB hC 0 = 1 := rfl

private theorem div_squareClass {B x : GaussianRat}
    (hB : B ≠ 0) (hx : x ≠ 0) :
    squareClassOf (B / x) (div_ne_zero hB hx) =
      squareClassOf B hB * squareClassOf x hx := by
  rw [← squareClassOf_mul hB hx]
  apply (squareClassOf_eq_iff (div_ne_zero hB hx)
    (mul_ne_zero hB hx)).mpr
  refine ⟨x⁻¹, inv_ne_zero hx, ?_⟩
  field_simp [hx]

/-- The explicit Kummer map respects the affine elliptic-curve group law. -/
theorem alpha_add (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0)
    (P Q : (curve A B).toAffine.Point) :
    alpha A B hB hC (P + Q) =
      alpha A B hB hC P * alpha A B hB hC Q := by
  rcases P with (_ | ⟨x₁, y₁, h₁⟩)
  · change alpha A B hB hC ((0 : (curve A B).toAffine.Point) + Q) =
      alpha A B hB hC 0 * alpha A B hB hC Q
    rw [zero_add, alpha_zero, one_mul]
  · rcases Q with (_ | ⟨x₂, y₂, h₂⟩)
    · change alpha A B hB hC
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ + 0) =
        alpha A B hB hC
          (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) *
          alpha A B hB hC 0
      rw [add_zero, alpha_zero, mul_one]
    · have heq₁ : y₁ ^ 2 = x₁ * (x₁ ^ 2 + A * x₁ + B) :=
        curve_equation_iff.mp h₁.left
      have heq₂ : y₂ ^ 2 = x₂ * (x₂ ^ 2 + A * x₂ + B) :=
        curve_equation_iff.mp h₂.left
      by_cases hvert :
          x₁ = x₂ ∧ y₁ = (curve A B).toAffine.negY x₂ y₂
      · rcases hvert with ⟨rfl, hvertY⟩
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq rfl hvertY]
        simp only [alpha_zero, alpha]
        by_cases hx : x₁ = 0
        · simp only [hx, ↓reduceDIte]
          exact (squareClass_mul_self _).symm
        · simp only [hx, ↓reduceDIte]
          exact (squareClass_mul_self _).symm
      · by_cases hx₁ : x₁ = 0
        · have hy₁ : y₁ = 0 := by
            rw [hx₁] at heq₁
            have : y₁ ^ 2 = 0 := by simpa using heq₁
            exact sq_eq_zero_iff.mp this
          subst x₁
          subst y₁
          have hx₂ : x₂ ≠ 0 := by
            intro hx₂
            have hy₂ : y₂ = 0 := by
              rw [hx₂] at heq₂
              have : y₂ ^ 2 = 0 := by simpa using heq₂
              exact sq_eq_zero_iff.mp this
            apply hvert
            exact ⟨hx₂.symm, by simp [hy₂, curve]⟩
          have haddX :
              (curve A B).toAffine.addX 0 x₂
                  ((curve A B).toAffine.slope 0 x₂ 0 y₂) = B / x₂ :=
            torsion_addX hx₂ heq₂
          have haddX0 :
              (curve A B).toAffine.addX 0 x₂
                  ((curve A B).toAffine.slope 0 x₂ 0 y₂) ≠ 0 := by
            rw [haddX]
            exact div_ne_zero hB hx₂
          rw [WeierstrassCurve.Affine.Point.add_of_X_ne (Ne.symm hx₂)]
          simp only [alpha, hx₂, haddX0, ↓reduceDIte]
          calc
            squareClassOf
                ((curve A B).toAffine.addX 0 x₂
                  ((curve A B).toAffine.slope 0 x₂ 0 y₂)) haddX0 =
                squareClassOf (B / x₂) (div_ne_zero hB hx₂) :=
              squareClassOf_congr _ _ haddX
            _ = _ := div_squareClass hB hx₂
        · by_cases hx₂ : x₂ = 0
          · have hy₂ : y₂ = 0 := by
              rw [hx₂] at heq₂
              have : y₂ ^ 2 = 0 := by simpa using heq₂
              exact sq_eq_zero_iff.mp this
            subst x₂
            subst y₂
            rw [add_comm, mul_comm]
            have haddX :
                (curve A B).toAffine.addX 0 x₁
                    ((curve A B).toAffine.slope 0 x₁ 0 y₁) = B / x₁ :=
              torsion_addX hx₁ heq₁
            have haddX0 :
                (curve A B).toAffine.addX 0 x₁
                    ((curve A B).toAffine.slope 0 x₁ 0 y₁) ≠ 0 := by
              rw [haddX]
              exact div_ne_zero hB hx₁
            rw [WeierstrassCurve.Affine.Point.add_of_X_ne (Ne.symm hx₁)]
            simp only [alpha, hx₁, haddX0, ↓reduceDIte]
            calc
              squareClassOf
                  ((curve A B).toAffine.addX 0 x₁
                    ((curve A B).toAffine.slope 0 x₁ 0 y₁)) haddX0 =
                  squareClassOf (B / x₁) (div_ne_zero hB hx₁) :=
                squareClassOf_congr _ _ haddX
              _ = _ := div_squareClass hB hx₁
          · let ℓ : GaussianRat :=
              (curve A B).toAffine.slope x₁ x₂ y₁ y₂
            let x₃ : GaussianRat :=
              (curve A B).toAffine.addX x₁ x₂ ℓ
            let s : GaussianRat := y₁ - ℓ * x₁
            have hprod : x₁ * x₂ * x₃ = s ^ 2 := by
              simpa only [ℓ, x₃, s] using
                (curve_addX_product h₁.left h₂.left hvert)
            by_cases hx₃ : x₃ = 0
            · have hs : s = 0 := by
                rw [hx₃, mul_zero] at hprod
                exact sq_eq_zero_iff.mp hprod.symm
              have hinter : y₁ = ℓ * x₁ := by
                dsimp only [s] at hs
                linear_combination hs
              have hadd :
                  ℓ ^ 2 - A - x₁ - x₂ = 0 := by
                simpa only [x₃, curve,
                  WeierstrassCurve.Affine.addX, zero_mul,
                  add_zero] using hx₃
              have hinner :
                  ℓ ^ 2 * x₁ = x₁ ^ 2 + A * x₁ + B := by
                apply (mul_left_cancel₀ hx₁)
                rw [hinter] at heq₁
                linear_combination heq₁
              have hBprod : B = x₁ * x₂ := by
                have hl : ℓ ^ 2 = A + x₁ + x₂ := by
                  linear_combination hadd
                calc
                  B = ℓ ^ 2 * x₁ - x₁ ^ 2 - A * x₁ := by
                    rw [hinner]
                    ring
                  _ = x₁ * x₂ := by rw [hl]; ring
              rw [WeierstrassCurve.Affine.Point.add_some hvert]
              simp only [alpha, hx₁, hx₂, hx₃, x₃, ℓ,
                ↓reduceDIte]
              calc
                squareClassOf B hB =
                    squareClassOf (x₁ * x₂) (mul_ne_zero hx₁ hx₂) :=
                  squareClassOf_congr _ _ hBprod
                _ = _ := squareClassOf_mul hx₁ hx₂
            · have hs : s ≠ 0 := by
                intro hs0
                have hleft : x₁ * x₂ * x₃ ≠ 0 :=
                  mul_ne_zero (mul_ne_zero hx₁ hx₂) hx₃
                apply hleft
                rw [hprod, hs0]
                simp
              let z : GaussianRat := s / (x₁ * x₂)
              have hz : z ≠ 0 :=
                div_ne_zero hs (mul_ne_zero hx₁ hx₂)
              have hxrel : x₃ = (x₁ * x₂) * z ^ 2 := by
                dsimp only [z]
                field_simp [hx₁, hx₂]
                linear_combination hprod
              rw [WeierstrassCurve.Affine.Point.add_some hvert]
              simp only [alpha, hx₁, hx₂, hx₃, x₃, ℓ,
                ↓reduceDIte]
              rw [← squareClassOf_mul hx₁ hx₂]
              exact (squareClassOf_eq_iff hx₃
                (mul_ne_zero hx₁ hx₂)).mpr ⟨z, hz, hxrel⟩

/-- The explicit descent map, as an additive homomorphism into the additive
type tag of the squareclass group. -/
def alphaHom (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0) :
    (curve A B).toAffine.Point →+ Additive SquareClass where
  toFun := alpha A B hB hC
  map_zero' := alpha_zero A B hB hC
  map_add' := alpha_add A B hB hC

@[simp] theorem alphaHom_apply (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0)
    (P : (curve A B).toAffine.Point) :
    alphaHom A B hB hC P = Additive.ofMul (alpha A B hB hC P) := rfl

private theorem dual_dual_coefficient_ne_zero {A B : GaussianRat}
    (hB : B ≠ 0) :
    (-2 * A) ^ 2 - 4 * (A ^ 2 - 4 * B) ≠ 0 := by
  intro h
  have h16 : (16 : GaussianRat) * B = 0 := by
    linear_combination h
  exact hB ((mul_eq_zero.mp h16).resolve_left (by norm_num))

private theorem alphaDual_eq_alpha (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0)
    (P : (dualCurve A B).toAffine.Point) :
    alphaDual A B hB hC P =
      alpha (-2 * A) (A ^ 2 - 4 * B) hC
        (dual_dual_coefficient_ne_zero hB) P := by
  rcases P with (_ | ⟨X, Y, h⟩)
  · rfl
  · simp only [alphaDual, alpha]

/-- The dual Kummer map also respects the elliptic-curve group law. -/
theorem alphaDual_add (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0)
    (P Q : (dualCurve A B).toAffine.Point) :
    alphaDual A B hB hC (P + Q) =
      alphaDual A B hB hC P * alphaDual A B hB hC Q := by
  rw [alphaDual_eq_alpha A B hB hC (P + Q),
    alphaDual_eq_alpha A B hB hC P,
    alphaDual_eq_alpha A B hB hC Q]
  exact alpha_add (-2 * A) (A ^ 2 - 4 * B) hC
    (dual_dual_coefficient_ne_zero hB) P Q

/-- The dual descent map, as an additive homomorphism into squareclasses. -/
def alphaDualHom (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0) :
    (dualCurve A B).toAffine.Point →+ Additive SquareClass where
  toFun := alphaDual A B hB hC
  map_zero' := alphaDual_zero A B hB hC
  map_add' := alphaDual_add A B hB hC

@[simp] theorem alphaDualHom_apply (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0)
    (P : (dualCurve A B).toAffine.Point) :
    alphaDualHom A B hB hC P =
      Additive.ofMul (alphaDual A B hB hC P) := rfl

/-- Every point in the image of the dual isogeny has trivial descent
squareclass. -/
theorem alpha_phiHat_eq_one (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0)
    (Q : (dualCurve A B).toAffine.Point) :
    alpha A B hB hC (phiHat A B hB hC Q) = 1 := by
  rcases Q with (_ | ⟨X, Y, h⟩)
  · rfl
  · have hXY : Y ^ 2 =
        X * (X ^ 2 - 2 * A * X + (A ^ 2 - 4 * B)) :=
      dualCurve_equation_iff.mp h.left
    by_cases hX : X = 0
    · simp [phiHat, hX, alpha]
    · by_cases hY : Y = 0
      · subst Y
        have hquad :
            X ^ 2 - 2 * A * X + (A ^ 2 - 4 * B) = 0 := by
          have hprod :
              X * (X ^ 2 - 2 * A * X + (A ^ 2 - 4 * B)) = 0 := by
            simpa using hXY.symm
          exact (mul_eq_zero.mp hprod).resolve_left hX
        have hBsquare : IsSquare B := by
          refine ⟨(X - A) / 2, ?_⟩
          field_simp
          linear_combination -hquad
        simp only [phiHat, hX, ↓reduceDIte, pointOfEquation,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, zero_div,
          alpha, ↓reduceDIte]
        exact (squareClassOf_eq_one_iff hB).mpr hBsquare
      · have hx : Y ^ 2 / (4 * X ^ 2) ≠ 0 :=
          div_ne_zero (pow_ne_zero 2 hY)
            (mul_ne_zero (by norm_num) (pow_ne_zero 2 hX))
        have hxsquare : IsSquare (Y ^ 2 / (4 * X ^ 2)) := by
          refine ⟨Y / (2 * X), ?_⟩
          field_simp [hX]
          ring
        simp only [phiHat, hX, ↓reduceDIte, pointOfEquation, alpha, hx]
        exact (squareClassOf_eq_one_iff hx).mpr hxsquare

/-- Constructive exactness of the two-isogeny descent:
the kernel of `alpha` is precisely the image of the normalized dual map. -/
theorem alpha_eq_one_iff_phiHat_image (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0)
    (P : (curve A B).toAffine.Point) :
    alpha A B hB hC P = 1 ↔
      ∃ Q : (dualCurve A B).toAffine.Point,
        phiHat A B hB hC Q = P := by
  constructor
  · intro hAlpha
    rcases P with (_ | ⟨x, y, h⟩)
    · exact ⟨0, rfl⟩
    · have hxy : y ^ 2 = x * (x ^ 2 + A * x + B) :=
        curve_equation_iff.mp h.left
      by_cases hx : x = 0
      · have hy : y = 0 := by
          rw [hx] at hxy
          have hy2 : y ^ 2 = 0 := by simpa using hxy
          exact sq_eq_zero_iff.mp hy2
        subst x
        subst y
        have hclass : squareClassOf B hB = 1 := by
          simpa only [alpha, ↓reduceDIte] using hAlpha
        rcases (squareClassOf_eq_one_iff hB).mp hclass with ⟨s, hs⟩
        have hs0 : s ≠ 0 := by
          intro hs0
          apply hB
          calc
            B = s * s := hs
            _ = 0 := by simp [hs0]
        let X : GaussianRat := A + 2 * s
        have hX : X ≠ 0 := by
          intro hX0
          apply hC
          calc
            A ^ 2 - 4 * B = (A + 2 * s) * (A - 2 * s) := by
              rw [hs]
              ring
            _ = 0 := by rw [show A + 2 * s = X by rfl, hX0]; simp
        have hQeq :
            (dualCurve A B).toAffine.Equation X 0 := by
          rw [dualCurve_equation_iff]
          rw [hs]
          dsimp [X]
          ring
        let Q : (dualCurve A B).toAffine.Point :=
          pointOfEquation (dualCurve A B)
            (dualCurve_discriminant_ne_zero hB hC) hQeq
        refine ⟨Q, ?_⟩
        simp only [Q, pointOfEquation, phiHat, hX, ↓reduceDIte,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, zero_div]
      · have hclass : squareClassOf x hx = 1 := by
          simpa only [alpha, hx, ↓reduceDIte] using hAlpha
        rcases (squareClassOf_eq_one_iff hx).mp hclass with ⟨z, hz⟩
        have hz0 : z ≠ 0 := by
          intro hz0
          apply hx
          calc
            x = z * z := hz
            _ = 0 := by simp [hz0]
        let X : GaussianRat := A + 2 * x - 2 * y / z
        let Y : GaussianRat := 2 * z * X
        have hprod :
            X * (A + 2 * x + 2 * y / z) = A ^ 2 - 4 * B := by
          dsimp [X]
          rw [hz] at hxy ⊢
          field_simp [hz0]
          linear_combination -4 * hxy
        have hX : X ≠ 0 := by
          intro hX0
          apply hC
          rw [hX0, zero_mul] at hprod
          exact hprod.symm
        have hquad :
            X ^ 2 - 2 * A * X + (A ^ 2 - 4 * B) =
              4 * x * X := by
          rw [← hprod]
          dsimp [X]
          ring
        have hdiff :
            (A ^ 2 - 4 * B) - X ^ 2 = 4 * X * y / z := by
          rw [← hprod]
          dsimp [X]
          field_simp [hz0]
          ring
        have hQeq :
            (dualCurve A B).toAffine.Equation X Y := by
          rw [dualCurve_equation_iff]
          rw [hquad]
          dsimp only [Y]
          rw [hz]
          ring
        let Q : (dualCurve A B).toAffine.Point :=
          pointOfEquation (dualCurve A B)
            (dualCurve_discriminant_ne_zero hB hC) hQeq
        refine ⟨Q, ?_⟩
        simp only [Q, pointOfEquation, phiHat, hX, ↓reduceDIte]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · dsimp only [Y]
          field_simp [hX]
          rw [hz]
          ring
        · dsimp only [Y]
          rw [hdiff]
          field_simp [hX, hz0]
          ring
  · rintro ⟨Q, rfl⟩
    exact alpha_phiHat_eq_one A B hB hC Q

/-- Every point in the image of the forward isogeny has trivial dual
descent squareclass. -/
theorem alphaDual_phi_eq_one (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0)
    (P : (curve A B).toAffine.Point) :
    alphaDual A B hB hC (phi A B hB hC P) = 1 := by
  rcases P with (_ | ⟨x, y, h⟩)
  · rfl
  · have hxy : y ^ 2 = x * (x ^ 2 + A * x + B) :=
      curve_equation_iff.mp h.left
    by_cases hx : x = 0
    · simp [phi, hx, alphaDual]
    · by_cases hy : y = 0
      · subst y
        have hquad : x ^ 2 + A * x + B = 0 := by
          have hprod : x * (x ^ 2 + A * x + B) = 0 := by
            simpa using hxy.symm
          exact (mul_eq_zero.mp hprod).resolve_left hx
        have hCsquare : IsSquare (A ^ 2 - 4 * B) := by
          refine ⟨2 * x + A, ?_⟩
          linear_combination -4 * hquad
        simp only [phi, hx, ↓reduceDIte, pointOfEquation,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, zero_div,
          alphaDual, ↓reduceDIte]
        exact (squareClassOf_eq_one_iff hC).mpr hCsquare
      · have hX : y ^ 2 / x ^ 2 ≠ 0 :=
          div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx)
        have hXsquare : IsSquare (y ^ 2 / x ^ 2) := by
          refine ⟨y / x, ?_⟩
          field_simp [hx]
        simp only [phi, hx, ↓reduceDIte, pointOfEquation, alphaDual, hX]
        exact (squareClassOf_eq_one_iff hX).mpr hXsquare

/-- Constructive exactness on the dual curve:
the kernel of `alphaDual` is precisely the image of the forward map. -/
theorem alphaDual_eq_one_iff_phi_image (A B : GaussianRat) (hB : B ≠ 0)
    (hC : A ^ 2 - 4 * B ≠ 0)
    (Q : (dualCurve A B).toAffine.Point) :
    alphaDual A B hB hC Q = 1 ↔
      ∃ P : (curve A B).toAffine.Point,
        phi A B hB hC P = Q := by
  constructor
  · intro hAlpha
    rcases Q with (_ | ⟨X, Y, h⟩)
    · exact ⟨0, rfl⟩
    · have hXY : Y ^ 2 =
          X * (X ^ 2 - 2 * A * X + (A ^ 2 - 4 * B)) :=
        dualCurve_equation_iff.mp h.left
      by_cases hX : X = 0
      · have hY : Y = 0 := by
          rw [hX] at hXY
          have hY2 : Y ^ 2 = 0 := by simpa using hXY
          exact sq_eq_zero_iff.mp hY2
        subst X
        subst Y
        have hclass : squareClassOf (A ^ 2 - 4 * B) hC = 1 := by
          simpa only [alphaDual, ↓reduceDIte] using hAlpha
        rcases (squareClassOf_eq_one_iff hC).mp hclass with ⟨s, hs⟩
        have hs0 : s ≠ 0 := by
          intro hs0
          apply hC
          calc
            A ^ 2 - 4 * B = s * s := hs
            _ = 0 := by simp [hs0]
        let x : GaussianRat := (s - A) / 2
        have hx : x ≠ 0 := by
          intro hx0
          have hsA : s = A := by
            dsimp [x] at hx0
            field_simp at hx0
            linear_combination hx0
          apply hB
          have hfour : (4 : GaussianRat) * B = 0 := by
            calc
              4 * B = A ^ 2 - (A ^ 2 - 4 * B) := by ring
              _ = A ^ 2 - s * s := by rw [hs]
              _ = 0 := by rw [hsA]; ring
          exact (mul_eq_zero.mp hfour).resolve_left (by norm_num)
        have hroot : x ^ 2 + A * x + B = 0 := by
          dsimp [x]
          field_simp
          linear_combination -hs
        have hPeq : (curve A B).toAffine.Equation x 0 := by
          rw [curve_equation_iff, hroot]
          ring
        let P : (curve A B).toAffine.Point :=
          pointOfEquation (curve A B)
            (curve_discriminant_ne_zero hB hC) hPeq
        refine ⟨P, ?_⟩
        simp only [P, pointOfEquation, phi, hx, ↓reduceDIte,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, zero_div]
      · have hclass : squareClassOf X hX = 1 := by
          simpa only [alphaDual, hX, ↓reduceDIte] using hAlpha
        rcases (squareClassOf_eq_one_iff hX).mp hclass with ⟨z, hz⟩
        have hz0 : z ≠ 0 := by
          intro hz0
          apply hX
          calc
            X = z * z := hz
            _ = 0 := by simp [hz0]
        let x : GaussianRat := (X - A - Y / z) / 2
        let xbar : GaussianRat := (X - A + Y / z) / 2
        let y : GaussianRat := z * x
        have hprod : x * xbar = B := by
          dsimp [x, xbar]
          rw [hz] at hXY ⊢
          field_simp [hz0]
          linear_combination -hXY
        have hx : x ≠ 0 := by
          intro hx0
          apply hB
          rw [hx0, zero_mul] at hprod
          exact hprod.symm
        have hsum : x + xbar = X - A := by
          dsimp [x, xbar]
          field_simp [hz0]
          ring
        have hxbar : xbar = X - A - x := by
          linear_combination hsum
        have hdiff : xbar - x = Y / z := by
          dsimp [x, xbar]
          field_simp [hz0]
          ring
        have hPeq : (curve A B).toAffine.Equation x y := by
          rw [curve_equation_iff]
          dsimp only [y]
          calc
            (z * x) ^ 2 = (z * z) * x ^ 2 := by ring
            _ = X * x ^ 2 := by rw [hz]
            _ = x * (x ^ 2 + A * x + B) := by
              rw [← hprod, hxbar]
              ring
        let P : (curve A B).toAffine.Point :=
          pointOfEquation (curve A B)
            (curve_discriminant_ne_zero hB hC) hPeq
        refine ⟨P, ?_⟩
        simp only [P, pointOfEquation, phi, hx, ↓reduceDIte]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · dsimp only [y]
          field_simp [hx]
          rw [hz]
          ring
        · have hBdiff : B - x ^ 2 = x * (Y / z) := by
            calc
              B - x ^ 2 = x * xbar - x ^ 2 := by rw [hprod]
              _ = x * (xbar - x) := by ring
              _ = x * (Y / z) := by rw [hdiff]
          dsimp only [y]
          rw [hBdiff]
          field_simp [hx, hz0]
  · rintro ⟨P, rfl⟩
    exact alphaDual_phi_eq_one A B hB hC P

/-! ## The four specialized Gaussian curves -/

/-- Coefficients of `E₀`. -/
def E0A : GaussianRat := 2 * gaussianI
def E0B : GaussianRat := -2 - 4 * gaussianI

/-- Coefficients of `E₁`. -/
def E1A : GaussianRat := 2
def E1B : GaussianRat := 2 + 4 * gaussianI

theorem gaussianE0_eq_curve : gaussianE0 = curve E0A E0B := rfl
theorem gaussianE1_eq_curve : gaussianE1 = curve E1A E1B := rfl

/-- The dual of `E₀`: `Y²=X³-4iX²+(4+16i)X`. -/
def gaussianE0Dual : WeierstrassCurve GaussianRat :=
  dualCurve E0A E0B

/-- The dual of `E₁`: `Y²=X³-4X²-(4+16i)X`. -/
def gaussianE1Dual : WeierstrassCurve GaussianRat :=
  dualCurve E1A E1B

theorem E0B_ne_zero : E0B ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  norm_num [E0B] at this

theorem E0C_ne_zero : E0A ^ 2 - 4 * E0B ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  norm_num [E0A, E0B, gaussianI, pow_two] at this

theorem E1B_ne_zero : E1B ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  norm_num [E1B] at this

theorem E1C_ne_zero : E1A ^ 2 - 4 * E1B ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  norm_num [E1A, E1B, gaussianI, pow_two] at this

instance gaussianE0Dual_isElliptic : gaussianE0Dual.IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr
    (dualCurve_discriminant_ne_zero E0B_ne_zero E0C_ne_zero)

instance gaussianE1Dual_isElliptic : gaussianE1Dual.IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr
    (dualCurve_discriminant_ne_zero E1B_ne_zero E1C_ne_zero)

/-- The specialized two-isogeny from `E₀`. -/
def gaussianE0Phi : gaussianE0.toAffine.Point → gaussianE0Dual.toAffine.Point :=
  phi E0A E0B E0B_ne_zero E0C_ne_zero

/-- The specialized dual two-isogeny back to `E₀`. -/
def gaussianE0PhiHat : gaussianE0Dual.toAffine.Point → gaussianE0.toAffine.Point :=
  phiHat E0A E0B E0B_ne_zero E0C_ne_zero

/-- The specialized two-isogeny from `E₁`. -/
def gaussianE1Phi : gaussianE1.toAffine.Point → gaussianE1Dual.toAffine.Point :=
  phi E1A E1B E1B_ne_zero E1C_ne_zero

/-- The specialized dual two-isogeny back to `E₁`. -/
def gaussianE1PhiHat : gaussianE1Dual.toAffine.Point → gaussianE1.toAffine.Point :=
  phiHat E1A E1B E1B_ne_zero E1C_ne_zero

/-! ## Explicit squareclass candidates and visible classes -/

/-- The Gaussian prime `1 + 2i`, of norm five. -/
def gaussianPi : GaussianRat := 1 + 2 * gaussianI

/-- The Gaussian prime `1 + 4i`, of norm seventeen. -/
def gaussianRho : GaussianRat := 1 + 4 * gaussianI

theorem gaussianI_ne_zero : gaussianI ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.im h
  norm_num [gaussianI] at this

theorem gaussianPi_ne_zero : gaussianPi ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  norm_num [gaussianPi] at this

theorem gaussianRho_ne_zero : gaussianRho ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  norm_num [gaussianRho] at this

/-- The squareclass of `i`. -/
def classI : SquareClass :=
  squareClassOf gaussianI gaussianI_ne_zero

/-- The squareclass of `1 + 2i`. -/
def classPi : SquareClass :=
  squareClassOf gaussianPi gaussianPi_ne_zero

/-- The squareclass of `i(1 + 2i)`. -/
def classIPi : SquareClass :=
  squareClassOf (gaussianI * gaussianPi)
    (mul_ne_zero gaussianI_ne_zero gaussianPi_ne_zero)

/-- The squareclass of `1 + 4i`. -/
def classRho : SquareClass :=
  squareClassOf gaussianRho gaussianRho_ne_zero

/-- The squareclass of `i(1 + 4i)`. -/
def classIRho : SquareClass :=
  squareClassOf (gaussianI * gaussianRho)
    (mul_ne_zero gaussianI_ne_zero gaussianRho_ne_zero)

theorem classI_mul_classPi : classI * classPi = classIPi := by
  exact (squareClassOf_mul gaussianI_ne_zero gaussianPi_ne_zero).symm

theorem classI_mul_classRho : classI * classRho = classIRho := by
  exact (squareClassOf_mul gaussianI_ne_zero gaussianRho_ne_zero).symm

private theorem gaussianNorm_isSquare_of_isSquare {z : GaussianRat}
    (hz : IsSquare z) : IsSquare (gaussianNorm z) := by
  rcases hz with ⟨w, rfl⟩
  exact ⟨gaussianNorm w, by rw [gaussianNorm_mul]⟩

theorem gaussianI_not_isSquare : ¬IsSquare gaussianI := by
  rintro ⟨z, hz⟩
  rcases z with ⟨a, b⟩
  have hre := congrArg QuadraticAlgebra.re hz
  have him := congrArg QuadraticAlgebra.im hz
  norm_num [gaussianI, pow_two] at hre him
  have hab : (a - b) * (a + b) = 0 := by nlinarith [hre]
  rcases mul_eq_zero.mp hab with h | h
  · have hab' : a = b := by linarith
    rw [hab'] at him
    have hsquare : IsSquare (2 : ℚ) :=
      ⟨2 * b, by nlinarith [him]⟩
    norm_num [IsSquare] at hsquare
  · have hab' : a = -b := by linarith
    rw [hab'] at him
    nlinarith [sq_nonneg b]

theorem classI_ne_one : classI ≠ 1 :=
  fun h ↦ gaussianI_not_isSquare
    ((squareClassOf_eq_one_iff gaussianI_ne_zero).mp h)

theorem classPi_ne_one : classPi ≠ 1 := by
  intro h
  have hsquare : IsSquare (gaussianNorm gaussianPi) :=
    gaussianNorm_isSquare_of_isSquare
      ((squareClassOf_eq_one_iff gaussianPi_ne_zero).mp h)
  have hnorm : gaussianNorm gaussianPi = 5 := by
    norm_num [gaussianPi, gaussianI, gaussianNorm,
      QuadraticAlgebra.norm_def]
  rw [hnorm] at hsquare
  norm_num [IsSquare] at hsquare

theorem classIPi_ne_one : classIPi ≠ 1 := by
  intro h
  have hsquare :
      IsSquare (gaussianNorm (gaussianI * gaussianPi)) :=
    gaussianNorm_isSquare_of_isSquare
      ((squareClassOf_eq_one_iff
        (mul_ne_zero gaussianI_ne_zero gaussianPi_ne_zero)).mp h)
  have hnorm : gaussianNorm (gaussianI * gaussianPi) = 5 := by
    rw [gaussianNorm_mul]
    norm_num [gaussianPi, gaussianI, gaussianNorm,
      QuadraticAlgebra.norm_def]
  rw [hnorm] at hsquare
  norm_num [IsSquare] at hsquare

theorem classRho_ne_one : classRho ≠ 1 := by
  intro h
  have hsquare : IsSquare (gaussianNorm gaussianRho) :=
    gaussianNorm_isSquare_of_isSquare
      ((squareClassOf_eq_one_iff gaussianRho_ne_zero).mp h)
  have hnorm : gaussianNorm gaussianRho = 17 := by
    norm_num [gaussianRho, gaussianI, gaussianNorm,
      QuadraticAlgebra.norm_def]
  rw [hnorm] at hsquare
  norm_num [IsSquare] at hsquare

theorem classIRho_ne_one : classIRho ≠ 1 := by
  intro h
  have hsquare :
      IsSquare (gaussianNorm (gaussianI * gaussianRho)) :=
    gaussianNorm_isSquare_of_isSquare
      ((squareClassOf_eq_one_iff
        (mul_ne_zero gaussianI_ne_zero gaussianRho_ne_zero)).mp h)
  have hnorm : gaussianNorm (gaussianI * gaussianRho) = 17 := by
    rw [gaussianNorm_mul]
    norm_num [gaussianRho, gaussianI, gaussianNorm,
      QuadraticAlgebra.norm_def]
  rw [hnorm] at hsquare
  norm_num [IsSquare] at hsquare

theorem classI_ne_classPi : classI ≠ classPi := by
  intro h
  apply classIPi_ne_one
  rw [← classI_mul_classPi, ← h, squareClass_mul_self]

theorem classI_ne_classIPi : classI ≠ classIPi := by
  intro h
  apply classPi_ne_one
  apply mul_left_cancel (a := classI)
  rw [classI_mul_classPi, ← h, mul_one]

theorem classPi_ne_classIPi : classPi ≠ classIPi := by
  intro h
  apply classI_ne_one
  apply mul_right_cancel (b := classPi)
  rw [classI_mul_classPi, ← h, one_mul]

theorem classI_ne_classRho : classI ≠ classRho := by
  intro h
  apply classIRho_ne_one
  rw [← classI_mul_classRho, ← h, squareClass_mul_self]

theorem classI_ne_classIRho : classI ≠ classIRho := by
  intro h
  apply classRho_ne_one
  apply mul_left_cancel (a := classI)
  rw [classI_mul_classRho, ← h, mul_one]

theorem classRho_ne_classIRho : classRho ≠ classIRho := by
  intro h
  apply classI_ne_one
  apply mul_right_cancel (b := classRho)
  rw [classI_mul_classRho, ← h, one_mul]

/-- The four squareclasses supported at `1+i` and `1+2i`. -/
def piCandidates : Finset (Additive SquareClass) :=
  by
    classical
    exact {0, Additive.ofMul classI, Additive.ofMul classPi,
      Additive.ofMul classIPi}

/-- The four squareclasses supported at `1+i` and `1+4i`. -/
def rhoCandidates : Finset (Additive SquareClass) :=
  by
    classical
    exact {0, Additive.ofMul classI, Additive.ofMul classRho,
      Additive.ofMul classIRho}

theorem piCandidates_card : piCandidates.card = 4 := by
  classical
  have h0 :
      (0 : Additive SquareClass) ∉
        ({Additive.ofMul classI, Additive.ofMul classPi,
          Additive.ofMul classIPi} : Finset (Additive SquareClass)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨classI_ne_one.symm, classPi_ne_one.symm,
      classIPi_ne_one.symm⟩
  have hI :
      Additive.ofMul classI ∉
        ({Additive.ofMul classPi, Additive.ofMul classIPi} :
          Finset (Additive SquareClass)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨classI_ne_classPi, classI_ne_classIPi⟩
  have hPi :
      Additive.ofMul classPi ∉
        ({Additive.ofMul classIPi} :
          Finset (Additive SquareClass)) := by
    simp only [Finset.mem_singleton]
    change classPi ≠ classIPi
    exact classPi_ne_classIPi
  simp only [piCandidates]
  rw [Finset.card_insert_of_notMem h0,
    Finset.card_insert_of_notMem hI,
    Finset.card_insert_of_notMem hPi]
  simp

theorem rhoCandidates_card : rhoCandidates.card = 4 := by
  classical
  have h0 :
      (0 : Additive SquareClass) ∉
        ({Additive.ofMul classI, Additive.ofMul classRho,
          Additive.ofMul classIRho} :
          Finset (Additive SquareClass)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨classI_ne_one.symm, classRho_ne_one.symm,
      classIRho_ne_one.symm⟩
  have hI :
      Additive.ofMul classI ∉
        ({Additive.ofMul classRho, Additive.ofMul classIRho} :
          Finset (Additive SquareClass)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨classI_ne_classRho, classI_ne_classIRho⟩
  have hRho :
      Additive.ofMul classRho ∉
        ({Additive.ofMul classIRho} :
          Finset (Additive SquareClass)) := by
    simp only [Finset.mem_singleton]
    change classRho ≠ classIRho
    exact classRho_ne_classIRho
  simp only [rhoCandidates]
  rw [Finset.card_insert_of_notMem h0,
    Finset.card_insert_of_notMem hI,
    Finset.card_insert_of_notMem hRho]
  simp

/-- The visible nontorsion point `(2,2)` on `E₀`. -/
def gaussianE0P : (curve E0A E0B).toAffine.Point :=
  pointOfEquation (curve E0A E0B)
    (curve_discriminant_ne_zero E0B_ne_zero E0C_ne_zero)
    (x := 2) (y := 2) (by
      rw [curve_equation_iff]
      ext <;> norm_num [E0A, E0B, gaussianI])

theorem alpha_gaussianE0P :
    alpha E0A E0B E0B_ne_zero E0C_ne_zero gaussianE0P = classI := by
  simp only [gaussianE0P, pointOfEquation, alpha, OfNat.ofNat,
    OfScientific.ofScientific, reduceCtorEq, ↓reduceDIte, classI]
  apply (squareClassOf_eq_iff (by norm_num : (2 : GaussianRat) ≠ 0)
    gaussianI_ne_zero).mpr
  refine ⟨1 - gaussianI, ?_, ?_⟩
  · intro h
    have := congrArg QuadraticAlgebra.re h
    norm_num [gaussianI] at this
  · ext <;> norm_num [gaussianI, pow_two]

theorem alpha_gaussianE0T :
    alpha E0A E0B E0B_ne_zero E0C_ne_zero
      (torsion E0A E0B E0B_ne_zero E0C_ne_zero) = classIPi := by
  simp only [torsion, pointOfEquation, alpha, ↓reduceDIte, classIPi]
  apply (squareClassOf_eq_iff E0B_ne_zero
    (mul_ne_zero gaussianI_ne_zero gaussianPi_ne_zero)).mpr
  refine ⟨1 + gaussianI, ?_, ?_⟩
  · intro h
    have := congrArg QuadraticAlgebra.re h
    norm_num [gaussianI] at this
  · ext <;> norm_num [E0B, gaussianPi, gaussianI, pow_two]

theorem alpha_gaussianE0P_add_T :
    alpha E0A E0B E0B_ne_zero E0C_ne_zero
      (gaussianE0P +
        torsion E0A E0B E0B_ne_zero E0C_ne_zero) = classPi := by
  rw [alpha_add, alpha_gaussianE0P, alpha_gaussianE0T,
    ← classI_mul_classPi]
  rw [← mul_assoc, squareClass_mul_self, one_mul]

theorem alpha_gaussianE1T :
    alpha E1A E1B E1B_ne_zero E1C_ne_zero
      (torsion E1A E1B E1B_ne_zero E1C_ne_zero) = classIPi := by
  simp only [torsion, pointOfEquation, alpha, ↓reduceDIte, classIPi]
  apply (squareClassOf_eq_iff E1B_ne_zero
    (mul_ne_zero gaussianI_ne_zero gaussianPi_ne_zero)).mpr
  refine ⟨1 - gaussianI, ?_, ?_⟩
  · intro h
    have := congrArg QuadraticAlgebra.re h
    norm_num [gaussianI] at this
  · ext <;> norm_num [E1B, gaussianPi, gaussianI, pow_two]

theorem alphaDual_gaussianE0T :
    alphaDual E0A E0B E0B_ne_zero E0C_ne_zero
      (dualTorsion E0A E0B E0B_ne_zero E0C_ne_zero) = classRho := by
  simp only [dualTorsion, pointOfEquation, alphaDual, ↓reduceDIte,
    classRho]
  apply (squareClassOf_eq_iff E0C_ne_zero gaussianRho_ne_zero).mpr
  refine ⟨2, by norm_num, ?_⟩
  ext <;> norm_num [E0A, E0B, gaussianRho, gaussianI, pow_two]

theorem alphaDual_gaussianE1T :
    alphaDual E1A E1B E1B_ne_zero E1C_ne_zero
      (dualTorsion E1A E1B E1B_ne_zero E1C_ne_zero) = classRho := by
  simp only [dualTorsion, pointOfEquation, alphaDual, ↓reduceDIte,
    classRho]
  apply (squareClassOf_eq_iff E1C_ne_zero gaussianRho_ne_zero).mpr
  refine ⟨2 * gaussianI, mul_ne_zero (by norm_num) gaussianI_ne_zero,
    ?_⟩
  ext <;> norm_num [E1A, E1B, gaussianRho, gaussianI, pow_two]

end GaussianDescent

end

end Cuboid2
