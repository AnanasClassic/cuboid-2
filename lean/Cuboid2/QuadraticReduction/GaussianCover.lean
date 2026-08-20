import Cuboid2.DPlus.GlobalBridge
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The Gaussian elliptic covering of the octic curve

This file contains the exact characteristic-zero algebra in the alternative
elliptic-Chabauty proof of the rational points on

`r² = 4u⁸ - 8u² + 5`.

The quadratic field is represented by `QuadraticAlgebra ℚ (-1) 0`, so its
field structure and its two rational coordinates are genuine Mathlib objects.
No global rank or local analytic conclusion is asserted here.
-/

namespace Cuboid2

noncomputable section

open scoped QuadraticAlgebra

/-- The quadratic field `ℚ(i)`, in the basis `1,i`. -/
abbrev GaussianRat := QuadraticAlgebra ℚ (-1) 0

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

/-- The distinguished square root of `-1` in `GaussianRat`. -/
def gaussianI : GaussianRat := QuadraticAlgebra.omega

@[simp] theorem gaussianI_re : gaussianI.re = 0 := rfl

@[simp] theorem gaussianI_im : gaussianI.im = 1 := rfl

@[simp] theorem gaussianI_sq : gaussianI ^ 2 = -1 := by
  ext <;> norm_num [gaussianI, pow_two]

/-- The standard embedding of `ℚ` into `ℚ(i)`. -/
def gaussianOfRat (x : ℚ) : GaussianRat := algebraMap ℚ GaussianRat x

@[simp] theorem gaussianOfRat_re (x : ℚ) : (gaussianOfRat x).re = x := rfl

@[simp] theorem gaussianOfRat_im (x : ℚ) : (gaussianOfRat x).im = 0 := rfl

@[simp] theorem gaussianOfRat_pow (x : ℚ) (n : ℕ) :
    gaussianOfRat x ^ n = gaussianOfRat (x ^ n) :=
  (map_pow (algebraMap ℚ GaussianRat) x n).symm

@[simp] theorem gaussianOfRat_injective :
    Function.Injective gaussianOfRat :=
  (algebraMap ℚ GaussianRat).injective

/-- Conjugation on `ℚ(i)`. -/
def gaussianConj (z : GaussianRat) : GaussianRat := star z

@[simp] theorem gaussianConj_re (z : GaussianRat) :
    (gaussianConj z).re = z.re := by
  simp [gaussianConj]

@[simp] theorem gaussianConj_im (z : GaussianRat) :
    (gaussianConj z).im = -z.im := by
  simp [gaussianConj]

/-- The rational norm `a²+b²` on `ℚ(i)`. -/
def gaussianNorm (z : GaussianRat) : ℚ :=
  QuadraticAlgebra.norm z

@[simp] theorem gaussianNorm_mk (a b : ℚ) :
    gaussianNorm (⟨a, b⟩ : GaussianRat) = a ^ 2 + b ^ 2 := by
  simp [gaussianNorm, QuadraticAlgebra.norm_def]
  ring

@[simp] theorem gaussianNorm_mul (z w : GaussianRat) :
    gaussianNorm (z * w) = gaussianNorm z * gaussianNorm w :=
  map_mul _ _ _

@[simp] theorem gaussianNorm_conj (z : GaussianRat) :
    gaussianNorm (gaussianConj z) = gaussianNorm z := by
  simp [gaussianNorm, gaussianConj]

theorem gaussian_mul_conj (z : GaussianRat) :
    z * gaussianConj z = gaussianOfRat (gaussianNorm z) := by
  ext <;> simp [gaussianConj, gaussianNorm, gaussianOfRat,
    QuadraticAlgebra.norm_def] <;> ring

/-- The first Gaussian quartic factor of the octic polynomial. -/
def gaussianQuartic (u : ℚ) : GaussianRat :=
  gaussianOfRat (2 * u ^ 4 - 1) + gaussianI * gaussianOfRat (2 * u ^ 2 - 2)

@[simp] theorem gaussianQuartic_re (u : ℚ) :
    (gaussianQuartic u).re = 2 * u ^ 4 - 1 := by
  simp only [gaussianQuartic, QuadraticAlgebra.re_add,
    QuadraticAlgebra.re_mul, gaussianOfRat_re, gaussianOfRat_im,
    gaussianI_re, gaussianI_im]
  ring

@[simp] theorem gaussianQuartic_im (u : ℚ) :
    (gaussianQuartic u).im = 2 * u ^ 2 - 2 := by
  simp only [gaussianQuartic, QuadraticAlgebra.im_add,
    QuadraticAlgebra.im_mul, gaussianOfRat_re, gaussianOfRat_im,
    gaussianI_re, gaussianI_im]
  ring

/-- The octic right-hand side is the norm of the Gaussian quartic. -/
theorem gaussianQuartic_norm (u : ℚ) :
    gaussianNorm (gaussianQuartic u) = octicRhs u := by
  rw [show gaussianQuartic u =
      (⟨2 * u ^ 4 - 1, 2 * u ^ 2 - 2⟩ : GaussianRat) by
    ext <;> simp]
  rw [gaussianNorm_mk]
  simp only [octicRhs]
  ring

/-- Multiplication of the two conjugate quartics gives the octic polynomial. -/
theorem gaussianQuartic_mul_conj (u : ℚ) :
    gaussianQuartic u * gaussianConj (gaussianQuartic u) =
      gaussianOfRat (octicRhs u) := by
  rw [gaussian_mul_conj, gaussianQuartic_norm]

/-- The untwisted Gaussian quartic cover `v²=q(u)`. -/
structure GaussianCoverZeroPoint where
  u : ℚ
  v : GaussianRat
  onCurve : v ^ 2 = gaussianQuartic u

/-- The `-i`-twisted Gaussian quartic cover `w²=-i q(u)`. -/
structure GaussianCoverOnePoint where
  u : ℚ
  w : GaussianRat
  onCurve : w ^ 2 = -gaussianI * gaussianQuartic u

/-- The Weierstrass curve
`E₀ : Y² = X³ + 2i X² - (2+4i)X`. -/
def gaussianE0 : WeierstrassCurve GaussianRat where
  a₁ := 0
  a₂ := 2 * gaussianI
  a₃ := 0
  a₄ := -2 - 4 * gaussianI
  a₆ := 0

/-- The Weierstrass curve
`E₁ : Y² = X³ + 2X² + (2+4i)X`. -/
def gaussianE1 : WeierstrassCurve GaussianRat where
  a₁ := 0
  a₂ := 2
  a₃ := 0
  a₄ := 2 + 4 * gaussianI
  a₆ := 0

private theorem gaussianE0_discriminant_ne_zero :
    gaussianE0.Δ ≠ 0 := by
  have hvalue :
      gaussianE0.Δ = (⟨-4864, -2048⟩ : GaussianRat) := by
    native_decide
  rw [hvalue]
  intro h
  have := congrArg QuadraticAlgebra.re h
  norm_num at this

private theorem gaussianE1_discriminant_ne_zero :
    gaussianE1.Δ ≠ 0 := by
  have hvalue :
      gaussianE1.Δ = (⟨4864, 2048⟩ : GaussianRat) := by
    native_decide
  rw [hvalue]
  intro h
  have := congrArg QuadraticAlgebra.re h
  norm_num at this

instance gaussianE0_isElliptic : gaussianE0.IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr gaussianE0_discriminant_ne_zero

instance gaussianE1_isElliptic : gaussianE1.IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr gaussianE1_discriminant_ne_zero

/-- The elliptic quotient map `C₀ → E₀`, `X=2u²`, `Y=2uv`. -/
def GaussianCoverZeroPoint.toE0 (P : GaussianCoverZeroPoint) :
    gaussianE0.toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk
    (x := 2 * gaussianOfRat (P.u ^ 2))
    (y := 2 * gaussianOfRat P.u * P.v) (by
    rw [WeierstrassCurve.Affine.equation_iff]
    dsimp only [gaussianE0]
    simp only [zero_mul, zero_add, add_zero]
    change
      (2 * gaussianOfRat P.u * P.v) ^ 2 =
        (2 * gaussianOfRat (P.u ^ 2)) ^ 3 +
          (2 * gaussianI) * (2 * gaussianOfRat (P.u ^ 2)) ^ 2 +
          (-2 - 4 * gaussianI) * (2 * gaussianOfRat (P.u ^ 2))
    rw [show (2 * gaussianOfRat P.u * P.v) ^ 2 =
        4 * gaussianOfRat (P.u ^ 2) * P.v ^ 2 by
      rw [show gaussianOfRat (P.u ^ 2) = gaussianOfRat P.u ^ 2 by
        simp]
      ring]
    rw [P.onCurve]
    simp only [gaussianQuartic]
    rw [show gaussianOfRat (2 * P.u ^ 4 - 1) =
        2 * gaussianOfRat (P.u ^ 4) - 1 by
      simp [gaussianOfRat]]
    rw [show gaussianOfRat (2 * P.u ^ 2 - 2) =
        2 * gaussianOfRat (P.u ^ 2) - 2 by
      simp [gaussianOfRat]]
    rw [show gaussianOfRat (P.u ^ 4) =
        gaussianOfRat (P.u ^ 2) ^ 2 by
      calc
        gaussianOfRat (P.u ^ 4) = gaussianOfRat ((P.u ^ 2) ^ 2) := by
          congr 1
          ring
        _ = gaussianOfRat (P.u ^ 2) ^ 2 := by
          rw [gaussianOfRat_pow]]
    ring)

/-- The elliptic quotient map `C₁ → E₁`,
`X=-2iu²`, `Y=-2iuw`. -/
def GaussianCoverOnePoint.toE1 (P : GaussianCoverOnePoint) :
    gaussianE1.toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk
    (x := -2 * gaussianI * gaussianOfRat (P.u ^ 2))
    (y := -2 * gaussianI * gaussianOfRat P.u * P.w) (by
    rw [WeierstrassCurve.Affine.equation_iff]
    dsimp only [gaussianE1]
    simp only [zero_mul, zero_add, add_zero]
    change
      (-2 * gaussianI * gaussianOfRat P.u * P.w) ^ 2 =
        (-2 * gaussianI * gaussianOfRat (P.u ^ 2)) ^ 3 +
          2 * (-2 * gaussianI * gaussianOfRat (P.u ^ 2)) ^ 2 +
          (2 + 4 * gaussianI) *
            (-2 * gaussianI * gaussianOfRat (P.u ^ 2))
    rw [show (-2 * gaussianI * gaussianOfRat P.u * P.w) ^ 2 =
        -4 * gaussianOfRat (P.u ^ 2) * P.w ^ 2 by
      rw [show gaussianOfRat (P.u ^ 2) = gaussianOfRat P.u ^ 2 by
        simp]
      calc
        (-2 * gaussianI * gaussianOfRat P.u * P.w) ^ 2 =
            4 * gaussianI ^ 2 * gaussianOfRat P.u ^ 2 * P.w ^ 2 := by ring
        _ = -4 * gaussianOfRat P.u ^ 2 * P.w ^ 2 := by rw [gaussianI_sq]; ring]
    rw [P.onCurve]
    simp only [gaussianQuartic]
    rw [show gaussianOfRat (2 * P.u ^ 4 - 1) =
        2 * gaussianOfRat (P.u ^ 4) - 1 by
      simp [gaussianOfRat]]
    rw [show gaussianOfRat (2 * P.u ^ 2 - 2) =
        2 * gaussianOfRat (P.u ^ 2) - 2 by
      simp [gaussianOfRat]]
    rw [show gaussianOfRat (P.u ^ 4) =
        gaussianOfRat (P.u ^ 2) ^ 2 by
      calc
        gaussianOfRat (P.u ^ 4) = gaussianOfRat ((P.u ^ 2) ^ 2) := by
          congr 1
          ring
        _ = gaussianOfRat (P.u ^ 2) ^ 2 := by
          rw [gaussianOfRat_pow]]
    have hi2 : gaussianI ^ 2 = -1 := gaussianI_sq
    have hi3 : gaussianI ^ 3 = -gaussianI := by
      calc
        gaussianI ^ 3 = gaussianI ^ 2 * gaussianI := by ring
        _ = -gaussianI := by rw [hi2]; ring
    ring_nf at hi2 hi3 ⊢
    rw [hi2, hi3]
    ring)

/-- The known infinite-order point `(2,2)` on `E₀`. -/
def gaussianE0P : gaussianE0.toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (x := 2) (y := 2) (by
    rw [WeierstrassCurve.Affine.equation_iff]
    ext <;> norm_num [gaussianE0, gaussianI, pow_two])

/-- The rational two-torsion point `(0,0)` on `E₀`. -/
def gaussianE0T : gaussianE0.toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (x := 0) (y := 0) (by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [gaussianE0])

/-- The rational two-torsion point `(0,0)` on `E₁`. -/
def gaussianE1T : gaussianE1.toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (x := 0) (y := 0) (by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [gaussianE1])

end

end Cuboid2
