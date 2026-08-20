import Cuboid2.QuadraticReduction.GaussianFormalKernelDisk

/-!
# Torsion in the actual infinity kernel

This file develops the local formal coordinates needed to prove that the
infinity fibre of the specialized `37`-adic two-torsion models has no
torsion.  The coordinates

* `t = -x / y`, and
* `w = -1 / y`

satisfy

`w = t³ + A t² w + B t w²`.

The symmetry `y ↦ -y` makes the associated formal group law odd.  In
particular, its nonlinear error starts in degree three.  This is the key
estimate needed for both prime-to-`37` torsion and `37`-primary torsion.
-/

namespace Cuboid2
namespace GaussianFormalKernelTorsion

noncomputable section

open GaussianProjectiveReduction
open GaussianFormalLocal
open GaussianFormalKernelDisk

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : DecidableEq ℚ_[37] := Classical.decEq _

private abbrev LocalPoint (A B : ℤ_[37]) :=
  (localPadicCurve A B).toAffine.Point

/-- The standard parameter at infinity, extended by zero at the identity. -/
def parameter (A B : ℤ_[37]) : LocalPoint A B → ℚ_[37]
  | .zero => 0
  | .some x y _ => -x / y

/-- The second formal coordinate `w = -1/y`, extended by zero at infinity. -/
def auxiliary (A B : ℤ_[37]) : LocalPoint A B → ℚ_[37]
  | .zero => 0
  | .some _ y _ => -1 / y

@[simp] theorem parameter_zero (A B : ℤ_[37]) :
    parameter A B (0 : LocalPoint A B) = 0 :=
  rfl

@[simp] theorem auxiliary_zero (A B : ℤ_[37]) :
    auxiliary A B (0 : LocalPoint A B) = 0 :=
  rfl

@[simp] theorem parameter_some
    (A B : ℤ_[37]) {x y : ℚ_[37]}
    (h : (localPadicCurve A B).toAffine.Nonsingular x y) :
    parameter A B (.some x y h) = -x / y :=
  rfl

@[simp] theorem auxiliary_some
    (A B : ℤ_[37]) {x y : ℚ_[37]}
    (h : (localPadicCurve A B).toAffine.Nonsingular x y) :
    auxiliary A B (.some x y h) = -1 / y :=
  rfl

/-- The exact formal-curve equation in the `(t,w)` chart at infinity. -/
theorem auxiliary_eq_parameter
    (A B : ℤ_[37]) {x y : ℚ_[37]}
    (hP : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hy : y ≠ 0) :
    (-1 / y : ℚ_[37]) =
      (-x / y) ^ 3 +
        (A : ℚ_[37]) * (-x / y) ^ 2 * (-1 / y) +
        (B : ℚ_[37]) * (-x / y) * (-1 / y) ^ 2 := by
  have hcurve := GaussianFormalLocal.local_curve_equation A B hP
  field_simp [hy]
  linear_combination -hcurve

/-- A nonidentity point in the infinity kernel has nonzero affine
coordinates. -/
theorem affine_coordinates_ne_zero_of_mem_kernel
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hP : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hmem : (.some x y hP : LocalPoint A B) ∈ infinityKernel A B) :
    x ≠ 0 ∧ y ≠ 0 := by
  have hxNorm :=
    norm_x_gt_one_of_finiteReducePoint_eq_none A B hP hmem
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, norm_zero] at hxNorm
    norm_num at hxNorm
  have hySq := norm_y_sq_eq_norm_x_cube A B hP hxNorm
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0, norm_zero, zero_pow (by norm_num)] at hySq
    have hxPos : 0 < ‖x‖ ^ 3 :=
      pow_pos (lt_trans (by norm_num) hxNorm) _
    exact (ne_of_gt hxPos) hySq.symm
  exact ⟨hx, hy⟩

/-- The formal parameter of a nonidentity kernel point lies in the maximal
ideal. -/
theorem norm_parameter_lt_one_of_mem_kernel
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hP : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hmem : (.some x y hP : LocalPoint A B) ∈ infinityKernel A B) :
    ‖parameter A B (.some x y hP)‖ < 1 := by
  rw [parameter_some]
  exact
    GaussianFormalLocal.norm_parameter_lt_one A B hP
      (norm_x_gt_one_of_finiteReducePoint_eq_none A B hP hmem)

/-- On the formal curve, `w` has exactly cubic size in `t`. -/
theorem norm_auxiliary_eq_parameter_cube_of_mem_kernel
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hP : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hmem : (.some x y hP : LocalPoint A B) ∈ infinityKernel A B) :
    ‖auxiliary A B (.some x y hP)‖ =
      ‖parameter A B (.some x y hP)‖ ^ 3 := by
  obtain ⟨hx, hy⟩ :=
    affine_coordinates_ne_zero_of_mem_kernel A B hP hmem
  have hxNorm :=
    norm_x_gt_one_of_finiteReducePoint_eq_none A B hP hmem
  have hySq := norm_y_sq_eq_norm_x_cube A B hP hxNorm
  simp only [auxiliary_some, parameter_some, norm_div, norm_neg,
    norm_one, norm_pow]
  have hxNorm0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hyNorm0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  field_simp [hxNorm0, hyNorm0]
  nlinarith

/-- Negation is exactly odd in the formal parameter. -/
theorem parameter_neg
    (A B : ℤ_[37]) (P : LocalPoint A B) :
    parameter A B (-P) = -parameter A B P := by
  rcases P with (_ | ⟨x, y, hP⟩)
  · rfl
  · rw [WeierstrassCurve.Affine.Point.neg_some]
    simp [parameter, localPadicCurve, localCurve,
      WeierstrassCurve.Affine.negY]
    ring

/-- Negation is exactly odd in the second formal coordinate. -/
theorem auxiliary_neg
    (A B : ℤ_[37]) (P : LocalPoint A B) :
    auxiliary A B (-P) = -auxiliary A B P := by
  rcases P with (_ | ⟨x, y, hP⟩)
  · rfl
  · rw [WeierstrassCurve.Affine.Point.neg_some]
    simp [auxiliary, localPadicCurve, localCurve,
      WeierstrassCurve.Affine.negY]
    ring

/-! ## Exact chord calculation in the formal chart -/

private def chordSlope (t₁ t₂ w₁ w₂ : ℚ_[37]) : ℚ_[37] :=
  (w₂ - w₁) / (t₂ - t₁)

private def chordIntercept (t₁ t₂ w₁ w₂ : ℚ_[37]) : ℚ_[37] :=
  w₁ - t₁ * chordSlope t₁ t₂ w₁ w₂

private def chordError
    (A B t₁ t₂ w₁ w₂ : ℚ_[37]) : ℚ_[37] :=
  let c := chordSlope t₁ t₂ w₁ w₂
  chordIntercept t₁ t₂ w₁ w₂ *
    (A + 2 * B * c) / (1 + A * c + B * c ^ 2)

set_option maxHeartbeats 800000 in
set_option maxRecDepth 10000 in
/-- Algebraic chord calculation once the line is written as `w = c t + h`.
The formal-curve equations are the only geometric input. -/
private theorem chord_parameter_cross_identity
    (A B t₁ t₂ w₁ w₂ c h : ℚ_[37])
    (hline₁ : w₁ = c * t₁ + h)
    (hline₂ : w₂ = c * t₂ + h)
    (h₁ :
      w₁ = t₁ ^ 3 + A * t₁ ^ 2 * w₁ + B * t₁ * w₁ ^ 2)
    (h₂ :
      w₂ = t₂ ^ 3 + A * t₂ ^ 2 * w₂ + B * t₂ * w₂ ^ 2)
    (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) (hh : h ≠ 0)
    (ht : t₂ - t₁ ≠ 0) :
    let x₃ := (c / h) ^ 2 - A - t₁ / w₁ - t₂ / w₂;
    let y₃ := -((c / h) * (x₃ - t₁ / w₁) + (-1 / w₁));
    (-x₃) * (1 + A * c + B * c ^ 2) =
      y₃ *
        ((t₁ + t₂) * (1 + A * c + B * c ^ 2) +
          h * (A + 2 * B * c)) := by
  subst w₁
  subst w₂
  let D := 1 + A * c + B * c ^ 2
  let C₂ := A * h + 2 * B * c * h
  let C₁ := B * h ^ 2 - c
  have hp₁ :
      D * t₁ ^ 3 + C₂ * t₁ ^ 2 + C₁ * t₁ - h = 0 := by
    dsimp [D, C₂, C₁]
    linear_combination -h₁
  have hp₂ :
      D * t₂ ^ 3 + C₂ * t₂ ^ 2 + C₁ * t₂ - h = 0 := by
    dsimp [D, C₂, C₁]
    linear_combination -h₂
  have hfactor :
      (t₂ - t₁) *
        (D * (t₂ ^ 2 + t₂ * t₁ + t₁ ^ 2) +
          C₂ * (t₂ + t₁) + C₁) = 0 := by
    linear_combination hp₂ - hp₁
  have hroot :
      D * (t₂ ^ 2 + t₂ * t₁ + t₁ ^ 2) +
          C₂ * (t₂ + t₁) + C₁ = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left ht
  have hprod :
      t₁ * t₂ * ((t₁ + t₂) * D + C₂) + h = 0 := by
    linear_combination t₁ * hroot - hp₁
  let K :=
    c ^ 2 * (t₁ * t₂) + c * h * (t₁ + t₂) + h ^ 2
  let X :=
    c ^ 2 * K - A * h ^ 2 * K -
      h ^ 2 * (2 * c * (t₁ * t₂) + h * (t₁ + t₂))
  have hK :
      (c * t₁ + h) * (c * t₂ + h) = K := by
    dsimp [K]
    ring
  have hK0 : K ≠ 0 := by
    rw [← hK]
    exact mul_ne_zero hw₁ hw₂
  have hx :
      (c / h) ^ 2 - A -
            t₁ / (c * t₁ + h) - t₂ / (c * t₂ + h) =
        X / (h ^ 2 * K) := by
    dsimp [X]
    field_simp [hw₁, hw₂, hh, hK0]
    dsimp [K]
    ring
  have hcross :
      (-h * X) * D =
        ((t₁ + t₂) * D + C₂) * (h ^ 2 * K - c * X) := by
    dsimp [X, K, D, C₂, C₁]
    dsimp [D, C₂, C₁] at hroot hprod
    linear_combination
      (-A * c ^ 2 * h ^ 3 + c ^ 4 * h - 2 * c * h ^ 3) * hroot +
      (-A * c ^ 3 * h ^ 2 + c ^ 5 - 3 * c ^ 2 * h ^ 2) * hprod
  have hyline (z : ℚ_[37]) :
      -((c / h) * (z - t₁ / (c * t₁ + h)) +
          (-1 / (c * t₁ + h))) =
        (1 - c * z) / h := by
    field_simp [hw₁, hh]
    ring
  dsimp
  rw [hyline, hx]
  field_simp [hh, hK0]
  linear_combination hcross

/-- Divided form of the exact chord calculation. -/
private theorem chord_parameter_identity
    (A B t₁ t₂ w₁ w₂ c h : ℚ_[37])
    (hline₁ : w₁ = c * t₁ + h)
    (hline₂ : w₂ = c * t₂ + h)
    (h₁ :
      w₁ = t₁ ^ 3 + A * t₁ ^ 2 * w₁ + B * t₁ * w₁ ^ 2)
    (h₂ :
      w₂ = t₂ ^ 3 + A * t₂ ^ 2 * w₂ + B * t₂ * w₂ ^ 2)
    (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) (hh : h ≠ 0)
    (ht : t₂ - t₁ ≠ 0)
    (hD : 1 + A * c + B * c ^ 2 ≠ 0)
    (hy :
      -((c / h) *
            (((c / h) ^ 2 - A - t₁ / w₁ - t₂ / w₂) -
              t₁ / w₁) +
          (-1 / w₁)) ≠ 0) :
    let x₃ := (c / h) ^ 2 - A - t₁ / w₁ - t₂ / w₂;
    let y₃ := -((c / h) * (x₃ - t₁ / w₁) + (-1 / w₁));
    -x₃ / y₃ =
      t₁ + t₂ + h * (A + 2 * B * c) /
        (1 + A * c + B * c ^ 2) := by
  dsimp
  have hcross :=
    chord_parameter_cross_identity A B t₁ t₂ w₁ w₂ c h
      hline₁ hline₂ h₁ h₂ hw₁ hw₂ hh ht
  have htarget :
      (t₁ + t₂ +
          h * (A + 2 * B * c) /
            (1 + A * c + B * c ^ 2)) *
          (1 + A * c + B * c ^ 2) =
        (t₁ + t₂) * (1 + A * c + B * c ^ 2) +
          h * (A + 2 * B * c) := by
    field_simp [hD]
  apply (div_eq_iff hy).2
  apply mul_right_cancel₀ hD
  calc
    (-((c / h) ^ 2 - A - t₁ / w₁ - t₂ / w₂)) *
          (1 + A * c + B * c ^ 2) =
        -(c / h * ((c / h) ^ 2 - A - t₁ / w₁ - t₂ / w₂ -
              t₁ / w₁) + -1 / w₁) *
          ((t₁ + t₂) * (1 + A * c + B * c ^ 2) +
            h * (A + 2 * B * c)) := hcross
    _ =
        ((t₁ + t₂ +
              h * (A + 2 * B * c) /
                (1 + A * c + B * c ^ 2)) *
            -(c / h * ((c / h) ^ 2 - A - t₁ / w₁ - t₂ / w₂ -
                t₁ / w₁) + -1 / w₁)) *
          (1 + A * c + B * c ^ 2) := by
      rw [← htarget]
      ring

/-! ## Exact tangent calculation -/

set_option maxHeartbeats 800000 in
set_option maxRecDepth 10000 in
/-- Algebraic tangent calculation once the tangent is written
`w = c t + h`. -/
private theorem tangent_parameter_cross_identity
    (A B t w c h : ℚ_[37])
    (hline : w = c * t + h)
    (hcurve :
      w = t ^ 3 + A * t ^ 2 * w + B * t * w ^ 2)
    (htangent :
      c * (1 - A * t ^ 2 - 2 * B * t * w) =
        3 * t ^ 2 + 2 * A * t * w + B * w ^ 2)
    (hw : w ≠ 0) (hh : h ≠ 0) :
    let x₂ := (c / h) ^ 2 - A - 2 * (t / w);
    let y₂ := -((c / h) * (x₂ - t / w) + (-1 / w));
    (-x₂) * (1 + A * c + B * c ^ 2) =
      y₂ *
        ((2 * t) * (1 + A * c + B * c ^ 2) +
          h * (A + 2 * B * c)) := by
  subst w
  let D := 1 + A * c + B * c ^ 2
  let C₂ := A * h + 2 * B * c * h
  let C₁ := B * h ^ 2 - c
  have hp :
      D * t ^ 3 + C₂ * t ^ 2 + C₁ * t - h = 0 := by
    dsimp [D, C₂, C₁]
    linear_combination -hcurve
  have hderiv :
      3 * D * t ^ 2 + 2 * C₂ * t + C₁ = 0 := by
    dsimp [D, C₂, C₁]
    linear_combination -htangent
  have hprod :
      t ^ 2 * (2 * t * D + C₂) + h = 0 := by
    linear_combination t * hderiv - hp
  let K := (c * t + h) ^ 2
  let X :=
    c ^ 2 * K - A * h ^ 2 * K -
      h ^ 2 * (2 * c * t ^ 2 + h * (2 * t))
  have hK0 : K ≠ 0 := by
    dsimp [K]
    exact pow_ne_zero 2 hw
  have hx :
      (c / h) ^ 2 - A - 2 * (t / (c * t + h)) =
        X / (h ^ 2 * K) := by
    dsimp [X]
    field_simp [hw, hh, hK0]
    dsimp [K]
    ring
  have hcross :
      (-h * X) * D =
        (2 * t * D + C₂) * (h ^ 2 * K - c * X) := by
    dsimp [X, K, D, C₂, C₁]
    dsimp [D, C₂, C₁] at hderiv hprod
    linear_combination
      (-A * c ^ 2 * h ^ 3 + c ^ 4 * h - 2 * c * h ^ 3) * hderiv +
      (-A * c ^ 3 * h ^ 2 + c ^ 5 - 3 * c ^ 2 * h ^ 2) * hprod
  have hyline (z : ℚ_[37]) :
      -((c / h) * (z - t / (c * t + h)) +
          (-1 / (c * t + h))) =
        (1 - c * z) / h := by
    field_simp [hw, hh]
    ring
  dsimp
  rw [hyline, hx]
  field_simp [hh, hK0]
  linear_combination hcross

/-- Divided form of the exact tangent calculation. -/
private theorem tangent_parameter_identity
    (A B t w c h : ℚ_[37])
    (hline : w = c * t + h)
    (hcurve :
      w = t ^ 3 + A * t ^ 2 * w + B * t * w ^ 2)
    (htangent :
      c * (1 - A * t ^ 2 - 2 * B * t * w) =
        3 * t ^ 2 + 2 * A * t * w + B * w ^ 2)
    (hw : w ≠ 0) (hh : h ≠ 0)
    (hD : 1 + A * c + B * c ^ 2 ≠ 0)
    (hy :
      -((c / h) *
            (((c / h) ^ 2 - A - 2 * (t / w)) -
              t / w) +
          (-1 / w)) ≠ 0) :
    let x₂ := (c / h) ^ 2 - A - 2 * (t / w);
    let y₂ := -((c / h) * (x₂ - t / w) + (-1 / w));
    -x₂ / y₂ =
      2 * t + h * (A + 2 * B * c) /
        (1 + A * c + B * c ^ 2) := by
  dsimp
  have hcross :=
    tangent_parameter_cross_identity A B t w c h
      hline hcurve htangent hw hh
  have htarget :
      (2 * t +
          h * (A + 2 * B * c) /
            (1 + A * c + B * c ^ 2)) *
          (1 + A * c + B * c ^ 2) =
        2 * t * (1 + A * c + B * c ^ 2) +
          h * (A + 2 * B * c) := by
    field_simp [hD]
  apply (div_eq_iff hy).2
  apply mul_right_cancel₀ hD
  calc
    (-((c / h) ^ 2 - A - 2 * (t / w))) *
          (1 + A * c + B * c ^ 2) =
        -(c / h * ((c / h) ^ 2 - A - 2 * (t / w) -
              t / w) + -1 / w) *
          (2 * t * (1 + A * c + B * c ^ 2) +
            h * (A + 2 * B * c)) := hcross
    _ =
        ((2 * t +
              h * (A + 2 * B * c) /
                (1 + A * c + B * c ^ 2)) *
            -(c / h * ((c / h) ^ 2 - A - 2 * (t / w) -
                t / w) + -1 / w)) *
          (1 + A * c + B * c ^ 2) := by
      rw [← htarget]
      ring

/-! ## Norm estimates for the chord and tangent tails -/

private theorem norm_one_add_eq_one_of_norm_lt_one
    (z : ℚ_[37]) (hz : ‖z‖ < 1) :
    ‖1 + z‖ = 1 := by
  calc
    ‖1 + z‖ = max ‖(1 : ℚ_[37])‖ ‖z‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (by simpa only [norm_one] using ne_of_gt hz)
    _ = 1 := by rw [norm_one, max_eq_left hz.le]

private theorem norm_one_sub_eq_one_of_norm_lt_one
    (z : ℚ_[37]) (hz : ‖z‖ < 1) :
    ‖1 - z‖ = 1 := by
  rw [sub_eq_add_neg,
    norm_one_add_eq_one_of_norm_lt_one (-z) (by simpa using hz)]

private theorem norm_two_eq_one :
    ‖(2 : ℚ_[37])‖ = 1 :=
  Padic.norm_natCast_eq_one_iff.mpr (by norm_num)

private theorem norm_integral_coe_le_one (z : ℤ_[37]) :
    ‖(z : ℚ_[37])‖ ≤ 1 :=
  z.property

private theorem norm_formal_denominator_eq_one
    (A B c : ℚ_[37])
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hc : ‖c‖ < 1) :
    ‖1 + A * c + B * c ^ 2‖ = 1 := by
  have hAc : ‖A * c‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg A, norm_nonneg c]
  have hBc : ‖B * c ^ 2‖ < 1 := by
    rw [norm_mul, norm_pow]
    have hc0 := norm_nonneg c
    nlinarith
  have hsmall :
      ‖A * c + B * c ^ 2‖ < 1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt hAc hBc)
  simpa only [add_assoc] using
    norm_one_add_eq_one_of_norm_lt_one
      (A * c + B * c ^ 2) hsmall

private theorem norm_linear_tail_le_one
    (A B c : ℚ_[37])
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hc : ‖c‖ ≤ 1) :
    ‖A + 2 * B * c‖ ≤ 1 := by
  have hTwoBc : ‖(2 : ℚ_[37]) * B * c‖ ≤ 1 := by
    rw [norm_mul, norm_mul, norm_two_eq_one, one_mul]
    nlinarith [norm_nonneg B, norm_nonneg c]
  exact
    (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le hA hTwoBc)

/-- The auxiliary coordinate is uniquely determined by a parameter in the
open unit disk. -/
private theorem auxiliary_unique
    (A B t w₁ w₂ : ℚ_[37])
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (ht : ‖t‖ < 1)
    (hw₁ : ‖w₁‖ ≤ ‖t‖ ^ 3)
    (hw₂ : ‖w₂‖ ≤ ‖t‖ ^ 3)
    (h₁ :
      w₁ = t ^ 3 + A * t ^ 2 * w₁ + B * t * w₁ ^ 2)
    (h₂ :
      w₂ = t ^ 3 + A * t ^ 2 * w₂ + B * t * w₂ ^ 2) :
    w₁ = w₂ := by
  let q := A * t ^ 2 + B * t * (w₁ + w₂)
  have hq : ‖q‖ < 1 := by
    have hAt : ‖A * t ^ 2‖ < 1 := by
      rw [norm_mul, norm_pow]
      nlinarith [norm_nonneg A, norm_nonneg t]
    have hwSum :
        ‖w₁ + w₂‖ ≤ ‖t‖ ^ 3 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le hw₁ hw₂)
    have hBt :
        ‖B * t * (w₁ + w₂)‖ < 1 := by
      rw [norm_mul, norm_mul]
      have ht0 := norm_nonneg t
      have hB0 := norm_nonneg B
      calc
        ‖B‖ * ‖t‖ * ‖w₁ + w₂‖ ≤
            1 * ‖t‖ * (‖t‖ ^ 3) := by
          gcongr
        _ = ‖t‖ ^ 4 := by ring
        _ < 1 :=
          pow_lt_one₀ (norm_nonneg t) ht (by norm_num)
    exact
      (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt hAt hBt)
  have hfactor : (1 - q) * (w₁ - w₂) = 0 := by
    dsimp [q]
    linear_combination h₁ - h₂
  have hq0 : 1 - q ≠ 0 := by
    intro hzero
    have : ‖(1 : ℚ_[37])‖ = ‖q‖ := by
      rw [sub_eq_zero.mp hzero]
    rw [norm_one] at this
    linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hq0)

private theorem pow_four_le_sq
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r ^ 4 ≤ r ^ 2 :=
  pow_le_pow_of_le_one hr0 hr1 (by omega)

private theorem pow_six_le_sq
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r ^ 6 ≤ r ^ 2 :=
  pow_le_pow_of_le_one hr0 hr1 (by omega)

/-- The secant slope in the `(t,w)` chart has quadratic size. -/
private theorem norm_chordSlope_le_max_sq
    (A B t₁ t₂ w₁ w₂ : ℚ_[37])
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (ht₁ : ‖t₁‖ < 1) (ht₂ : ‖t₂‖ < 1)
    (hw₁ : ‖w₁‖ ≤ ‖t₁‖ ^ 3)
    (hw₂ : ‖w₂‖ ≤ ‖t₂‖ ^ 3)
    (h₁ :
      w₁ = t₁ ^ 3 + A * t₁ ^ 2 * w₁ + B * t₁ * w₁ ^ 2)
    (h₂ :
      w₂ = t₂ ^ 3 + A * t₂ ^ 2 * w₂ + B * t₂ * w₂ ^ 2)
    (ht : t₂ - t₁ ≠ 0) :
    ‖chordSlope t₁ t₂ w₁ w₂‖ ≤
      max ‖t₁‖ ‖t₂‖ ^ 2 := by
  let M := max ‖t₁‖ ‖t₂‖
  let e := t₂ - t₁
  let n := w₂ - w₁
  let U :=
    1 - A * t₂ ^ 2 - B * t₂ * (w₂ + w₁)
  let V :=
    t₂ ^ 2 + t₂ * t₁ + t₁ ^ 2 +
      A * (t₂ + t₁) * w₁ + B * w₁ ^ 2
  have hM0 : 0 ≤ M :=
    le_trans (norm_nonneg t₁) (le_max_left _ _)
  have hM1 : M < 1 := max_lt ht₁ ht₂
  have ht₁M : ‖t₁‖ ≤ M := le_max_left _ _
  have ht₂M : ‖t₂‖ ≤ M := le_max_right _ _
  have hw₁M : ‖w₁‖ ≤ M ^ 3 := by
    exact hw₁.trans (pow_le_pow_left₀ (norm_nonneg t₁) ht₁M 3)
  have hw₂M : ‖w₂‖ ≤ M ^ 3 := by
    exact hw₂.trans (pow_le_pow_left₀ (norm_nonneg t₂) ht₂M 3)
  have hUSmall :
      ‖A * t₂ ^ 2 + B * t₂ * (w₂ + w₁)‖ < 1 := by
    have hAt : ‖A * t₂ ^ 2‖ < 1 := by
      rw [norm_mul, norm_pow]
      nlinarith [norm_nonneg A, norm_nonneg t₂]
    have hwSum :
        ‖w₂ + w₁‖ ≤ M ^ 3 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le hw₂M hw₁M)
    have hBt : ‖B * t₂ * (w₂ + w₁)‖ < 1 := by
      rw [norm_mul, norm_mul]
      calc
        ‖B‖ * ‖t₂‖ * ‖w₂ + w₁‖ ≤
            1 * M * (M ^ 3) := by gcongr
        _ = M ^ 4 := by ring
        _ < 1 :=
          pow_lt_one₀ hM0 hM1 (by norm_num)
    exact
      (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt hAt hBt)
  have hU : ‖U‖ = 1 := by
    dsimp [U]
    simpa only [sub_sub] using
      norm_one_sub_eq_one_of_norm_lt_one
        (A * t₂ ^ 2 + B * t₂ * (w₂ + w₁)) hUSmall
  have hV : ‖V‖ ≤ M ^ 2 := by
    have ht₂sq : ‖t₂ ^ 2‖ ≤ M ^ 2 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg t₂) ht₂M 2
    have htprod : ‖t₂ * t₁‖ ≤ M ^ 2 := by
      rw [norm_mul]
      nlinarith [norm_nonneg t₁, norm_nonneg t₂]
    have ht₁sq : ‖t₁ ^ 2‖ ≤ M ^ 2 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg t₁) ht₁M 2
    have hpoly :
        ‖t₂ ^ 2 + t₂ * t₁ + t₁ ^ 2‖ ≤ M ^ 2 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans <|
        max_le
          ((IsUltrametricDist.norm_add_le_max _ _).trans
            (max_le ht₂sq htprod))
          ht₁sq
    have htSum : ‖t₂ + t₁‖ ≤ M :=
      (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le ht₂M ht₁M)
    have hAterm :
        ‖A * (t₂ + t₁) * w₁‖ ≤ M ^ 2 := by
      rw [norm_mul, norm_mul]
      calc
        ‖A‖ * ‖t₂ + t₁‖ * ‖w₁‖ ≤
            1 * M * (M ^ 3) := by gcongr
        _ = M ^ 4 := by ring
        _ ≤ M ^ 2 := pow_four_le_sq hM0 hM1.le
    have hBterm :
        ‖B * w₁ ^ 2‖ ≤ M ^ 2 := by
      rw [norm_mul, norm_pow]
      calc
        ‖B‖ * ‖w₁‖ ^ 2 ≤ 1 * (M ^ 3) ^ 2 := by
          gcongr
        _ = M ^ 6 := by ring
        _ ≤ M ^ 2 := pow_six_le_sq hM0 hM1.le
    exact
      (IsUltrametricDist.norm_add_le_max _ _).trans <|
        max_le
          ((IsUltrametricDist.norm_add_le_max _ _).trans
            (max_le hpoly hAterm))
          hBterm
  have hfactor : n * U = e * V := by
    dsimp [n, U, e, V]
    linear_combination h₂ - h₁
  have heNorm0 : ‖e‖ ≠ 0 :=
    norm_ne_zero_iff.mpr ht
  have hnorm : ‖n‖ = ‖e‖ * ‖V‖ := by
    have := congrArg norm hfactor
    simpa only [norm_mul, hU, mul_one] using this
  dsimp [chordSlope, n, e]
  rw [norm_div, hnorm]
  change (‖e‖ * ‖V‖) / ‖e‖ ≤ M ^ 2
  rw [mul_div_cancel_left₀ _ heNorm0]
  exact hV

/-- Consequently the chord intercept has cubic size. -/
private theorem norm_chordIntercept_le_max_cube
    (A B t₁ t₂ w₁ w₂ : ℚ_[37])
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (ht₁ : ‖t₁‖ < 1) (ht₂ : ‖t₂‖ < 1)
    (hw₁ : ‖w₁‖ ≤ ‖t₁‖ ^ 3)
    (hw₂ : ‖w₂‖ ≤ ‖t₂‖ ^ 3)
    (h₁ :
      w₁ = t₁ ^ 3 + A * t₁ ^ 2 * w₁ + B * t₁ * w₁ ^ 2)
    (h₂ :
      w₂ = t₂ ^ 3 + A * t₂ ^ 2 * w₂ + B * t₂ * w₂ ^ 2)
    (ht : t₂ - t₁ ≠ 0) :
    ‖chordIntercept t₁ t₂ w₁ w₂‖ ≤
      max ‖t₁‖ ‖t₂‖ ^ 3 := by
  let M := max ‖t₁‖ ‖t₂‖
  have ht₁M : ‖t₁‖ ≤ M := le_max_left _ _
  have hw₁M : ‖w₁‖ ≤ M ^ 3 :=
    hw₁.trans (pow_le_pow_left₀ (norm_nonneg t₁) ht₁M 3)
  have hc :=
    norm_chordSlope_le_max_sq A B t₁ t₂ w₁ w₂
      hA hB ht₁ ht₂ hw₁ hw₂ h₁ h₂ ht
  have htc :
      ‖t₁ * chordSlope t₁ t₂ w₁ w₂‖ ≤ M ^ 3 := by
    rw [norm_mul]
    calc
      ‖t₁‖ * ‖chordSlope t₁ t₂ w₁ w₂‖ ≤ M * (M ^ 2) := by
        gcongr
      _ = M ^ 3 := by ring
  dsimp [chordIntercept]
  rw [sub_eq_add_neg]
  exact
    (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le hw₁M (by simpa using htc))

/-- The nonlinear chord tail is cubic in the larger input parameter. -/
private theorem norm_chordError_le_max_cube
    (A B t₁ t₂ w₁ w₂ : ℚ_[37])
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (ht₁ : ‖t₁‖ < 1) (ht₂ : ‖t₂‖ < 1)
    (hw₁ : ‖w₁‖ ≤ ‖t₁‖ ^ 3)
    (hw₂ : ‖w₂‖ ≤ ‖t₂‖ ^ 3)
    (h₁ :
      w₁ = t₁ ^ 3 + A * t₁ ^ 2 * w₁ + B * t₁ * w₁ ^ 2)
    (h₂ :
      w₂ = t₂ ^ 3 + A * t₂ ^ 2 * w₂ + B * t₂ * w₂ ^ 2)
    (ht : t₂ - t₁ ≠ 0) :
    ‖chordError A B t₁ t₂ w₁ w₂‖ ≤
      max ‖t₁‖ ‖t₂‖ ^ 3 := by
  let c := chordSlope t₁ t₂ w₁ w₂
  have hc :=
    norm_chordSlope_le_max_sq A B t₁ t₂ w₁ w₂
      hA hB ht₁ ht₂ hw₁ hw₂ h₁ h₂ ht
  have hM1 : max ‖t₁‖ ‖t₂‖ < 1 := max_lt ht₁ ht₂
  have hcLt : ‖c‖ < 1 := by
    have hM0 : 0 ≤ max ‖t₁‖ ‖t₂‖ :=
      le_trans (norm_nonneg t₁) (le_max_left _ _)
    exact lt_of_le_of_lt hc
      (pow_lt_one₀ hM0 hM1 (by norm_num))
  have hD :=
    norm_formal_denominator_eq_one A B c hA hB hcLt
  have htail :=
    norm_linear_tail_le_one A B c hA hB hcLt.le
  have hh :=
    norm_chordIntercept_le_max_cube A B t₁ t₂ w₁ w₂
      hA hB ht₁ ht₂ hw₁ hw₂ h₁ h₂ ht
  dsimp [chordError, c]
  rw [norm_div, norm_mul, hD, div_one]
  exact
    (mul_le_mul_of_nonneg_left htail
      (norm_nonneg (chordIntercept t₁ t₂ w₁ w₂))).trans <|
      by simpa using hh

private def tangentDenominator
    (A B t w : ℚ_[37]) : ℚ_[37] :=
  1 - A * t ^ 2 - 2 * B * t * w

private def tangentSlope
    (A B t w : ℚ_[37]) : ℚ_[37] :=
  (3 * t ^ 2 + 2 * A * t * w + B * w ^ 2) /
    tangentDenominator A B t w

private def tangentIntercept
    (A B t w : ℚ_[37]) : ℚ_[37] :=
  w - t * tangentSlope A B t w

private def tangentError
    (A B t w : ℚ_[37]) : ℚ_[37] :=
  let c := tangentSlope A B t w
  tangentIntercept A B t w *
    (A + 2 * B * c) / (1 + A * c + B * c ^ 2)

private theorem norm_tangentDenominator_eq_one
    (A B t w : ℚ_[37])
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (ht : ‖t‖ < 1) (hw : ‖w‖ ≤ ‖t‖ ^ 3) :
    ‖tangentDenominator A B t w‖ = 1 := by
  have hAt : ‖A * t ^ 2‖ < 1 := by
    rw [norm_mul, norm_pow]
    nlinarith [norm_nonneg A, norm_nonneg t]
  have hBtw : ‖(2 : ℚ_[37]) * B * t * w‖ < 1 := by
    rw [norm_mul, norm_mul, norm_mul, norm_two_eq_one, one_mul]
    calc
      ‖B‖ * ‖t‖ * ‖w‖ ≤ 1 * ‖t‖ * (‖t‖ ^ 3) := by
        gcongr
      _ = ‖t‖ ^ 4 := by ring
      _ < 1 :=
        pow_lt_one₀ (norm_nonneg t) ht (by norm_num)
  have hsmall :
      ‖A * t ^ 2 + 2 * B * t * w‖ < 1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt hAt hBtw)
  dsimp [tangentDenominator]
  simpa only [sub_sub] using
    norm_one_sub_eq_one_of_norm_lt_one
      (A * t ^ 2 + 2 * B * t * w) hsmall

private theorem norm_tangentSlope_le_sq
    (A B t w : ℚ_[37])
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (ht : ‖t‖ < 1) (hw : ‖w‖ ≤ ‖t‖ ^ 3) :
    ‖tangentSlope A B t w‖ ≤ ‖t‖ ^ 2 := by
  have hDen :=
    norm_tangentDenominator_eq_one A B t w hA hB ht hw
  have hThree : ‖(3 : ℚ_[37])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have hFirst : ‖(3 : ℚ_[37]) * t ^ 2‖ ≤ ‖t‖ ^ 2 := by
    rw [norm_mul, norm_pow, hThree, one_mul]
  have hSecond :
      ‖(2 : ℚ_[37]) * A * t * w‖ ≤ ‖t‖ ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, norm_two_eq_one, one_mul]
    calc
      ‖A‖ * ‖t‖ * ‖w‖ ≤ 1 * ‖t‖ * (‖t‖ ^ 3) := by
        gcongr
      _ = ‖t‖ ^ 4 := by ring
      _ ≤ ‖t‖ ^ 2 :=
        pow_four_le_sq (norm_nonneg t) ht.le
  have hThird : ‖B * w ^ 2‖ ≤ ‖t‖ ^ 2 := by
    rw [norm_mul, norm_pow]
    calc
      ‖B‖ * ‖w‖ ^ 2 ≤ 1 * (‖t‖ ^ 3) ^ 2 := by
        gcongr
      _ = ‖t‖ ^ 6 := by ring
      _ ≤ ‖t‖ ^ 2 :=
        pow_six_le_sq (norm_nonneg t) ht.le
  dsimp [tangentSlope]
  rw [norm_div, hDen, div_one]
  exact
    (IsUltrametricDist.norm_add_le_max _ _).trans <|
      max_le
        ((IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le hFirst hSecond))
        hThird

private theorem tangentIntercept_eq
    (A B t w : ℚ_[37])
    (hcurve :
      w = t ^ 3 + A * t ^ 2 * w + B * t * w ^ 2)
    (hDen : tangentDenominator A B t w ≠ 0) :
    tangentIntercept A B t w =
      -(2 : ℚ_[37]) * w / tangentDenominator A B t w := by
  dsimp [tangentIntercept, tangentSlope]
  field_simp [hDen]
  dsimp [tangentDenominator]
  linear_combination 3 * hcurve

private theorem norm_tangentIntercept_le_cube
    (A B t w : ℚ_[37])
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (ht : ‖t‖ < 1) (hw : ‖w‖ ≤ ‖t‖ ^ 3)
    (hcurve :
      w = t ^ 3 + A * t ^ 2 * w + B * t * w ^ 2) :
    ‖tangentIntercept A B t w‖ ≤ ‖t‖ ^ 3 := by
  have hDenNorm :=
    norm_tangentDenominator_eq_one A B t w hA hB ht hw
  have hDen : tangentDenominator A B t w ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hDenNorm]; norm_num)
  rw [tangentIntercept_eq A B t w hcurve hDen,
    norm_div, norm_mul, norm_neg, norm_two_eq_one, one_mul,
    hDenNorm, div_one]
  exact hw

private theorem norm_tangentError_le_cube
    (A B t w : ℚ_[37])
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (ht : ‖t‖ < 1) (hw : ‖w‖ ≤ ‖t‖ ^ 3)
    (hcurve :
      w = t ^ 3 + A * t ^ 2 * w + B * t * w ^ 2) :
    ‖tangentError A B t w‖ ≤ ‖t‖ ^ 3 := by
  let c := tangentSlope A B t w
  have hc := norm_tangentSlope_le_sq A B t w hA hB ht hw
  have hcLt : ‖c‖ < 1 :=
    lt_of_le_of_lt hc
      (pow_lt_one₀ (norm_nonneg t) ht (by norm_num))
  have hD :=
    norm_formal_denominator_eq_one A B c hA hB hcLt
  have htail :=
    norm_linear_tail_le_one A B c hA hB hcLt.le
  have hh :=
    norm_tangentIntercept_le_cube A B t w
      hA hB ht hw hcurve
  dsimp [tangentError, c]
  rw [norm_div, norm_mul, hD, div_one]
  exact
    (mul_le_mul_of_nonneg_left htail
      (norm_nonneg (tangentIntercept A B t w))).trans <|
      by simpa using hh

/-! ## Returning from formal coordinates to actual local points -/

private theorem parameter_div_auxiliary
    {x y : ℚ_[37]} (hy : y ≠ 0) :
    (-x / y) / (-1 / y) = x := by
  field_simp [hy]

private theorem neg_one_div_auxiliary
    {y : ℚ_[37]} (hy : y ≠ 0) :
    -1 / (-1 / y) = y := by
  field_simp [hy]

private theorem secant_slope_eq_chord
    (t₁ t₂ w₁ w₂ c h : ℚ_[37])
    (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) (hh : h ≠ 0)
    (hx : t₁ / w₁ - t₂ / w₂ ≠ 0)
    (hline₁ : w₁ = c * t₁ + h)
    (hline₂ : w₂ = c * t₂ + h) :
    ((-1 / w₁) - (-1 / w₂)) /
        (t₁ / w₁ - t₂ / w₂) =
      c / h := by
  have hcross : w₂ * t₁ - w₁ * t₂ ≠ 0 := by
    intro hcrossZero
    apply hx
    rw [sub_eq_zero]
    apply (div_eq_div_iff hw₁ hw₂).2
    exact sub_eq_zero.mp (by simpa [mul_comm] using hcrossZero)
  have hwdiff : w₁ - w₂ = c * (t₁ - t₂) := by
    linear_combination hline₁ - hline₂
  have hcrossEq :
      w₂ * t₁ - w₁ * t₂ = h * (t₁ - t₂) := by
    linear_combination t₁ * hline₂ - t₂ * hline₁
  field_simp [hw₁, hw₂, hh, hx, hcross]
  linear_combination h * hwdiff - c * hcrossEq

private theorem parameter_ne_zero_of_affine_mem_kernel
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hP : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hmem : (.some x y hP : LocalPoint A B) ∈ infinityKernel A B) :
    parameter A B (.some x y hP) ≠ 0 := by
  obtain ⟨hx, hy⟩ :=
    affine_coordinates_ne_zero_of_mem_kernel A B hP hmem
  simp only [parameter_some]
  exact div_ne_zero (neg_ne_zero.mpr hx) hy

/-- On the actual infinity kernel the formal parameter vanishes only at the
identity. -/
theorem parameter_eq_zero_iff
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : LocalPoint A B)
    (hP : P ∈ infinityKernel A B) :
    parameter A B P = 0 ↔ P = 0 := by
  rcases P with (_ | ⟨x, y, hxy⟩)
  · constructor
    · intro _
      rfl
    · intro _
      exact parameter_zero A B
  · constructor
    · exact fun h =>
        (parameter_ne_zero_of_affine_mem_kernel A B hxy hP h).elim
    · exact fun h => (WeierstrassCurve.Affine.Point.some_ne_zero _ h).elim

private theorem formal_coordinates_determine_point
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x₁ y₁ x₂ y₂ : ℚ_[37]}
    (h₁ : (localPadicCurve A B).toAffine.Nonsingular x₁ y₁)
    (h₂ : (localPadicCurve A B).toAffine.Nonsingular x₂ y₂)
    (hmem₁ : (.some x₁ y₁ h₁ : LocalPoint A B) ∈ infinityKernel A B)
    (hmem₂ : (.some x₂ y₂ h₂ : LocalPoint A B) ∈ infinityKernel A B)
    (ht :
      parameter A B (.some x₁ y₁ h₁) =
        parameter A B (.some x₂ y₂ h₂)) :
    (.some x₁ y₁ h₁ : LocalPoint A B) = .some x₂ y₂ h₂ := by
  obtain ⟨hx₁, hy₁⟩ :=
    affine_coordinates_ne_zero_of_mem_kernel A B h₁ hmem₁
  obtain ⟨hx₂, hy₂⟩ :=
    affine_coordinates_ne_zero_of_mem_kernel A B h₂ hmem₂
  let t := parameter A B (.some x₁ y₁ h₁)
  let w₁ := auxiliary A B (.some x₁ y₁ h₁)
  let w₂ := auxiliary A B (.some x₂ y₂ h₂)
  have htNorm := norm_parameter_lt_one_of_mem_kernel A B h₁ hmem₁
  have hw₁Norm :=
    norm_auxiliary_eq_parameter_cube_of_mem_kernel A B h₁ hmem₁
  have hw₂Norm :=
    norm_auxiliary_eq_parameter_cube_of_mem_kernel A B h₂ hmem₂
  have hformal₁ :
      w₁ = t ^ 3 + (A : ℚ_[37]) * t ^ 2 * w₁ +
        (B : ℚ_[37]) * t * w₁ ^ 2 := by
    dsimp [w₁, t]
    exact auxiliary_eq_parameter A B h₁ hy₁
  have hformal₂ :
      w₂ = t ^ 3 + (A : ℚ_[37]) * t ^ 2 * w₂ +
        (B : ℚ_[37]) * t * w₂ ^ 2 := by
    have hraw := auxiliary_eq_parameter A B h₂ hy₂
    change
      auxiliary A B (.some x₂ y₂ h₂) =
        parameter A B (.some x₂ y₂ h₂) ^ 3 +
          (A : ℚ_[37]) * parameter A B (.some x₂ y₂ h₂) ^ 2 *
            auxiliary A B (.some x₂ y₂ h₂) +
          (B : ℚ_[37]) * parameter A B (.some x₂ y₂ h₂) *
            auxiliary A B (.some x₂ y₂ h₂) ^ 2 at hraw
    change
      auxiliary A B (.some x₂ y₂ h₂) =
        parameter A B (.some x₁ y₁ h₁) ^ 3 +
          (A : ℚ_[37]) * parameter A B (.some x₁ y₁ h₁) ^ 2 *
            auxiliary A B (.some x₂ y₂ h₂) +
          (B : ℚ_[37]) * parameter A B (.some x₁ y₁ h₁) *
            auxiliary A B (.some x₂ y₂ h₂) ^ 2
    simpa only [ht] using hraw
  have hwEq : w₁ = w₂ :=
    auxiliary_unique (A : ℚ_[37]) (B : ℚ_[37]) t w₁ w₂
      A.property B.property htNorm
      (by
        change
          ‖auxiliary A B (.some x₁ y₁ h₁)‖ ≤
            ‖parameter A B (.some x₁ y₁ h₁)‖ ^ 3
        exact hw₁Norm.le)
      (by
        change
          ‖auxiliary A B (.some x₂ y₂ h₂)‖ ≤
            ‖parameter A B (.some x₁ y₁ h₁)‖ ^ 3
        rw [ht]
        exact hw₂Norm.le)
      hformal₁ hformal₂
  change
    auxiliary A B (.some x₁ y₁ h₁) =
      auxiliary A B (.some x₂ y₂ h₂) at hwEq
  have hxEq : x₁ = x₂ := by
    calc
      x₁ =
          parameter A B (.some x₁ y₁ h₁) /
            auxiliary A B (.some x₁ y₁ h₁) :=
        (parameter_div_auxiliary hy₁).symm
      _ =
          parameter A B (.some x₂ y₂ h₂) /
            auxiliary A B (.some x₂ y₂ h₂) := by
        rw [ht, hwEq]
      _ = x₂ := parameter_div_auxiliary hy₂
  have hyEq : y₁ = y₂ := by
    calc
      y₁ = -1 / auxiliary A B (.some x₁ y₁ h₁) :=
        (neg_one_div_auxiliary hy₁).symm
      _ = -1 / auxiliary A B (.some x₂ y₂ h₂) := by rw [hwEq]
      _ = y₂ := neg_one_div_auxiliary hy₂
  subst x₂
  subst y₂
  rfl

/-! ## The actual formal-group estimate -/

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 12000 in
/-- For two affine kernel points with distinct abscissae, the parameter of
their sum is given by the exact chord expression developed above. -/
private theorem parameter_add_eq_chord_of_X_ne
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x₁ y₁ x₂ y₂ : ℚ_[37]}
    (h₁ : (localPadicCurve A B).toAffine.Nonsingular x₁ y₁)
    (h₂ : (localPadicCurve A B).toAffine.Nonsingular x₂ y₂)
    (hmem₁ : (.some x₁ y₁ h₁ : LocalPoint A B) ∈ infinityKernel A B)
    (hmem₂ : (.some x₂ y₂ h₂ : LocalPoint A B) ∈ infinityKernel A B)
    (hx : x₁ ≠ x₂) :
    let t₁ := parameter A B (.some x₁ y₁ h₁)
    let t₂ := parameter A B (.some x₂ y₂ h₂)
    let w₁ := auxiliary A B (.some x₁ y₁ h₁)
    let w₂ := auxiliary A B (.some x₂ y₂ h₂)
    parameter A B
        ((.some x₁ y₁ h₁ : LocalPoint A B) + .some x₂ y₂ h₂) =
      t₁ + t₂ + chordError (A : ℚ_[37]) (B : ℚ_[37]) t₁ t₂ w₁ w₂ := by
  dsimp only
  obtain ⟨_, hy₁⟩ :=
    affine_coordinates_ne_zero_of_mem_kernel A B h₁ hmem₁
  obtain ⟨_, hy₂⟩ :=
    affine_coordinates_ne_zero_of_mem_kernel A B h₂ hmem₂
  let t₁ : ℚ_[37] := -x₁ / y₁
  let t₂ : ℚ_[37] := -x₂ / y₂
  let w₁ : ℚ_[37] := -1 / y₁
  let w₂ : ℚ_[37] := -1 / y₂
  let c := chordSlope t₁ t₂ w₁ w₂
  let h := chordIntercept t₁ t₂ w₁ w₂
  have hw₁ : w₁ ≠ 0 := by
    dsimp [w₁]
    exact div_ne_zero (by norm_num) hy₁
  have hw₂ : w₂ ≠ 0 := by
    dsimp [w₂]
    exact div_ne_zero (by norm_num) hy₂
  have ht₁x : t₁ / w₁ = x₁ := by
    dsimp [t₁, w₁]
    exact parameter_div_auxiliary hy₁
  have ht₂x : t₂ / w₂ = x₂ := by
    dsimp [t₂, w₂]
    exact parameter_div_auxiliary hy₂
  have hw₁y : -1 / w₁ = y₁ := by
    dsimp [w₁]
    exact neg_one_div_auxiliary hy₁
  have hw₂y : -1 / w₂ = y₂ := by
    dsimp [w₂]
    exact neg_one_div_auxiliary hy₂
  have ht : t₂ - t₁ ≠ 0 := by
    intro ht0
    have htEq : t₂ = t₁ := sub_eq_zero.mp ht0
    have hwEq : w₂ = w₁ := by
      have htNorm := norm_parameter_lt_one_of_mem_kernel A B h₁ hmem₁
      have hw₁Norm :=
        norm_auxiliary_eq_parameter_cube_of_mem_kernel A B h₁ hmem₁
      have hw₂Norm :=
        norm_auxiliary_eq_parameter_cube_of_mem_kernel A B h₂ hmem₂
      apply auxiliary_unique (A : ℚ_[37]) (B : ℚ_[37]) t₁ w₂ w₁
          A.property B.property
      · simpa [t₁] using htNorm
      · change ‖w₂‖ ≤ ‖t₁‖ ^ 3
        rw [← htEq]
        simpa [t₂, w₂] using hw₂Norm.le
      · change ‖w₁‖ ≤ ‖t₁‖ ^ 3
        simpa [t₁, w₁] using hw₁Norm.le
      · have hformal := auxiliary_eq_parameter A B h₂ hy₂
        simpa [t₁, t₂, w₂, htEq] using hformal
      · have hformal := auxiliary_eq_parameter A B h₁ hy₁
        simpa [t₁, w₁] using hformal
    apply hx
    calc
      x₁ = t₁ / w₁ := ht₁x.symm
      _ = t₂ / w₂ := by rw [htEq, hwEq]
      _ = x₂ := ht₂x
  have hline₁ : w₁ = c * t₁ + h := by
    dsimp [h, chordIntercept]
    ring
  have hline₂ : w₂ = c * t₂ + h := by
    dsimp [h, c, chordIntercept, chordSlope]
    field_simp [ht]
    ring
  have hformal₁ :
      w₁ = t₁ ^ 3 + (A : ℚ_[37]) * t₁ ^ 2 * w₁ +
        (B : ℚ_[37]) * t₁ * w₁ ^ 2 := by
    simpa [t₁, w₁] using auxiliary_eq_parameter A B h₁ hy₁
  have hformal₂ :
      w₂ = t₂ ^ 3 + (A : ℚ_[37]) * t₂ ^ 2 * w₂ +
        (B : ℚ_[37]) * t₂ * w₂ ^ 2 := by
    simpa [t₂, w₂] using auxiliary_eq_parameter A B h₂ hy₂
  have hh : h ≠ 0 := by
    intro hh0
    have hw₁ct : w₁ = c * t₁ := by simpa [hh0] using hline₁
    have hw₂ct : w₂ = c * t₂ := by simpa [hh0] using hline₂
    have hc : c ≠ 0 := by
      intro hc0
      rw [hc0, zero_mul] at hw₁ct
      exact hw₁ hw₁ct
    have ht₁0 : t₁ ≠ 0 := by
      intro ht₁zero
      rw [ht₁zero, mul_zero] at hw₁ct
      exact hw₁ hw₁ct
    have ht₂0 : t₂ ≠ 0 := by
      intro ht₂zero
      rw [ht₂zero, mul_zero] at hw₂ct
      exact hw₂ hw₂ct
    apply hx
    calc
      x₁ = t₁ / w₁ := ht₁x.symm
      _ = t₁ / (c * t₁) := by rw [hw₁ct]
      _ = c⁻¹ := by
        field_simp [hc, ht₁0]
      _ = t₂ / (c * t₂) := by
        field_simp [hc, ht₂0]
      _ = t₂ / w₂ := by rw [hw₂ct]
      _ = x₂ := ht₂x
  have ht₁Norm :=
    norm_parameter_lt_one_of_mem_kernel A B h₁ hmem₁
  have ht₂Norm :=
    norm_parameter_lt_one_of_mem_kernel A B h₂ hmem₂
  have hw₁Norm :=
    norm_auxiliary_eq_parameter_cube_of_mem_kernel A B h₁ hmem₁
  have hw₂Norm :=
    norm_auxiliary_eq_parameter_cube_of_mem_kernel A B h₂ hmem₂
  have hcNorm :=
    norm_chordSlope_le_max_sq
      (A : ℚ_[37]) (B : ℚ_[37]) t₁ t₂ w₁ w₂
      A.property B.property
      (by simpa [t₁] using ht₁Norm)
      (by simpa [t₂] using ht₂Norm)
      (by simpa [t₁, w₁] using hw₁Norm.le)
      (by simpa [t₂, w₂] using hw₂Norm.le)
      hformal₁ hformal₂ ht
  have hcLt : ‖c‖ < 1 := by
    have hM0 : 0 ≤ max ‖t₁‖ ‖t₂‖ :=
      le_trans (norm_nonneg t₁) (le_max_left _ _)
    exact lt_of_le_of_lt hcNorm
      (pow_lt_one₀ hM0
        (max_lt
          (by simpa [t₁] using ht₁Norm)
          (by simpa [t₂] using ht₂Norm))
        (by norm_num))
  have hDNorm :=
    norm_formal_denominator_eq_one
      (A : ℚ_[37]) (B : ℚ_[37]) c A.property B.property hcLt
  have hD : 1 + (A : ℚ_[37]) * c + (B : ℚ_[37]) * c ^ 2 ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hDNorm]; norm_num)
  let W := (localPadicCurve A B).toAffine
  have hxFormal : t₁ / w₁ - t₂ / w₂ ≠ 0 := by
    rw [ht₁x, ht₂x]
    exact sub_ne_zero.mpr hx
  have hcoordSlope :
      ((-1 / w₁) - (-1 / w₂)) /
          (t₁ / w₁ - t₂ / w₂) =
        c / h := by
    exact
      secant_slope_eq_chord t₁ t₂ w₁ w₂ c h
        hw₁ hw₂ hh hxFormal hline₁ hline₂
  have hslopeRaw :
      (y₁ - y₂) / (x₁ - x₂) = c / h := by
    calc
      (y₁ - y₂) / (x₁ - x₂) =
          ((-1 / w₁) - (-1 / w₂)) /
            (t₁ / w₁ - t₂ / w₂) := by
        rw [hw₁y, hw₂y, ht₁x, ht₂x]
      _ = c / h := hcoordSlope
  have hslope :
      W.slope x₁ x₂ y₁ y₂ = c / h := by
    rw [W.slope_of_X_ne hx]
    exact hslopeRaw
  have hAddX :
      W.addX x₁ x₂ (c / h) =
        (c / h) ^ 2 - (A : ℚ_[37]) - t₁ / w₁ - t₂ / w₂ := by
    dsimp [W, localPadicCurve, localCurve,
      WeierstrassCurve.map, WeierstrassCurve.Affine.addX]
    simp only [map_zero, zero_mul, add_zero, zero_add, sub_zero]
    rw [show PadicInt.Coe.ringHom A = (A : ℚ_[37]) by rfl]
    rw [ht₁x, ht₂x]
  have hAddY :
      W.addY x₁ x₂ y₁ (c / h) =
        -((c / h) *
              (((c / h) ^ 2 - (A : ℚ_[37]) - t₁ / w₁ - t₂ / w₂) -
                t₁ / w₁) +
            (-1 / w₁)) := by
    dsimp [W, localPadicCurve, localCurve,
      WeierstrassCurve.map,
      WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX]
    simp only [map_zero, zero_mul, add_zero, zero_add, sub_zero]
    rw [show PadicInt.Coe.ringHom A = (A : ℚ_[37]) by rfl]
    rw [ht₁x, ht₂x, hw₁y]
  have hsumMem :
      ((.some x₁ y₁ h₁ : LocalPoint A B) + .some x₂ y₂ h₂) ∈
        infinityKernel A B :=
    (infinityKernel A B).add_mem hmem₁ hmem₂
  have hxy :
      ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) :=
    fun hxy => hx hxy.1
  have hySum :
      W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂) ≠ 0 := by
    rw [WeierstrassCurve.Affine.Point.add_some hxy] at hsumMem
    exact
      (affine_coordinates_ne_zero_of_mem_kernel A B
        (W.nonsingular_add h₁ h₂ hxy) hsumMem).2
  have hyIdentity :
      -((c / h) *
            (((c / h) ^ 2 - (A : ℚ_[37]) - t₁ / w₁ - t₂ / w₂) -
              t₁ / w₁) +
          (-1 / w₁)) ≠ 0 := by
    rw [← hAddY]
    simpa only [hslope] using hySum
  rw [WeierstrassCurve.Affine.Point.add_some hxy]
  simp only [parameter_some]
  rw [hslope]
  have hidentity :=
    chord_parameter_identity
      (A : ℚ_[37]) (B : ℚ_[37]) t₁ t₂ w₁ w₂ c h
      hline₁ hline₂ hformal₁ hformal₂ hw₁ hw₂ hh ht hD
      hyIdentity
  rw [hAddX, hAddY]
  simpa [t₁, t₂, w₁, w₂, c, h, chordError, auxiliary] using hidentity

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 12000 in
/-- Exact tangent expression for doubling an affine point in the infinity
kernel. -/
private theorem parameter_two_nsmul_eq_tangent
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hP : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hmem : (.some x y hP : LocalPoint A B) ∈ infinityKernel A B) :
    let t := parameter A B (.some x y hP)
    let w := auxiliary A B (.some x y hP)
    parameter A B (2 • (.some x y hP : LocalPoint A B)) =
      2 * t + tangentError (A : ℚ_[37]) (B : ℚ_[37]) t w := by
  dsimp only
  obtain ⟨_, hy⟩ :=
    affine_coordinates_ne_zero_of_mem_kernel A B hP hmem
  let t : ℚ_[37] := -x / y
  let w : ℚ_[37] := -1 / y
  let c := tangentSlope (A : ℚ_[37]) (B : ℚ_[37]) t w
  let h := tangentIntercept (A : ℚ_[37]) (B : ℚ_[37]) t w
  have hw : w ≠ 0 := by
    dsimp [w]
    exact div_ne_zero (by norm_num) hy
  have htx : t / w = x := by
    dsimp [t, w]
    exact parameter_div_auxiliary hy
  have hwy : -1 / w = y := by
    dsimp [w]
    exact neg_one_div_auxiliary hy
  have htNorm :=
    norm_parameter_lt_one_of_mem_kernel A B hP hmem
  have hwNorm :=
    norm_auxiliary_eq_parameter_cube_of_mem_kernel A B hP hmem
  have hformal :
      w = t ^ 3 + (A : ℚ_[37]) * t ^ 2 * w +
        (B : ℚ_[37]) * t * w ^ 2 := by
    simpa [t, w] using auxiliary_eq_parameter A B hP hy
  have hDenNorm :=
    norm_tangentDenominator_eq_one
      (A : ℚ_[37]) (B : ℚ_[37]) t w
      A.property B.property
      (by simpa [t] using htNorm)
      (by simpa [t, w] using hwNorm.le)
  have hDen :
      tangentDenominator (A : ℚ_[37]) (B : ℚ_[37]) t w ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hDenNorm]; norm_num)
  have hline : w = c * t + h := by
    dsimp [h, tangentIntercept]
    ring
  have htangent :
      c *
          (1 - (A : ℚ_[37]) * t ^ 2 -
            2 * (B : ℚ_[37]) * t * w) =
        3 * t ^ 2 + 2 * (A : ℚ_[37]) * t * w +
          (B : ℚ_[37]) * w ^ 2 := by
    change
      tangentSlope (A : ℚ_[37]) (B : ℚ_[37]) t w *
          tangentDenominator (A : ℚ_[37]) (B : ℚ_[37]) t w =
        3 * t ^ 2 + 2 * (A : ℚ_[37]) * t * w +
          (B : ℚ_[37]) * w ^ 2
    dsimp [tangentSlope]
    exact div_mul_cancel₀ _ hDen
  have hhEq :
      h =
        -(2 : ℚ_[37]) * w /
          tangentDenominator (A : ℚ_[37]) (B : ℚ_[37]) t w :=
    tangentIntercept_eq
      (A : ℚ_[37]) (B : ℚ_[37]) t w hformal hDen
  have hh : h ≠ 0 := by
    rw [hhEq]
    exact
      div_ne_zero
        (mul_ne_zero (by norm_num) hw)
        hDen
  have hcNorm :=
    norm_tangentSlope_le_sq
      (A : ℚ_[37]) (B : ℚ_[37]) t w
      A.property B.property
      (by simpa [t] using htNorm)
      (by simpa [t, w] using hwNorm.le)
  have hcLt : ‖c‖ < 1 :=
    lt_of_le_of_lt hcNorm
      (pow_lt_one₀ (norm_nonneg t)
        (by simpa [t] using htNorm) (by norm_num))
  have hFormalDNorm :=
    norm_formal_denominator_eq_one
      (A : ℚ_[37]) (B : ℚ_[37]) c
      A.property B.property hcLt
  have hFormalD :
      1 + (A : ℚ_[37]) * c + (B : ℚ_[37]) * c ^ 2 ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hFormalDNorm]; norm_num)
  let W := (localPadicCurve A B).toAffine
  have hnegY : W.negY x y = -y := by
    dsimp [W, localPadicCurve, localCurve, WeierstrassCurve.map,
      WeierstrassCurve.Affine.negY]
    simp
  have hyNeg : y ≠ W.negY x y := by
    rw [hnegY]
    intro hyEq
    have hzero : (2 : ℚ_[37]) * y = 0 := by
      linear_combination hyEq
    exact hy ((mul_eq_zero.mp hzero).resolve_left (by norm_num))
  have hslopeRaw :
      (3 * x ^ 2 + 2 * (A : ℚ_[37]) * x + (B : ℚ_[37])) /
          (2 * y) =
        c / h := by
    rw [← htx, ← hwy]
    dsimp [c, tangentSlope]
    rw [hhEq]
    field_simp [hw, hDen]
  have hslope :
      W.slope x x y y = c / h := by
    rw [W.slope_of_Y_ne rfl hyNeg]
    dsimp [W, localPadicCurve, localCurve, WeierstrassCurve.map]
    simp only [map_zero, zero_mul, add_zero, zero_add, sub_zero]
    rw [show PadicInt.Coe.ringHom A = (A : ℚ_[37]) by rfl]
    rw [show PadicInt.Coe.ringHom B = (B : ℚ_[37]) by rfl]
    convert hslopeRaw using 1 <;> ring
  have hAddX :
      W.addX x x (c / h) =
        (c / h) ^ 2 - (A : ℚ_[37]) - 2 * (t / w) := by
    dsimp [W, localPadicCurve, localCurve, WeierstrassCurve.map,
      WeierstrassCurve.Affine.addX]
    simp only [map_zero, zero_mul, add_zero, zero_add, sub_zero]
    rw [show PadicInt.Coe.ringHom A = (A : ℚ_[37]) by rfl]
    rw [htx]
    ring
  have hAddY :
      W.addY x x y (c / h) =
        -((c / h) *
              (((c / h) ^ 2 - (A : ℚ_[37]) - 2 * (t / w)) -
                t / w) +
            (-1 / w)) := by
    dsimp [W, localPadicCurve, localCurve, WeierstrassCurve.map,
      WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX]
    simp only [map_zero, zero_mul, add_zero, zero_add, sub_zero]
    rw [show PadicInt.Coe.ringHom A = (A : ℚ_[37]) by rfl]
    rw [htx, hwy]
    ring
  have hsumMem :
      ((.some x y hP : LocalPoint A B) + .some x y hP) ∈
        infinityKernel A B :=
    (infinityKernel A B).add_mem hmem hmem
  have hySum :
      W.addY x x y (W.slope x x y y) ≠ 0 := by
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyNeg] at hsumMem
    exact
      (affine_coordinates_ne_zero_of_mem_kernel A B
        (W.nonsingular_add hP hP (fun hxy => hyNeg hxy.2)) hsumMem).2
  have hyIdentity :
      -((c / h) *
            (((c / h) ^ 2 - (A : ℚ_[37]) - 2 * (t / w)) -
              t / w) +
          (-1 / w)) ≠ 0 := by
    rw [← hAddY]
    simpa only [hslope] using hySum
  have hidentity :=
    tangent_parameter_identity
      (A : ℚ_[37]) (B : ℚ_[37]) t w c h
      hline hformal htangent hw hh hFormalD hyIdentity
  rw [two_nsmul,
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyNeg]
  simp only [parameter_some, hslope]
  rw [hAddX, hAddY]
  simpa [t, w, c, h, tangentError, auxiliary] using hidentity

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 12000 in
/-- The actual formal parameter is additive up to a cubic error throughout
the infinity kernel. -/
theorem norm_parameter_add_sub_le_max_cube
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P Q : LocalPoint A B)
    (hP : P ∈ infinityKernel A B)
    (hQ : Q ∈ infinityKernel A B) :
    ‖parameter A B (P + Q) - parameter A B P - parameter A B Q‖ ≤
      max ‖parameter A B P‖ ‖parameter A B Q‖ ^ 3 := by
  rcases P with (_ | ⟨x₁, y₁, h₁⟩)
  · rw [show
      (WeierstrassCurve.Affine.Point.zero : LocalPoint A B) + Q = Q by
        rfl,
      show
        parameter A B
            (WeierstrassCurve.Affine.Point.zero : LocalPoint A B) = 0 by
        rfl]
    simp
  rcases Q with (_ | ⟨x₂, y₂, h₂⟩)
  · rw [show
      (.some x₁ y₁ h₁ : LocalPoint A B) +
          WeierstrassCurve.Affine.Point.zero =
        .some x₁ y₁ h₁ by rfl,
      show
        parameter A B
            (WeierstrassCurve.Affine.Point.zero : LocalPoint A B) = 0 by
        rfl]
    simp
  let P : LocalPoint A B := .some x₁ y₁ h₁
  let Q : LocalPoint A B := .some x₂ y₂ h₂
  let t₁ := parameter A B P
  let t₂ := parameter A B Q
  let w₁ := auxiliary A B P
  let w₂ := auxiliary A B Q
  let W := (localPadicCurve A B).toAffine
  change
    ‖parameter A B (P + Q) - t₁ - t₂‖ ≤
      max ‖t₁‖ ‖t₂‖ ^ 3
  by_cases hinv : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
  · have hsum : P + Q = 0 :=
      WeierstrassCurve.Affine.Point.add_of_Y_eq hinv.1 hinv.2
    have hQneg : Q = -P := by
      exact eq_neg_of_add_eq_zero_right hsum
    have htNeg : t₂ = -t₁ := by
      calc
        t₂ = parameter A B Q := rfl
        _ = parameter A B (-P) := by rw [hQneg]
        _ = -parameter A B P := parameter_neg A B P
        _ = -t₁ := rfl
    rw [hsum, parameter_zero, htNeg]
    simp
  · by_cases htEq : t₁ = t₂
    · have hPointEq : P = Q := by
        exact
          formal_coordinates_determine_point A B h₁ h₂ hP hQ htEq
      have htNorm :=
        norm_parameter_lt_one_of_mem_kernel A B h₁ hP
      have hwNorm :=
        norm_auxiliary_eq_parameter_cube_of_mem_kernel A B h₁ hP
      have hformal :
          w₁ = t₁ ^ 3 + (A : ℚ_[37]) * t₁ ^ 2 * w₁ +
            (B : ℚ_[37]) * t₁ * w₁ ^ 2 := by
        obtain ⟨_, hy₁⟩ :=
          affine_coordinates_ne_zero_of_mem_kernel A B h₁ hP
        simpa [P, t₁, w₁] using auxiliary_eq_parameter A B h₁ hy₁
      have htail :=
        norm_tangentError_le_cube
          (A : ℚ_[37]) (B : ℚ_[37]) t₁ w₁
          A.property B.property
          (by simpa [P, t₁] using htNorm)
          (by simpa [P, t₁, w₁] using hwNorm.le)
          hformal
      have htwo :=
        parameter_two_nsmul_eq_tangent A B h₁ hP
      have htwo' :
          parameter A B (2 • P) =
            2 * t₁ +
              tangentError (A : ℚ_[37]) (B : ℚ_[37]) t₁ w₁ := by
        simpa [P, t₁, w₁] using htwo
      rw [← hPointEq, ← two_nsmul, htwo', ← htEq]
      change
        ‖2 * t₁ +
              tangentError (A : ℚ_[37]) (B : ℚ_[37]) t₁ w₁ -
            t₁ - t₁‖ ≤
          max ‖t₁‖ ‖t₁‖ ^ 3
      rw [show
        2 * t₁ +
              tangentError (A : ℚ_[37]) (B : ℚ_[37]) t₁ w₁ -
            t₁ - t₁ =
          tangentError (A : ℚ_[37]) (B : ℚ_[37]) t₁ w₁ by ring,
        max_self]
      exact htail
    · have hx : x₁ ≠ x₂ := by
        intro hxEq
        rcases W.Y_eq_of_X_eq h₁.left h₂.left hxEq with hyEq | hyInv
        · apply htEq
          subst x₂
          subst y₂
          rfl
        · exact hinv ⟨hxEq, hyInv⟩
      have hchord :=
        parameter_add_eq_chord_of_X_ne A B h₁ h₂ hP hQ hx
      obtain ⟨_, hy₁⟩ :=
        affine_coordinates_ne_zero_of_mem_kernel A B h₁ hP
      obtain ⟨_, hy₂⟩ :=
        affine_coordinates_ne_zero_of_mem_kernel A B h₂ hQ
      have ht₁Norm :=
        norm_parameter_lt_one_of_mem_kernel A B h₁ hP
      have ht₂Norm :=
        norm_parameter_lt_one_of_mem_kernel A B h₂ hQ
      have hw₁Norm :=
        norm_auxiliary_eq_parameter_cube_of_mem_kernel A B h₁ hP
      have hw₂Norm :=
        norm_auxiliary_eq_parameter_cube_of_mem_kernel A B h₂ hQ
      have hformal₁ :
          w₁ = t₁ ^ 3 + (A : ℚ_[37]) * t₁ ^ 2 * w₁ +
            (B : ℚ_[37]) * t₁ * w₁ ^ 2 := by
        simpa [P, t₁, w₁] using auxiliary_eq_parameter A B h₁ hy₁
      have hformal₂ :
          w₂ = t₂ ^ 3 + (A : ℚ_[37]) * t₂ ^ 2 * w₂ +
            (B : ℚ_[37]) * t₂ * w₂ ^ 2 := by
        simpa [Q, t₂, w₂] using auxiliary_eq_parameter A B h₂ hy₂
      have ht : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm htEq)
      have htail :=
        norm_chordError_le_max_cube
          (A : ℚ_[37]) (B : ℚ_[37]) t₁ t₂ w₁ w₂
          A.property B.property
          (by simpa [P, t₁] using ht₁Norm)
          (by simpa [Q, t₂] using ht₂Norm)
          (by simpa [P, t₁, w₁] using hw₁Norm.le)
          (by simpa [Q, t₂, w₂] using hw₂Norm.le)
          hformal₁ hformal₂ ht
      rw [hchord]
      change
        ‖t₁ + t₂ +
              chordError (A : ℚ_[37]) (B : ℚ_[37]) t₁ t₂ w₁ w₂ -
            t₁ - t₂‖ ≤
          max ‖t₁‖ ‖t₂‖ ^ 3
      convert htail using 1 <;> ring

/-- Every point of the actual infinity kernel has parameter in the open
unit disk, including the identity. -/
theorem norm_parameter_lt_one_of_mem_kernel_point
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : LocalPoint A B)
    (hP : P ∈ infinityKernel A B) :
    ‖parameter A B P‖ < 1 := by
  rcases P with (_ | ⟨x, y, hxy⟩)
  · simp [parameter]
  · exact norm_parameter_lt_one_of_mem_kernel A B hxy hP

private theorem norm_parameter_nsmul_estimates
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : LocalPoint A B)
    (hP : P ∈ infinityKernel A B) :
    ∀ n : ℕ,
      ‖parameter A B (n • P) -
          (n : ℚ_[37]) * parameter A B P‖ ≤
          ‖parameter A B P‖ ^ 3 ∧
        ‖parameter A B (n • P)‖ ≤ ‖parameter A B P‖ := by
  let t := parameter A B P
  have ht : ‖t‖ < 1 := by
    simpa [t] using norm_parameter_lt_one_of_mem_kernel_point A B P hP
  have htCube : ‖t‖ ^ 3 ≤ ‖t‖ := by
    have ht0 := norm_nonneg t
    nlinarith [mul_self_nonneg ‖t‖]
  intro n
  induction n with
  | zero =>
      change ‖parameter A B (0 • P) - (0 : ℚ_[37]) * t‖ ≤ ‖t‖ ^ 3 ∧
        ‖parameter A B (0 • P)‖ ≤ ‖t‖
      simp [parameter]
  | succ n ih =>
      have hnMem : n • P ∈ infinityKernel A B :=
        (infinityKernel A B).nsmul_mem hP n
      have hadd :=
        norm_parameter_add_sub_le_max_cube
          A B (n • P) P hnMem hP
      have hadd' :
          ‖parameter A B (n • P + P) -
              parameter A B (n • P) - t‖ ≤ ‖t‖ ^ 3 := by
        exact hadd.trans <| by
          apply pow_le_pow_left₀
            (le_trans (norm_nonneg _) (le_max_left _ _))
          exact max_le ih.2 le_rfl
      have herror :
          ‖parameter A B ((n + 1) • P) -
              ((n + 1 : ℕ) : ℚ_[37]) * t‖ ≤ ‖t‖ ^ 3 := by
        have hdecomp :
            parameter A B ((n + 1) • P) -
                ((n + 1 : ℕ) : ℚ_[37]) * t =
              (parameter A B (n • P + P) -
                  parameter A B (n • P) - t) +
                (parameter A B (n • P) - (n : ℚ_[37]) * t) := by
          rw [add_nsmul, one_nsmul]
          push_cast
          ring
        rw [hdecomp]
        exact
          (IsUltrametricDist.norm_add_le_max _ _).trans
            (max_le hadd' ih.1)
      have hcast :
          ‖(((n + 1 : ℕ) : ℚ_[37]))‖ ≤ 1 :=
        IsUltrametricDist.norm_natCast_le_one ℚ_[37] (n + 1)
      have hlinear :
          ‖(((n + 1 : ℕ) : ℚ_[37]) * t)‖ ≤ ‖t‖ := by
        rw [norm_mul]
        nlinarith [norm_nonneg t]
      have hnorm :
          ‖parameter A B ((n + 1) • P)‖ ≤ ‖t‖ := by
        have hrecompose :
            parameter A B ((n + 1) • P) =
              ((n + 1 : ℕ) : ℚ_[37]) * t +
                (parameter A B ((n + 1) • P) -
                  ((n + 1 : ℕ) : ℚ_[37]) * t) := by
          ring
        rw [hrecompose]
        exact
          (IsUltrametricDist.norm_add_le_max _ _).trans
            (max_le hlinear (herror.trans htCube))
      exact ⟨herror, hnorm⟩

/-- Uniform cubic approximation for multiplication by a natural number on
the actual infinity kernel. -/
theorem norm_parameter_nsmul_sub_le_cube
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : LocalPoint A B)
    (hP : P ∈ infinityKernel A B)
    (n : ℕ) :
    ‖parameter A B (n • P) -
        (n : ℚ_[37]) * parameter A B P‖ ≤
      ‖parameter A B P‖ ^ 3 :=
  (norm_parameter_nsmul_estimates A B P hP n).1

/-- Signed version of the uniform cubic multiplication estimate. -/
theorem norm_parameter_zsmul_sub_le_cube
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : LocalPoint A B)
    (hP : P ∈ infinityKernel A B)
    (z : ℤ) :
    ‖parameter A B (z • P) -
        (z : ℚ_[37]) * parameter A B P‖ ≤
      ‖parameter A B P‖ ^ 3 := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simpa using norm_parameter_nsmul_sub_le_cube A B P hP n
  · have h :=
      norm_parameter_nsmul_sub_le_cube A B P hP n
    rw [neg_zsmul, natCast_zsmul, parameter_neg,
      Int.cast_neg, Int.cast_natCast, neg_mul]
    have heq :
        -parameter A B (n • P) -
            -((n : ℚ_[37]) * parameter A B P) =
          -(parameter A B (n • P) -
            (n : ℚ_[37]) * parameter A B P) := by
      ring
    rw [heq, norm_neg]
    exact h

/-- Multiplication does not increase the norm of the formal parameter. -/
theorem norm_parameter_nsmul_le
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : LocalPoint A B)
    (hP : P ∈ infinityKernel A B)
    (n : ℕ) :
    ‖parameter A B (n • P)‖ ≤ ‖parameter A B P‖ :=
  (norm_parameter_nsmul_estimates A B P hP n).2

private theorem norm_37_padic :
    ‖(37 : ℚ_[37])‖ = (37 : ℝ)⁻¹ := by
  simpa using (Padic.norm_p (p := 37))

private theorem norm_37_padicInt :
    ‖((37 : ℕ) : ℤ_[37])‖ = (37 : ℝ)⁻¹ := by
  simpa using (PadicInt.norm_p (p := 37))

/-- A `37`-adic number in the open unit disk has norm at most `37⁻¹`. -/
theorem norm_le_inv_37_of_lt_one
    (z : ℚ_[37]) (hz : ‖z‖ < 1) :
    ‖z‖ ≤ (37 : ℝ)⁻¹ := by
  let zInt : ℤ_[37] := ⟨z, hz.le⟩
  have hzInt : ‖zInt‖ < 1 := by
    simpa [zInt] using hz
  obtain ⟨q, hq⟩ :=
    (PadicInt.norm_lt_one_iff_dvd zInt).mp hzInt
  calc
    ‖z‖ = ‖zInt‖ := rfl
    _ = ‖((37 : ℕ) : ℤ_[37]) * q‖ := by rw [hq]
    _ = ‖((37 : ℕ) : ℤ_[37])‖ * ‖q‖ := norm_mul _ _
    _ ≤ (37 : ℝ)⁻¹ * 1 := by
      rw [norm_37_padicInt]
      exact
        mul_le_mul_of_nonneg_left q.property (by positivity)
    _ = (37 : ℝ)⁻¹ := mul_one _

/-- Multiplication by an integer prime to `37` preserves the norm of the
formal parameter on the actual infinity kernel. -/
theorem norm_parameter_nsmul_eq_of_not_dvd
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : LocalPoint A B)
    (hP : P ∈ infinityKernel A B)
    (n : ℕ)
    (hn : ¬37 ∣ n) :
    ‖parameter A B (n • P)‖ = ‖parameter A B P‖ := by
  by_cases hPzero : P = 0
  · subst P
    simp [parameter_zero]
  let t := parameter A B P
  have htZero : t ≠ 0 := by
    intro ht0
    apply hPzero
    exact (parameter_eq_zero_iff A B P hP).1 (by simpa [t] using ht0)
  have htPos : 0 < ‖t‖ := norm_pos_iff.mpr htZero
  have htLt : ‖t‖ < 1 := by
    simpa [t] using norm_parameter_lt_one_of_mem_kernel_point A B P hP
  have hcubeLt : ‖t‖ ^ 3 < ‖t‖ := by
    nlinarith [mul_self_nonneg ‖t‖]
  have happrox :=
    norm_parameter_nsmul_sub_le_cube A B P hP n
  have hnNorm : ‖(n : ℚ_[37])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr
      ((show Nat.Prime 37 by norm_num).coprime_iff_not_dvd.mpr hn)
  have hlinearNorm :
      ‖(n : ℚ_[37]) * t‖ = ‖t‖ := by
    rw [norm_mul, hnNorm, one_mul]
  have herrLt :
      ‖parameter A B (n • P) - (n : ℚ_[37]) * t‖ <
        ‖(n : ℚ_[37]) * t‖ := by
    rw [hlinearNorm]
    have happrox' :
        ‖parameter A B (n • P) - (n : ℚ_[37]) * t‖ ≤ ‖t‖ ^ 3 := by
      simpa [t] using happrox
    exact happrox'.trans_lt hcubeLt
  have hrecompose :
      parameter A B (n • P) =
        (n : ℚ_[37]) * t +
          (parameter A B (n • P) - (n : ℚ_[37]) * t) := by
    ring
  rw [hrecompose,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (ne_of_gt herrLt),
    max_eq_left herrLt.le, hlinearNorm]

/-- Multiplication by `37` scales the formal-parameter norm by exactly
`37⁻¹`. -/
theorem norm_parameter_37_nsmul_eq
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : LocalPoint A B)
    (hP : P ∈ infinityKernel A B) :
    ‖parameter A B (37 • P)‖ =
      (37 : ℝ)⁻¹ * ‖parameter A B P‖ := by
  by_cases hPzero : P = 0
  · subst P
    simp [parameter_zero]
  let t := parameter A B P
  have htZero : t ≠ 0 := by
    intro ht0
    apply hPzero
    exact (parameter_eq_zero_iff A B P hP).1 (by simpa [t] using ht0)
  have htPos : 0 < ‖t‖ := norm_pos_iff.mpr htZero
  have htLt : ‖t‖ < 1 := by
    simpa [t] using norm_parameter_lt_one_of_mem_kernel_point A B P hP
  have htLe : ‖t‖ ≤ (37 : ℝ)⁻¹ :=
    norm_le_inv_37_of_lt_one t htLt
  have hinvPos : 0 < (37 : ℝ)⁻¹ := by positivity
  have hinvLt : (37 : ℝ)⁻¹ < 1 := by norm_num
  have htSqLt : ‖t‖ ^ 2 < (37 : ℝ)⁻¹ := by
    calc
      ‖t‖ ^ 2 ≤ ((37 : ℝ)⁻¹) ^ 2 := by
        gcongr
      _ < (37 : ℝ)⁻¹ := by
        nlinarith
  have hcubeLt :
      ‖t‖ ^ 3 < (37 : ℝ)⁻¹ * ‖t‖ := by
    calc
      ‖t‖ ^ 3 = ‖t‖ ^ 2 * ‖t‖ := by ring
      _ < (37 : ℝ)⁻¹ * ‖t‖ :=
        mul_lt_mul_of_pos_right htSqLt htPos
  have happrox :=
    norm_parameter_nsmul_sub_le_cube A B P hP 37
  have hlinearNorm :
      ‖(37 : ℚ_[37]) * t‖ =
        (37 : ℝ)⁻¹ * ‖t‖ := by
    rw [norm_mul, norm_37_padic]
  have herrLt :
      ‖parameter A B (37 • P) - (37 : ℚ_[37]) * t‖ <
        ‖(37 : ℚ_[37]) * t‖ := by
    rw [hlinearNorm]
    have happrox' :
        ‖parameter A B (37 • P) - (37 : ℚ_[37]) * t‖ ≤ ‖t‖ ^ 3 := by
      simpa [t] using happrox
    exact happrox'.trans_lt hcubeLt
  have hrecompose :
      parameter A B (37 • P) =
        (37 : ℚ_[37]) * t +
          (parameter A B (37 • P) - (37 : ℚ_[37]) * t) := by
    ring
  rw [hrecompose,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (ne_of_gt herrLt),
    max_eq_left herrLt.le, hlinearNorm]

/-- Prime-to-`37` multiplication has trivial kernel on the actual infinity
kernel. -/
theorem nsmul_eq_zero_iff_of_not_dvd_37
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : LocalPoint A B)
    (hP : P ∈ infinityKernel A B)
    (n : ℕ)
    (hn : ¬37 ∣ n) :
    n • P = 0 ↔ P = 0 := by
  constructor
  · intro hnP
    have hnorm :=
      norm_parameter_nsmul_eq_of_not_dvd A B P hP n hn
    rw [hnP, parameter_zero, norm_zero] at hnorm
    have htNorm : ‖parameter A B P‖ = 0 := hnorm.symm
    exact
      (parameter_eq_zero_iff A B P hP).1
        (norm_eq_zero.mp htNorm)
  · intro hzero
    subst P
    simp

/-- Multiplication by `37` has trivial kernel on the actual infinity
kernel. -/
theorem nsmul_37_eq_zero_iff
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : LocalPoint A B)
    (hP : P ∈ infinityKernel A B) :
    37 • P = 0 ↔ P = 0 := by
  constructor
  · intro h37P
    have hnorm := norm_parameter_37_nsmul_eq A B P hP
    rw [h37P, parameter_zero, norm_zero] at hnorm
    have hnormZero : ‖parameter A B P‖ = 0 := by
      rcases mul_eq_zero.mp hnorm.symm with hinv | ht
      · exact (ne_of_gt (show 0 < (37 : ℝ)⁻¹ by positivity) hinv).elim
      · exact ht
    exact
      (parameter_eq_zero_iff A B P hP).1
        (norm_eq_zero.mp hnormZero)
  · intro hzero
    subst P
    simp

private theorem nsmul_eq_zero_of_ne_zero
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (n : ℕ) :
    ∀ P : LocalPoint A B,
      P ∈ infinityKernel A B →
      n ≠ 0 →
      n • P = 0 →
      P = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro P hP hn hnP
      by_cases hdiv : 37 ∣ n
      · obtain ⟨m, rfl⟩ := hdiv
        have hm : m ≠ 0 := by
          intro hm0
          subst m
          simp at hn
        have hlt : m < 37 * m := by omega
        have h37Mem : 37 • P ∈ infinityKernel A B :=
          (infinityKernel A B).nsmul_mem hP 37
        have hm37 : m • (37 • P) = 0 := by
          rw [← mul_nsmul]
          simpa [Nat.mul_comm] using hnP
        have h37zero :=
          ih m hlt (37 • P) h37Mem hm hm37
        exact (nsmul_37_eq_zero_iff A B P hP).1 h37zero
      · exact
          (nsmul_eq_zero_iff_of_not_dvd_37 A B P hP n hdiv).1 hnP

/-- Every nonzero natural multiplication map is injective on the actual
infinity kernel. -/
theorem infinityKernel_nsmul_right_injective
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (n : ℕ) (hn : n ≠ 0) :
    Function.Injective
      (fun P : infinityKernel A B => n • P) := by
  intro P Q hPQ
  apply Subtype.ext
  have hsubMem :
      (P : LocalPoint A B) - (Q : LocalPoint A B) ∈
        infinityKernel A B :=
    (infinityKernel A B).sub_mem P.property Q.property
  have hPQ' :
      n • (P : LocalPoint A B) = n • (Q : LocalPoint A B) := by
    exact congrArg Subtype.val hPQ
  have hzero :
      n • ((P : LocalPoint A B) - (Q : LocalPoint A B)) = 0 := by
    rw [nsmul_sub, hPQ', sub_self]
  exact sub_eq_zero.mp
    (nsmul_eq_zero_of_ne_zero A B n
      ((P : LocalPoint A B) - (Q : LocalPoint A B))
      hsubMem hn hzero)

/-- The actual infinity kernel is additively torsion-free. -/
instance infinityKernel_isAddTorsionFree
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic] :
    IsAddTorsionFree (infinityKernel A B) where
  nsmul_right_injective {n} hn :=
    infinityKernel_nsmul_right_injective A B _ hn

end

end GaussianFormalKernelTorsion
end Cuboid2
