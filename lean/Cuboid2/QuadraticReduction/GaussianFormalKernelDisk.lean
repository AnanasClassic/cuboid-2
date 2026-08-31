import Cuboid2.QuadraticReduction.GaussianProjectiveReductionHom
import Cuboid2.QuadraticReduction.GaussianFormalLocal

/-!
# Valuation boundary for the split-37 formal kernel disk

This module isolates unconditional facts about the fibre of projective
reduction above infinity.  It characterizes that fibre, proves its stability
under negation, extracts congruences from coincident integral reductions, and
proves that adding an infinity-disk point to an integral point preserves both
reduced affine coordinates.  Group cancellation then upgrades the mixed case
to closure of the infinity fibre and translation invariance for every point.
Finally, secant and tangent estimates show that coincident reductions differ
by an infinity-fibre point, so the reduction fibres are exactly its cosets.

No group-map interface is assumed here.
-/

namespace Cuboid2
namespace GaussianFormalKernelDisk

noncomputable section

open GaussianProjectiveReduction
open GaussianProjectiveReductionHom
open GaussianGoodReduction
open GaussianFinite
open GaussianP37Bridge

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : DecidableEq ℚ_[37] := Classical.decEq _

/-! ## Exact description of the infinity fibre -/

/-- A point lies in the projective infinity disk when it is infinity itself,
or when its affine abscissa is nonintegral. -/
def InInfinityDisk
    (A B : ℤ_[37]) :
    (localPadicCurve A B).toAffine.Point → Prop
  | .zero => True
  | .some x _ _ => 1 < ‖x‖

/-- Every affine point with nonintegral abscissa reduces to infinity. -/
theorem finiteReducePoint_eq_none_of_norm_x_gt_one
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hx : 1 < ‖x‖) :
    finiteReducePoint A B (.some x y hpoint) = none := by
  have hxNot : ¬‖x‖ ≤ 1 := not_le_of_gt hx
  simp [finiteReducePoint, reducePoint, hxNot, finitePointOfResidue]

/-- Conversely, an affine point reducing to infinity has nonintegral
abscissa. -/
theorem norm_x_gt_one_of_finiteReducePoint_eq_none
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hred : finiteReducePoint A B (.some x y hpoint) = none) :
    1 < ‖x‖ := by
  by_contra hx
  have hxInt : ‖x‖ ≤ 1 := le_of_not_gt hx
  have hred' := hred
  unfold finiteReducePoint at hred'
  simp only [reducePoint, hxInt, ↓reduceDIte] at hred'
  simp [finitePointOfResidue, WeierstrassCurve.Affine.Point.mk] at hred'

/-- The definitional infinity disk is exactly the kernel fibre of executable
projective reduction. -/
theorem finiteReducePoint_eq_none_iff_inInfinityDisk
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : (localPadicCurve A B).toAffine.Point) :
    finiteReducePoint A B P = none ↔ InInfinityDisk A B P := by
  rcases P with (_ | ⟨x, y, hpoint⟩)
  · constructor
    · intro
      trivial
    · intro
      exact finiteReducePoint_zero A B
  · constructor
    · exact norm_x_gt_one_of_finiteReducePoint_eq_none A B hpoint
    · exact finiteReducePoint_eq_none_of_norm_x_gt_one A B hpoint

/-- The infinity fibre is stable under negation. -/
theorem finiteReducePoint_neg_eq_none_iff
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : (localPadicCurve A B).toAffine.Point) :
    finiteReducePoint A B (-P) = none ↔
      finiteReducePoint A B P = none := by
  rw [finiteReducePoint_neg]
  cases finiteReducePoint A B P <;> simp [finiteNeg]

/-! ## Congruences from coincident integral reductions -/

/-- Equal reductions of two integral affine points give equal residue
coordinates, with no appeal to a group-homomorphism theorem. -/
theorem residue_coordinates_eq_of_finiteReducePoint_eq
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x₁ y₁ x₂ y₂ : ℚ_[37]}
    (h₁ : (localPadicCurve A B).toAffine.Nonsingular x₁ y₁)
    (h₂ : (localPadicCurve A B).toAffine.Nonsingular x₂ y₂)
    (hx₁ : ‖x₁‖ ≤ 1) (hx₂ : ‖x₂‖ ≤ 1)
    (hred :
      finiteReducePoint A B (.some x₁ y₁ h₁) =
        finiteReducePoint A B (.some x₂ y₂ h₂)) :
    PadicInt.toZMod (⟨x₁, hx₁⟩ : ℤ_[37]) =
        PadicInt.toZMod (⟨x₂, hx₂⟩ : ℤ_[37]) ∧
      PadicInt.toZMod
          (⟨y₁, norm_y_le_one_of_norm_x_le_one A B h₁.1 hx₁⟩ :
            ℤ_[37]) =
        PadicInt.toZMod
          (⟨y₂, norm_y_le_one_of_norm_x_le_one A B h₂.1 hx₂⟩ :
            ℤ_[37]) := by
  have hred' := hred
  simp only [finiteReducePoint, reducePoint, hx₁, hx₂, ↓reduceDIte,
    finitePointOfResidue, WeierstrassCurve.Affine.Point.mk] at hred'
  injection hred' with hxy
  exact
    ⟨ZMod.val_injective 37 (congrArg Prod.fst hxy),
      ZMod.val_injective 37 (congrArg Prod.snd hxy)⟩

/-- Two 37-adic integers with equal residues differ by an element of norm
strictly less than one. -/
theorem norm_coe_sub_lt_one_of_toZMod_eq
    (u v : ℤ_[37])
    (hred : PadicInt.toZMod u = PadicInt.toZMod v) :
    ‖(u : ℚ_[37]) - (v : ℚ_[37])‖ < 1 := by
  let w : ℤ_[37] := u - v
  have hwMap : PadicInt.toZMod w = 0 := by
    simp [w, hred]
  have hwMem : w ∈ IsLocalRing.maximalIdeal ℤ_[37] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact hwMap
  have hspan : w ∈ Ideal.span {((37 : ℕ) : ℤ_[37])} := by
    simpa only [PadicInt.maximalIdeal_eq_span_p] using hwMem
  have hwDvd : ((37 : ℕ) : ℤ_[37]) ∣ w :=
    Ideal.mem_span_singleton.mp hspan
  have hwNorm : ‖w‖ < 1 :=
    (PadicInt.norm_lt_one_iff_dvd w).mpr hwDvd
  have hwCoe :
      (w : ℚ_[37]) = (u : ℚ_[37]) - (v : ℚ_[37]) := by
    simpa only [w] using PadicInt.coe_sub u v
  calc
    ‖(u : ℚ_[37]) - (v : ℚ_[37])‖ =
        ‖(w : ℚ_[37])‖ := congrArg norm hwCoe.symm
    _ = ‖w‖ := (PadicInt.norm_eq_padic_norm w.property).symm
    _ < 1 := hwNorm

/-- An integral 37-adic element reducing to zero has generic-fibre norm
strictly less than one. -/
theorem norm_coe_lt_one_of_toZMod_eq_zero
    (u : ℤ_[37]) (hred : PadicInt.toZMod u = 0) :
    ‖(u : ℚ_[37])‖ < 1 := by
  have h :=
    norm_coe_sub_lt_one_of_toZMod_eq u 0 (by simpa using hred)
  simpa using h

/-- The converse residue criterion: 37-adic integers whose generic-fibre
difference has norm strictly less than one have the same residue. -/
theorem toZMod_eq_of_norm_coe_sub_lt_one
    (u v : ℤ_[37])
    (h : ‖(u : ℚ_[37]) - (v : ℚ_[37])‖ < 1) :
    PadicInt.toZMod u = PadicInt.toZMod v := by
  let w : ℤ_[37] := u - v
  have hwCoe :
      (w : ℚ_[37]) = (u : ℚ_[37]) - (v : ℚ_[37]) := by
    simpa only [w] using PadicInt.coe_sub u v
  have hwNorm : ‖w‖ < 1 := by
    calc
      ‖w‖ = ‖(w : ℚ_[37])‖ :=
        (PadicInt.padic_norm_e_of_padicInt w).symm
      _ = ‖(u : ℚ_[37]) - (v : ℚ_[37])‖ := congrArg norm hwCoe
      _ < 1 := h
  have hwDvd : ((37 : ℕ) : ℤ_[37]) ∣ w :=
    (PadicInt.norm_lt_one_iff_dvd w).mp hwNorm
  have hwMem : w ∈ IsLocalRing.maximalIdeal ℤ_[37] := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    exact hwDvd
  have hwMap : PadicInt.toZMod w = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
    exact hwMem
  simpa only [w, map_sub, sub_eq_zero] using hwMap

/-- A 37-adic integer with nonzero residue is a unit and hence has generic
fibre norm exactly one. -/
theorem norm_coe_eq_one_of_toZMod_ne_zero
    (u : ℤ_[37]) (hred : PadicInt.toZMod u ≠ 0) :
    ‖(u : ℚ_[37])‖ = 1 := by
  apply le_antisymm u.property
  apply le_of_not_gt
  intro hlt
  apply hred
  have hzero :=
    toZMod_eq_of_norm_coe_sub_lt_one u 0 (by simpa using hlt)
  simpa using hzero

/-- Coordinatewise maximal-ideal congruence is enough to identify executable
reductions of two integral affine points. -/
theorem finiteReducePoint_eq_of_norm_coordinate_sub_lt_one
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x₁ y₁ x₂ y₂ : ℚ_[37]}
    (h₁ : (localPadicCurve A B).toAffine.Nonsingular x₁ y₁)
    (h₂ : (localPadicCurve A B).toAffine.Nonsingular x₂ y₂)
    (hx₁ : ‖x₁‖ ≤ 1) (hx₂ : ‖x₂‖ ≤ 1)
    (hxDiff : ‖x₁ - x₂‖ < 1)
    (hyDiff : ‖y₁ - y₂‖ < 1) :
    finiteReducePoint A B (.some x₁ y₁ h₁) =
      finiteReducePoint A B (.some x₂ y₂ h₂) := by
  have hy₁ : ‖y₁‖ ≤ 1 :=
    norm_y_le_one_of_norm_x_le_one A B h₁.1 hx₁
  have hy₂ : ‖y₂‖ ≤ 1 :=
    norm_y_le_one_of_norm_x_le_one A B h₂.1 hx₂
  have hxRed :
      PadicInt.toZMod (⟨x₁, hx₁⟩ : ℤ_[37]) =
        PadicInt.toZMod (⟨x₂, hx₂⟩ : ℤ_[37]) :=
    toZMod_eq_of_norm_coe_sub_lt_one
      (⟨x₁, hx₁⟩ : ℤ_[37]) (⟨x₂, hx₂⟩ : ℤ_[37]) hxDiff
  have hyRed :
      PadicInt.toZMod (⟨y₁, hy₁⟩ : ℤ_[37]) =
        PadicInt.toZMod (⟨y₂, hy₂⟩ : ℤ_[37]) :=
    toZMod_eq_of_norm_coe_sub_lt_one
      (⟨y₁, hy₁⟩ : ℤ_[37]) (⟨y₂, hy₂⟩ : ℤ_[37]) hyDiff
  simp only [finiteReducePoint, reducePoint, hx₁, hx₂, ↓reduceDIte,
    finitePointOfResidue, WeierstrassCurve.Affine.Point.mk]
  rw [congrArg ZMod.val hxRed, congrArg ZMod.val hyRed]

/-- Coincident executable reductions of integral affine points force both
coordinate differences into the maximal ideal. -/
theorem norm_coordinate_sub_lt_one_of_finiteReducePoint_eq
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x₁ y₁ x₂ y₂ : ℚ_[37]}
    (h₁ : (localPadicCurve A B).toAffine.Nonsingular x₁ y₁)
    (h₂ : (localPadicCurve A B).toAffine.Nonsingular x₂ y₂)
    (hx₁ : ‖x₁‖ ≤ 1) (hx₂ : ‖x₂‖ ≤ 1)
    (hred :
      finiteReducePoint A B (.some x₁ y₁ h₁) =
        finiteReducePoint A B (.some x₂ y₂ h₂)) :
    ‖x₁ - x₂‖ < 1 ∧ ‖y₁ - y₂‖ < 1 := by
  obtain ⟨hxRed, hyRed⟩ :=
    residue_coordinates_eq_of_finiteReducePoint_eq
      A B h₁ h₂ hx₁ hx₂ hred
  exact
    ⟨norm_coe_sub_lt_one_of_toZMod_eq
        (⟨x₁, hx₁⟩ : ℤ_[37]) (⟨x₂, hx₂⟩ : ℤ_[37]) hxRed,
      norm_coe_sub_lt_one_of_toZMod_eq
        (⟨y₁, norm_y_le_one_of_norm_x_le_one A B h₁.1 hx₁⟩ :
          ℤ_[37])
        (⟨y₂, norm_y_le_one_of_norm_x_le_one A B h₂.1 hx₂⟩ :
          ℤ_[37])
        hyRed⟩

/-! ## Dominant terms in the mixed integral/infinity case -/

/-- The factored equation on the normalized local two-torsion model. -/
theorem local_curve_equation
    (A B : ℤ_[37]) {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y) :
    y ^ 2 =
      x * (x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37])) := by
  have h := hpoint.left
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [localPadicCurve, localCurve, WeierstrassCurve.map,
    map_zero, zero_mul, add_zero] at h
  calc
    y ^ 2 =
        x ^ 3 + (A : ℚ_[37]) * x ^ 2 + (B : ℚ_[37]) * x := h
    _ = x * (x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37])) := by
      ring

/-- Reducing an integral generic-fibre point gives a genuinely nonsingular
point on the elliptic special fibre. -/
theorem residue_nonsingular_of_integral_point
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hx : ‖x‖ ≤ 1) :
    (localResidueCurve A B).toAffine.Nonsingular
      (PadicInt.toZMod (⟨x, hx⟩ : ℤ_[37]))
      (PadicInt.toZMod
        (⟨y, norm_y_le_one_of_norm_x_le_one A B hpoint.1 hx⟩ :
          ℤ_[37])) := by
  let xInt : ℤ_[37] := ⟨x, hx⟩
  let yInt : ℤ_[37] :=
    ⟨y, norm_y_le_one_of_norm_x_le_one A B hpoint.1 hx⟩
  have hInt :
      (localCurve A B).toAffine.Equation xInt yInt := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [localCurve, zero_mul, add_zero]
    apply Subtype.val_injective
    have hcurve := hpoint.1
    rw [WeierstrassCurve.Affine.equation_iff] at hcurve
    change
      y ^ 2 =
        x ^ 3 + (A : ℚ_[37]) * x ^ 2 + (B : ℚ_[37]) * x
    have hcurve' :
        y ^ 2 =
          x ^ 3 + PadicInt.Coe.ringHom A * x ^ 2 +
            PadicInt.Coe.ringHom B * x := by
      simpa only [localPadicCurve, localCurve, WeierstrassCurve.map,
        map_zero, zero_mul, add_zero] using hcurve
    exact hcurve'.trans (by rfl)
  apply
    (localResidueCurve A B).toAffine.equation_iff_nonsingular.mp
  exact hInt.map PadicInt.toZMod

/-- At a residue point with ordinate zero, nonsingularity says exactly that
the derivative of `x³ + A x² + B x` is nonzero. -/
theorem residue_derivative_ne_zero_of_y_eq_zero
    (A B x y : ℤ_[37])
    [_hEll : (localResidueCurve A B).IsElliptic]
    (hpoint :
      (localResidueCurve A B).toAffine.Nonsingular
        (PadicInt.toZMod x) (PadicInt.toZMod y))
    (hy : PadicInt.toZMod y = 0) :
    3 * PadicInt.toZMod x ^ 2 +
        2 * PadicInt.toZMod A * PadicInt.toZMod x +
        PadicInt.toZMod B ≠ 0 := by
  have hn :=
    ((localResidueCurve A B).toAffine.nonsingular_iff'
      (PadicInt.toZMod x) (PadicInt.toZMod y)).mp hpoint
  rcases hn.2 with hx | hy'
  · have hx' :
        -(3 * PadicInt.toZMod x ^ 2 +
            2 * PadicInt.toZMod A * PadicInt.toZMod x +
            PadicInt.toZMod B) ≠ 0 := by
      simpa only [localResidueCurve, localCurve, WeierstrassCurve.map,
        map_zero, zero_mul, zero_sub] using hx
    exact neg_ne_zero.mp hx'
  · rw [hy] at hy'
    simp only [localResidueCurve, localCurve, WeierstrassCurve.map,
      map_zero, zero_mul, add_zero, ne_eq] at hy'
    exact (hy' rfl).elim

/-- The lifted `x`-derivative is a 37-adic unit at an integral point whose
special-fibre ordinate is zero. -/
theorem norm_curve_derivative_eq_one_of_residue_y_eq_zero
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hx : ‖x‖ ≤ 1)
    (hyRed :
      PadicInt.toZMod
        (⟨y, norm_y_le_one_of_norm_x_le_one A B hpoint.1 hx⟩ :
          ℤ_[37]) = 0) :
    ‖3 * x ^ 2 + 2 * (A : ℚ_[37]) * x + (B : ℚ_[37])‖ = 1 := by
  let xInt : ℤ_[37] := ⟨x, hx⟩
  let yInt : ℤ_[37] :=
    ⟨y, norm_y_le_one_of_norm_x_le_one A B hpoint.1 hx⟩
  let D : ℤ_[37] := 3 * xInt ^ 2 + 2 * A * xInt + B
  have hres :=
    residue_nonsingular_of_integral_point A B hpoint hx
  have hD :
      3 * PadicInt.toZMod xInt ^ 2 +
          2 * PadicInt.toZMod A * PadicInt.toZMod xInt +
          PadicInt.toZMod B ≠ 0 :=
    residue_derivative_ne_zero_of_y_eq_zero
      A B xInt yInt hres (by simpa only [yInt] using hyRed)
  have hDred : PadicInt.toZMod D ≠ 0 := by
    simpa only [D, map_add, map_mul, map_pow, map_ofNat] using hD
  have hDnorm := norm_coe_eq_one_of_toZMod_ne_zero D hDred
  have hDcoe :
      (D : ℚ_[37]) =
        3 * x ^ 2 + 2 * (A : ℚ_[37]) * x + (B : ℚ_[37]) := by
    simp only [D, xInt, PadicInt.coe_add, PadicInt.coe_mul]
    norm_cast
  rw [← hDcoe]
  exact hDnorm

/-- For two integral abscissae with the same residue, the cubic divided
difference is a unit whenever the common point is on the residue
two-torsion fibre. -/
theorem norm_curve_dividedDifference_eq_one_of_common_residue_y_zero
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x₁ y₁ x₂ y₂ : ℚ_[37]}
    (h₁ : (localPadicCurve A B).toAffine.Nonsingular x₁ y₁)
    (h₂ : (localPadicCurve A B).toAffine.Nonsingular x₂ y₂)
    (hx₁ : ‖x₁‖ ≤ 1) (hx₂ : ‖x₂‖ ≤ 1)
    (hred :
      finiteReducePoint A B (.some x₁ y₁ h₁) =
        finiteReducePoint A B (.some x₂ y₂ h₂))
    (hyRed :
      PadicInt.toZMod
        (⟨y₁, norm_y_le_one_of_norm_x_le_one A B h₁.1 hx₁⟩ :
          ℤ_[37]) = 0) :
    ‖x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 +
        (A : ℚ_[37]) * (x₁ + x₂) + (B : ℚ_[37])‖ = 1 := by
  let x₁Int : ℤ_[37] := ⟨x₁, hx₁⟩
  let x₂Int : ℤ_[37] := ⟨x₂, hx₂⟩
  let y₁Int : ℤ_[37] :=
    ⟨y₁, norm_y_le_one_of_norm_x_le_one A B h₁.1 hx₁⟩
  let D : ℤ_[37] :=
    x₁Int ^ 2 + x₁Int * x₂Int + x₂Int ^ 2 +
      A * (x₁Int + x₂Int) + B
  obtain ⟨hxRed, _hyRed⟩ :=
    residue_coordinates_eq_of_finiteReducePoint_eq
      A B h₁ h₂ hx₁ hx₂ hred
  have hres :=
    residue_nonsingular_of_integral_point A B h₁ hx₁
  have hderiv :
      3 * PadicInt.toZMod x₁Int ^ 2 +
          2 * PadicInt.toZMod A * PadicInt.toZMod x₁Int +
          PadicInt.toZMod B ≠ 0 :=
    residue_derivative_ne_zero_of_y_eq_zero
      A B x₁Int y₁Int hres (by simpa only [y₁Int] using hyRed)
  have hDred : PadicInt.toZMod D ≠ 0 := by
    intro hzero
    apply hderiv
    have hmap :
        PadicInt.toZMod D =
          3 * PadicInt.toZMod x₁Int ^ 2 +
            2 * PadicInt.toZMod A * PadicInt.toZMod x₁Int +
            PadicInt.toZMod B := by
      simp only [D, map_add, map_mul, map_pow]
      rw [← hxRed]
      ring
    rw [← hmap]
    exact hzero
  have hDnorm := norm_coe_eq_one_of_toZMod_ne_zero D hDred
  have hDcoe :
      (D : ℚ_[37]) =
        x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 +
          (A : ℚ_[37]) * (x₁ + x₂) + (B : ℚ_[37]) := by
    simp only [D, x₁Int, x₂Int, PadicInt.coe_add,
      PadicInt.coe_mul]
    norm_cast
  rw [← hDcoe]
  exact hDnorm

/-- Outside the integral chart, the quadratic leading term strictly
dominates the lower-degree integral terms. -/
theorem norm_inner_eq_norm_x_sq
    (A B : ℤ_[37]) {x : ℚ_[37]} (hx : 1 < ‖x‖) :
    ‖x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37])‖ = ‖x‖ ^ 2 := by
  have hA : ‖(A : ℚ_[37])‖ ≤ 1 := A.property
  have hB : ‖(B : ℚ_[37])‖ ≤ 1 := B.property
  have hAx : ‖(A : ℚ_[37]) * x‖ ≤ ‖x‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg (A : ℚ_[37]), norm_nonneg x]
  have hsmall :
      ‖(A : ℚ_[37]) * x + (B : ℚ_[37])‖ ≤ ‖x‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    exact max_le hAx (hB.trans hx.le)
  have hlt :
      ‖(A : ℚ_[37]) * x + (B : ℚ_[37])‖ < ‖x ^ 2‖ := by
    rw [norm_pow]
    nlinarith [norm_nonneg x]
  calc
    ‖x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37])‖ =
        ‖x ^ 2 + ((A : ℚ_[37]) * x + (B : ℚ_[37]))‖ := by
          congr 1
          ring
    _ = max ‖x ^ 2‖ ‖(A : ℚ_[37]) * x + (B : ℚ_[37])‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (ne_of_gt hlt)
    _ = ‖x ^ 2‖ := max_eq_left hlt.le
    _ = ‖x‖ ^ 2 := norm_pow x 2

/-- The ordinate of an infinity-disk point has the expected cubic norm. -/
theorem norm_y_sq_eq_norm_x_cube
    (A B : ℤ_[37]) {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hx : 1 < ‖x‖) :
    ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
  calc
    ‖y‖ ^ 2 = ‖y ^ 2‖ := (norm_pow y 2).symm
    _ =
        ‖x * (x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37]))‖ := by
          rw [local_curve_equation A B hpoint]
    _ =
        ‖x‖ * ‖x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37])‖ :=
          norm_mul _ _
    _ = ‖x‖ ^ 3 := by
      rw [norm_inner_eq_norm_x_sq A B hx]
      ring

private theorem norm_sub_eq_right_of_lt
    {a b : ℚ_[37]} (h : ‖a‖ < ‖b‖) :
    ‖a - b‖ = ‖b‖ := by
  calc
    ‖a - b‖ = ‖a + -b‖ := by rw [sub_eq_add_neg]
    _ = max ‖a‖ ‖-b‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (by simpa only [norm_neg] using ne_of_lt h)
    _ = ‖b‖ := by simp [max_eq_right h.le]

private theorem norm_sub_eq_left_of_lt
    {a b : ℚ_[37]} (h : ‖b‖ < ‖a‖) :
    ‖a - b‖ = ‖a‖ := by
  calc
    ‖a - b‖ = ‖a + -b‖ := by rw [sub_eq_add_neg]
    _ = max ‖a‖ ‖-b‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (by simpa only [norm_neg] using ne_of_gt h)
    _ = ‖a‖ := by simp [max_eq_left h.le]

/-- If two integral points have the same reduction but distinct abscissae,
the secant slope used for their difference has norm greater than one.

When the common residue ordinate is nonzero, `y₁+y₂` is a unit.  On the
residue two-torsion branch, the curve equation replaces that numerator by the
unit cubic divided difference divided by `y₁-y₂`.
-/
theorem norm_difference_secant_slope_gt_one_of_X_ne
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x₁ y₁ x₂ y₂ : ℚ_[37]}
    (h₁ : (localPadicCurve A B).toAffine.Nonsingular x₁ y₁)
    (h₂ : (localPadicCurve A B).toAffine.Nonsingular x₂ y₂)
    (hx₁ : ‖x₁‖ ≤ 1) (hx₂ : ‖x₂‖ ≤ 1)
    (hred :
      finiteReducePoint A B (.some x₁ y₁ h₁) =
        finiteReducePoint A B (.some x₂ y₂ h₂))
    (hxNe : x₁ ≠ x₂) :
    1 < ‖(y₁ + y₂) / (x₁ - x₂)‖ := by
  have hy₁ : ‖y₁‖ ≤ 1 :=
    norm_y_le_one_of_norm_x_le_one A B h₁.1 hx₁
  have hy₂ : ‖y₂‖ ≤ 1 :=
    norm_y_le_one_of_norm_x_le_one A B h₂.1 hx₂
  let y₁Int : ℤ_[37] := ⟨y₁, hy₁⟩
  obtain ⟨_hxRed, hyRed⟩ :=
    residue_coordinates_eq_of_finiteReducePoint_eq
      A B h₁ h₂ hx₁ hx₂ hred
  obtain ⟨hxDiff, hyDiff⟩ :=
    norm_coordinate_sub_lt_one_of_finiteReducePoint_eq
      A B h₁ h₂ hx₁ hx₂ hred
  have hxDiff0 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hxNe
  by_cases hyZero : PadicInt.toZMod y₁Int = 0
  · let D : ℚ_[37] :=
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 +
        (A : ℚ_[37]) * (x₁ + x₂) + (B : ℚ_[37])
    have hDnorm : ‖D‖ = 1 := by
      exact
        norm_curve_dividedDifference_eq_one_of_common_residue_y_zero
          A B h₁ h₂ hx₁ hx₂ hred
            (by simpa only [y₁Int] using hyZero)
    have hD0 : D ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hDnorm
      norm_num at hDnorm
    have hEq₁ := local_curve_equation A B h₁
    have hEq₂ := local_curve_equation A B h₂
    have hfactor :
        (y₁ - y₂) * (y₁ + y₂) =
          (x₁ - x₂) * D := by
      dsimp only [D]
      linear_combination hEq₁ - hEq₂
    have hyDiff0 : y₁ - y₂ ≠ 0 := by
      intro hzero
      have hprod : (x₁ - x₂) * D = 0 := by
        rw [← hfactor, hzero, zero_mul]
      exact (mul_ne_zero hxDiff0 hD0) hprod
    have hslope :
        (y₁ + y₂) / (x₁ - x₂) =
          D / (y₁ - y₂) := by
      field_simp [hxDiff0, hyDiff0]
      linear_combination hfactor
    rw [hslope, norm_div, hDnorm]
    have hpos : 0 < ‖y₁ - y₂‖ :=
      norm_pos_iff.mpr hyDiff0
    simpa only [one_div] using
      (one_lt_inv₀ hpos).2 hyDiff
  · have hy₁Norm : ‖y₁‖ = 1 :=
      norm_coe_eq_one_of_toZMod_ne_zero y₁Int hyZero
    have hTwo : ‖(2 : ℚ_[37])‖ = 1 :=
      Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
    have hTwoY : ‖(2 : ℚ_[37]) * y₁‖ = 1 := by
      rw [norm_mul, hTwo, hy₁Norm, one_mul]
    have hsum : ‖y₁ + y₂‖ = 1 := by
      calc
        ‖y₁ + y₂‖ =
            ‖(2 : ℚ_[37]) * y₁ - (y₁ - y₂)‖ := by
              congr 1
              ring
        _ = ‖(2 : ℚ_[37]) * y₁‖ :=
          norm_sub_eq_left_of_lt (by simpa only [hTwoY] using hyDiff)
        _ = 1 := hTwoY
    rw [norm_div, hsum]
    have hpos : 0 < ‖x₁ - x₂‖ :=
      norm_pos_iff.mpr hxDiff0
    simpa only [one_div] using
      (one_lt_inv₀ hpos).2 hxDiff

/-- At a lift of a residue two-torsion point, the tangent slope has norm
greater than one: its derivative numerator is a unit and its `2y`
denominator lies in the maximal ideal. -/
theorem norm_tangent_slope_gt_one_of_residue_y_zero
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x y : ℚ_[37]}
    (hpoint : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hx : ‖x‖ ≤ 1)
    (hy0 : y ≠ 0)
    (hyRed :
      PadicInt.toZMod
        (⟨y, norm_y_le_one_of_norm_x_le_one A B hpoint.1 hx⟩ :
          ℤ_[37]) = 0) :
    1 <
      ‖(localPadicCurve A B).toAffine.slope x x y y‖ := by
  have hDerivative :
      ‖3 * x ^ 2 + 2 * (A : ℚ_[37]) * x + (B : ℚ_[37])‖ = 1 :=
    norm_curve_derivative_eq_one_of_residue_y_eq_zero
      A B hpoint hx hyRed
  have hyNorm : ‖y‖ < 1 := by
    exact norm_coe_lt_one_of_toZMod_eq_zero
      (⟨y, norm_y_le_one_of_norm_x_le_one A B hpoint.1 hx⟩ :
        ℤ_[37]) hyRed
  have hyNeNeg : y ≠ -y := by
    intro h
    apply hy0
    have htwo : (2 : ℚ_[37]) * y = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hyNeCurveNeg :
      y ≠ (localPadicCurve A B).toAffine.negY x y := by
    simpa only [localPadicCurve, localCurve, WeierstrassCurve.map,
      WeierstrassCurve.Affine.negY, map_zero, zero_mul, sub_zero] using
      hyNeNeg
  have hslope :
      (localPadicCurve A B).toAffine.slope x x y y =
        (3 * x ^ 2 + 2 * (A : ℚ_[37]) * x + (B : ℚ_[37])) /
          ((2 : ℚ_[37]) * y) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyNeCurveNeg]
    simp only [localPadicCurve, localCurve, WeierstrassCurve.map,
      WeierstrassCurve.Affine.negY, map_zero, zero_mul, sub_zero]
    rw [show PadicInt.Coe.ringHom A = (A : ℚ_[37]) by rfl,
      show PadicInt.Coe.ringHom B = (B : ℚ_[37]) by rfl]
    congr 1
    ring
  have hTwo : ‖(2 : ℚ_[37])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have hdenNorm : ‖(2 : ℚ_[37]) * y‖ < 1 := by
    rw [norm_mul, hTwo, one_mul]
    exact hyNorm
  have hden0 : (2 : ℚ_[37]) * y ≠ 0 :=
    mul_ne_zero (by norm_num) hy0
  rw [hslope, norm_div, hDerivative]
  have hpos : 0 < ‖(2 : ℚ_[37]) * y‖ :=
    norm_pos_iff.mpr hden0
  simpa only [one_div] using
    (one_lt_inv₀ hpos).2 hdenNorm

/-- On an integral two-torsion model, a slope of norm greater than one forces
the resulting addition abscissa into the infinity chart. -/
theorem norm_addX_gt_one_of_integral_of_norm_slope_gt_one
    (A B : ℤ_[37])
    {x₁ x₂ ℓ : ℚ_[37]}
    (hx₁ : ‖x₁‖ ≤ 1) (hx₂ : ‖x₂‖ ≤ 1)
    (hℓ : 1 < ‖ℓ‖) :
    1 <
      ‖(localPadicCurve A B).toAffine.addX x₁ x₂ ℓ‖ := by
  have hA : ‖(A : ℚ_[37])‖ ≤ 1 := A.property
  have hsmall :
      ‖(A : ℚ_[37]) + x₁ + x₂‖ ≤ 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    apply max_le
    · exact
        (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le hA hx₁)
    · exact hx₂
  have hℓsq : 1 < ‖ℓ ^ 2‖ := by
    rw [norm_pow]
    nlinarith [norm_nonneg ℓ]
  calc
    1 < ‖ℓ ^ 2‖ := hℓsq
    _ = ‖ℓ ^ 2 - ((A : ℚ_[37]) + x₁ + x₂)‖ :=
      (norm_sub_eq_left_of_lt (hsmall.trans_lt hℓsq)).symm
    _ =
        ‖(localPadicCurve A B).toAffine.addX x₁ x₂ ℓ‖ := by
      congr 1
      simp only [localPadicCurve, localCurve, WeierstrassCurve.map,
        WeierstrassCurve.Affine.addX, map_zero, zero_mul, add_zero]
      rw [show PadicInt.Coe.ringHom A = (A : ℚ_[37]) by rfl]
      ring

/-- Two integral affine points with the same executable reduction differ by a
point in the infinity fibre.  The proof treats ordinary residue points by a
secant estimate and residue two-torsion points by the tangent estimate. -/
theorem finiteReducePoint_sub_eq_none_of_integral_eq
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {x₁ y₁ x₂ y₂ : ℚ_[37]}
    (h₁ : (localPadicCurve A B).toAffine.Nonsingular x₁ y₁)
    (h₂ : (localPadicCurve A B).toAffine.Nonsingular x₂ y₂)
    (hx₁ : ‖x₁‖ ≤ 1) (hx₂ : ‖x₂‖ ≤ 1)
    (hred :
      finiteReducePoint A B (.some x₁ y₁ h₁) =
        finiteReducePoint A B (.some x₂ y₂ h₂)) :
    finiteReducePoint A B
        ((.some x₁ y₁ h₁ : (localPadicCurve A B).toAffine.Point) -
          .some x₂ y₂ h₂) = none := by
  by_cases hsame : x₁ = x₂ ∧ y₁ = y₂
  · rcases hsame with ⟨rfl, rfl⟩
    rw [sub_self, finiteReducePoint_zero]
  · have hnot :
        ¬(x₁ = x₂ ∧
          y₁ =
            (localPadicCurve A B).toAffine.negY x₂
              ((localPadicCurve A B).toAffine.negY x₂ y₂)) := by
      intro h
      apply hsame
      exact
        ⟨h.1, by
          simpa only [WeierstrassCurve.Affine.negY_negY] using h.2⟩
    have hslope :
        1 <
          ‖(localPadicCurve A B).toAffine.slope x₁ x₂ y₁
            ((localPadicCurve A B).toAffine.negY x₂ y₂)‖ := by
      by_cases hxNe : x₁ ≠ x₂
      · have hsecant :=
          norm_difference_secant_slope_gt_one_of_X_ne
            A B h₁ h₂ hx₁ hx₂ hred hxNe
        rw [WeierstrassCurve.Affine.slope_of_X_ne hxNe]
        simpa only [localPadicCurve, localCurve, WeierstrassCurve.map,
          WeierstrassCurve.Affine.negY, map_zero, zero_mul, sub_zero,
          sub_neg_eq_add] using hsecant
      · have hxEq : x₁ = x₂ := not_ne_iff.mp hxNe
        subst x₂
        have hyNe : y₁ ≠ y₂ := by
          intro hyEq
          exact hsame ⟨rfl, hyEq⟩
        have hEq₁ := local_curve_equation A B h₁
        have hEq₂ := local_curve_equation A B h₂
        have hprod : (y₁ - y₂) * (y₁ + y₂) = 0 := by
          linear_combination hEq₁ - hEq₂
        have hsum : y₁ + y₂ = 0 :=
          (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hyNe)
        have hy₂ : y₂ = -y₁ := by
          linear_combination hsum
        obtain ⟨_hxDiff, hyDiff⟩ :=
          norm_coordinate_sub_lt_one_of_finiteReducePoint_eq
            A B h₁ h₂ hx₁ hx₂ hred
        have hTwo : ‖(2 : ℚ_[37])‖ = 1 :=
          Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
        have hyNorm : ‖y₁‖ < 1 := by
          have htwoY : ‖(2 : ℚ_[37]) * y₁‖ < 1 := by
            calc
              ‖(2 : ℚ_[37]) * y₁‖ = ‖y₁ - y₂‖ := by
                congr 1
                rw [hy₂]
                ring
              _ < 1 := hyDiff
          rw [norm_mul, hTwo, one_mul] at htwoY
          exact htwoY
        have hy0 : y₁ ≠ 0 := by
          intro hyZero
          apply hyNe
          rw [hyZero, neg_zero] at hy₂
          exact hyZero.trans hy₂.symm
        let y₁Int : ℤ_[37] :=
          ⟨y₁, norm_y_le_one_of_norm_x_le_one A B h₁.1 hx₁⟩
        have hyRed : PadicInt.toZMod y₁Int = 0 := by
          have h :=
            toZMod_eq_of_norm_coe_sub_lt_one y₁Int 0
              (by simpa [y₁Int] using hyNorm)
          simpa using h
        have htangent :=
          norm_tangent_slope_gt_one_of_residue_y_zero
            A B h₁ hx₁ hy0 (by simpa only [y₁Int] using hyRed)
        have hneg :
            (localPadicCurve A B).toAffine.negY x₁ y₂ = y₁ := by
          simp only [localPadicCurve, localCurve, WeierstrassCurve.map,
            WeierstrassCurve.Affine.negY, map_zero, zero_mul, sub_zero]
          rw [hy₂, neg_neg]
        rw [hneg]
        exact htangent
    have hxAdd :
        1 <
          ‖(localPadicCurve A B).toAffine.addX x₁ x₂
            ((localPadicCurve A B).toAffine.slope x₁ x₂ y₁
              ((localPadicCurve A B).toAffine.negY x₂ y₂))‖ :=
      norm_addX_gt_one_of_integral_of_norm_slope_gt_one
        A B hx₁ hx₂ hslope
    rw [sub_eq_add_neg, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.add_some hnot]
    exact
      finiteReducePoint_eq_none_of_norm_x_gt_one A B
        (WeierstrassCurve.Affine.nonsingular_add h₁
          ((WeierstrassCurve.Affine.nonsingular_neg x₂ y₂).mpr h₂)
          hnot)
        hxAdd

/-- For an integral affine point `Q=(u,v)` and an infinity-disk point
`S=(x,y)`, both secant differences are dominated by the coordinates of `S`,
and the squared norm of the secant slope is exactly `‖x‖`.

These are the dominant-term estimates needed before the final leading-term
cancellation proving that `Q+S` has the same reduction as `Q`.
-/
theorem mixed_secant_norms
    (A B : ℤ_[37])
    {u v x y : ℚ_[37]}
    (hQ : (localPadicCurve A B).toAffine.Nonsingular u v)
    (hS : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hu : ‖u‖ ≤ 1)
    (hx : 1 < ‖x‖) :
    ‖u - x‖ = ‖x‖ ∧
      ‖v - y‖ = ‖y‖ ∧
      ‖(v - y) / (u - x)‖ ^ 2 = ‖x‖ := by
  have hv : ‖v‖ ≤ 1 :=
    norm_y_le_one_of_norm_x_le_one A B hQ.1 hu
  have hySq := norm_y_sq_eq_norm_x_cube A B hS hx
  have hy : 1 < ‖y‖ := by
    by_contra h
    have hyLe : ‖y‖ ≤ 1 := le_of_not_gt h
    have hySqLe : ‖y‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg y]
    have hxCubeGt : 1 < ‖x‖ ^ 3 :=
      one_lt_pow₀ hx (by norm_num)
    rw [hySq] at hySqLe
    exact (not_lt_of_ge hySqLe) hxCubeGt
  have hux : ‖u - x‖ = ‖x‖ :=
    norm_sub_eq_right_of_lt (lt_of_le_of_lt hu hx)
  have hvy : ‖v - y‖ = ‖y‖ :=
    norm_sub_eq_right_of_lt (lt_of_le_of_lt hv hy)
  refine ⟨hux, hvy, ?_⟩
  rw [norm_div, hvy, hux, div_pow, hySq]
  field_simp [show ‖x‖ ≠ 0 by
    exact ne_of_gt (lt_trans (by norm_num) hx)]

/-! ## Exact leading cancellation in the mixed secant -/

/-- The integral tail left after cancelling the two leading terms in the
mixed secant abscissa. -/
def mixedXTranslationTail
    (A B u v r t : ℚ_[37]) : ℚ_[37] :=
  (B + 2 * A * u + 3 * u ^ 2 + 2 * A * v * t + v ^ 2 * t ^ 2) +
    r * (2 * B * v * t + A * v ^ 2 * t ^ 2 -
      u ^ 2 * (A + 2 * u)) +
    r ^ 2 * (B * v ^ 2 * t ^ 2)

private theorem mixed_x_numerator_factor
    (A B u v r t : ℚ_[37]) :
    (1 + A * r + B * r ^ 2) * (1 + v * r * t) ^ 2 -
          (1 - u * r) ^ 2 -
          r * (1 - u * r) ^ 2 * (A + 2 * u) =
      r * (2 * v * t + r * mixedXTranslationTail A B u v r t) := by
  simp only [mixedXTranslationTail]
  ring

/-- Exact cancellation formula for the abscissa obtained by translating an
integral point `(u,v)` by a formal point with coordinates
`r=1/x`, `t=-x/y`.

The left side is `x(Q+S)-u` after substituting the secant slope.
-/
theorem formal_mixed_translated_x_sub
    (A B u v r t : ℚ_[37])
    (hr : r = t ^ 2 * (1 + A * r + B * r ^ 2))
    (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hden : 1 - u * r ≠ 0) :
    (-(1 + v * r * t) / (t * (1 - u * r))) ^ 2 -
          A - u - r⁻¹ - u =
      (2 * v * t + r * mixedXTranslationTail A B u v r t) /
        (1 - u * r) ^ 2 := by
  let C : ℚ_[37] := 1 + A * r + B * r ^ 2
  let q : ℚ_[37] := 1 + v * r * t
  let d : ℚ_[37] := 1 - u * r
  have hd0 : d ≠ 0 := by simpa [d] using hden
  have hsquare :
      (-q / (t * d)) ^ 2 =
        C * q ^ 2 / (r * d ^ 2) := by
    rw [div_pow]
    apply (div_eq_div_iff
      (pow_ne_zero 2 (mul_ne_zero ht0 hd0))
      (mul_ne_zero hr0 (pow_ne_zero 2 hd0))).mpr
    simp only [neg_sq]
    dsimp [C]
    linear_combination q ^ 2 * d ^ 2 * hr
  have hfactor := mixed_x_numerator_factor A B u v r t
  change
    (-q / (t * d)) ^ 2 - A - u - r⁻¹ - u =
      (2 * v * t + r * mixedXTranslationTail A B u v r t) /
        d ^ 2
  rw [hsquare]
  field_simp [hr0, hd0]
  dsimp [C, q, d]
  linear_combination hfactor

/-- The tail in the mixed abscissa identity is integral whenever all its
arguments are 37-adic integers. -/
theorem norm_mixedXTranslationTail_le_one
    (A B u v r t : ℤ_[37]) :
    ‖mixedXTranslationTail (A : ℚ_[37]) (B : ℚ_[37])
        (u : ℚ_[37]) (v : ℚ_[37]) (r : ℚ_[37]) (t : ℚ_[37])‖ ≤ 1 := by
  let H : ℤ_[37] :=
    (B + 2 * A * u + 3 * u ^ 2 + 2 * A * v * t + v ^ 2 * t ^ 2) +
      r * (2 * B * v * t + A * v ^ 2 * t ^ 2 -
        u ^ 2 * (A + 2 * u)) +
      r ^ 2 * (B * v ^ 2 * t ^ 2)
  have hH :
      (H : ℚ_[37]) =
        mixedXTranslationTail (A : ℚ_[37]) (B : ℚ_[37])
          (u : ℚ_[37]) (v : ℚ_[37]) (r : ℚ_[37])
          (t : ℚ_[37]) := by
    simp only [H, mixedXTranslationTail, PadicInt.coe_add,
      PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow]
    norm_cast
  rw [← hH]
  exact H.property

/-- The integral tail left after cancelling the leading term in the ordinate
of a mixed integral/formal sum. -/
def mixedYTranslationTail
    (A B u v r t : ℚ_[37]) : ℚ_[37] :=
  (1 + A * r + B * r ^ 2) *
    (2 * v * t *
        (v * t + 3 * u - 3 * u ^ 2 * r + u ^ 3 * r ^ 2) +
      (1 + v * r * t) * mixedXTranslationTail A B u v r t)

/-- Exact cancellation formula for the ordinate obtained by translating an
integral point `(u,v)` by a formal point with coordinates
`r=1/x`, `t=-x/y`.

The left side is `y(Q+S)-v` after substituting the secant slope and the
translated-abscissa identity.
-/
theorem formal_mixed_translated_y_sub
    (A B u v r t : ℚ_[37])
    (hr : r = t ^ 2 * (1 + A * r + B * r ^ 2))
    (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hden : 1 - u * r ≠ 0) :
    -(-(1 + v * r * t) / (t * (1 - u * r))) *
          ((-(1 + v * r * t) / (t * (1 - u * r))) ^ 2 -
            A - u - r⁻¹ - u) -
        2 * v =
      t * mixedYTranslationTail A B u v r t /
        (1 - u * r) ^ 3 := by
  let q : ℚ_[37] := 1 + v * r * t
  let d : ℚ_[37] := 1 - u * r
  let H : ℚ_[37] := mixedXTranslationTail A B u v r t
  let N : ℚ_[37] := 2 * v * t + r * H
  let K : ℚ_[37] := mixedYTranslationTail A B u v r t
  let C : ℚ_[37] := 1 + A * r + B * r ^ 2
  let J : ℚ_[37] :=
    v * t + 3 * u - 3 * u ^ 2 * r + u ^ 3 * r ^ 2
  have hd0 : d ≠ 0 := by simpa only [d] using hden
  have hxIdentity :
      (-(1 + v * r * t) / (t * (1 - u * r))) ^ 2 -
            A - u - r⁻¹ - u =
        N / d ^ 2 := by
    simpa only [N, H, d] using
      formal_mixed_translated_x_sub A B u v r t hr hr0 ht0 hden
  have hfactor :
      q * N - 2 * v * t * d ^ 3 = t ^ 2 * K := by
    have hpoly :
        q * N - 2 * v * t * d ^ 3 =
          r * (2 * v * t * J + q * H) := by
      dsimp only [q, N, d, J]
      ring
    calc
      q * N - 2 * v * t * d ^ 3 =
          r * (2 * v * t * J + q * H) := hpoly
      _ = (t ^ 2 * C) * (2 * v * t * J + q * H) :=
        congrArg (fun z => z * (2 * v * t * J + q * H)) <| by
          simpa only [C] using hr
      _ = t ^ 2 * (C * (2 * v * t * J + q * H)) := by ring
      _ = t ^ 2 * K := by rfl
  rw [hxIdentity]
  change -(-q / (t * d)) * (N / d ^ 2) - 2 * v =
    t * K / d ^ 3
  calc
    -(-q / (t * d)) * (N / d ^ 2) - 2 * v =
        (q * N - 2 * v * t * d ^ 3) / (t * d ^ 3) := by
          field_simp [ht0, hd0]
    _ = t ^ 2 * K / (t * d ^ 3) := by rw [hfactor]
    _ = t * K / d ^ 3 := by
      field_simp [ht0, hd0]

/-- The tail in the mixed ordinate identity is integral whenever all its
arguments are 37-adic integers. -/
theorem norm_mixedYTranslationTail_le_one
    (A B u v r t : ℤ_[37]) :
    ‖mixedYTranslationTail (A : ℚ_[37]) (B : ℚ_[37])
        (u : ℚ_[37]) (v : ℚ_[37]) (r : ℚ_[37]) (t : ℚ_[37])‖ ≤ 1 := by
  let H : ℤ_[37] :=
    (1 + A * r + B * r ^ 2) *
      (2 * v * t *
          (v * t + 3 * u - 3 * u ^ 2 * r + u ^ 3 * r ^ 2) +
        (1 + v * r * t) *
          ((B + 2 * A * u + 3 * u ^ 2 + 2 * A * v * t +
              v ^ 2 * t ^ 2) +
            r * (2 * B * v * t + A * v ^ 2 * t ^ 2 -
              u ^ 2 * (A + 2 * u)) +
            r ^ 2 * (B * v ^ 2 * t ^ 2)))
  have hH :
      (H : ℚ_[37]) =
        mixedYTranslationTail (A : ℚ_[37]) (B : ℚ_[37])
          (u : ℚ_[37]) (v : ℚ_[37]) (r : ℚ_[37])
          (t : ℚ_[37]) := by
    simp only [H, mixedYTranslationTail, mixedXTranslationTail,
      PadicInt.coe_add, PadicInt.coe_sub, PadicInt.coe_mul,
      PadicInt.coe_pow]
    norm_cast
  rw [← hH]
  exact H.property

/-- Rewriting a mixed secant slope in the integral formal coordinates
`r=1/x` and `t=-x/y`. -/
theorem mixed_secant_slope_eq_formal
    (u v x y : ℚ_[37])
    (hx : x ≠ 0) (hy : y ≠ 0) (hux : u ≠ x) :
    (v - y) / (u - x) =
      -(1 + v * x⁻¹ * (-x / y)) /
        ((-x / y) * (1 - u * x⁻¹)) := by
  field_simp [hx, hy, hux]
  ring

/-- In the mixed integral/infinity case, the abscissa produced by the
secant-and-tangent formula is congruent to the integral input abscissa.

This closes the leading cancellation left open by `mixed_secant_norms`.
-/
theorem norm_mixed_translated_x_sub_lt_one
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {u v x y : ℚ_[37]}
    (hQ : (localPadicCurve A B).toAffine.Nonsingular u v)
    (hS : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hu : ‖u‖ ≤ 1)
    (hredS : finiteReducePoint A B (.some x y hS) = none) :
    ‖((v - y) / (u - x)) ^ 2 - (A : ℚ_[37]) - u - x - u‖ < 1 := by
  have hxNorm :=
    norm_x_gt_one_of_finiteReducePoint_eq_none A B hS hredS
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, norm_zero] at hxNorm
    norm_num at hxNorm
  have hySq := norm_y_sq_eq_norm_x_cube A B hS hxNorm
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0, norm_zero, zero_pow (by norm_num)] at hySq
    have hxCubePos : 0 < ‖x‖ ^ 3 :=
      pow_pos (lt_trans (by norm_num) hxNorm) _
    exact (ne_of_gt hxCubePos) hySq.symm
  have hux : u ≠ x := by
    intro h
    subst x
    linarith
  obtain ⟨t, r, ht, hr, htRed, hrRed, hformal⟩ :=
    GaussianFormalLocal.exists_integral_formal_parameters
      A B hS hredS
  have htNorm : ‖(t : ℚ_[37])‖ < 1 :=
    norm_coe_lt_one_of_toZMod_eq_zero t htRed
  have hrNorm : ‖(r : ℚ_[37])‖ < 1 :=
    norm_coe_lt_one_of_toZMod_eq_zero r hrRed
  have hv : ‖v‖ ≤ 1 :=
    norm_y_le_one_of_norm_x_le_one A B hQ.1 hu
  let uInt : ℤ_[37] := ⟨u, hu⟩
  let vInt : ℤ_[37] := ⟨v, hv⟩
  have hurNorm : ‖u * (r : ℚ_[37])‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg u, norm_nonneg (r : ℚ_[37])]
  have hden : 1 - u * (r : ℚ_[37]) ≠ 0 := by
    intro hzero
    have hone : (1 : ℚ_[37]) = u * (r : ℚ_[37]) :=
      sub_eq_zero.mp hzero
    rw [← hone, norm_one] at hurNorm
    exact (lt_irrefl 1) hurNorm
  have hr0 : (r : ℚ_[37]) ≠ 0 := by
    rw [hr]
    exact inv_ne_zero hx
  have ht0 : (t : ℚ_[37]) ≠ 0 := by
    rw [ht]
    exact div_ne_zero (neg_ne_zero.mpr hx) hy
  have hrInv : ((r : ℚ_[37]))⁻¹ = x := by
    rw [hr]
    exact inv_inv x
  have hslope :
      (v - y) / (u - x) =
        -(1 + v * (r : ℚ_[37]) * (t : ℚ_[37])) /
          ((t : ℚ_[37]) * (1 - u * (r : ℚ_[37]))) := by
    rw [hr, ht]
    exact mixed_secant_slope_eq_formal u v x y hx hy hux
  have hxIdentity :=
    formal_mixed_translated_x_sub
      (A : ℚ_[37]) (B : ℚ_[37]) u v (r : ℚ_[37])
        (t : ℚ_[37]) hformal hr0 ht0 hden
  have hTail :
      ‖mixedXTranslationTail (A : ℚ_[37]) (B : ℚ_[37])
          u v (r : ℚ_[37]) (t : ℚ_[37])‖ ≤ 1 := by
    simpa only [uInt, vInt] using
      norm_mixedXTranslationTail_le_one A B uInt vInt r t
  have hTwo : ‖(2 : ℚ_[37])‖ ≤ 1 :=
    show ‖((2 : ℤ_[37]) : ℚ_[37])‖ ≤ 1 from
      (2 : ℤ_[37]).property
  have hFirst : ‖(2 : ℚ_[37]) * v * (t : ℚ_[37])‖ < 1 := by
    simp only [norm_mul]
    have hTwoV : ‖(2 : ℚ_[37])‖ * ‖v‖ ≤ 1 := by
      calc
        ‖(2 : ℚ_[37])‖ * ‖v‖ ≤ 1 * ‖v‖ :=
          mul_le_mul_of_nonneg_right hTwo (norm_nonneg v)
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hv (by norm_num)
        _ = 1 := by norm_num
    calc
      (‖(2 : ℚ_[37])‖ * ‖v‖) * ‖(t : ℚ_[37])‖ ≤
          1 * ‖(t : ℚ_[37])‖ :=
        mul_le_mul_of_nonneg_right hTwoV (norm_nonneg (t : ℚ_[37]))
      _ < 1 := by simpa using htNorm
  have hSecond :
      ‖(r : ℚ_[37]) *
          mixedXTranslationTail (A : ℚ_[37]) (B : ℚ_[37])
            u v (r : ℚ_[37]) (t : ℚ_[37])‖ < 1 := by
    rw [norm_mul]
    calc
      ‖(r : ℚ_[37])‖ *
          ‖mixedXTranslationTail (A : ℚ_[37]) (B : ℚ_[37])
            u v (r : ℚ_[37]) (t : ℚ_[37])‖ ≤
          ‖(r : ℚ_[37])‖ * 1 :=
        mul_le_mul_of_nonneg_left hTail (norm_nonneg (r : ℚ_[37]))
      _ < 1 := by simpa using hrNorm
  have hNumerator :
      ‖(2 : ℚ_[37]) * v * (t : ℚ_[37]) +
          (r : ℚ_[37]) *
            mixedXTranslationTail (A : ℚ_[37]) (B : ℚ_[37])
              u v (r : ℚ_[37]) (t : ℚ_[37])‖ < 1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt hFirst hSecond)
  have hdenNorm : ‖1 - u * (r : ℚ_[37])‖ = 1 := by
    calc
      ‖1 - u * (r : ℚ_[37])‖ =
          ‖(1 : ℚ_[37]) + -(u * (r : ℚ_[37]))‖ := by
            rw [sub_eq_add_neg]
      _ = max ‖(1 : ℚ_[37])‖ ‖-(u * (r : ℚ_[37]))‖ :=
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
          (by simpa only [norm_one, norm_neg] using ne_of_gt hurNorm)
      _ = max 1 ‖u * (r : ℚ_[37])‖ := by
        rw [norm_one, norm_neg]
      _ = 1 := max_eq_left hurNorm.le
  calc
    ‖((v - y) / (u - x)) ^ 2 - (A : ℚ_[37]) - u - x - u‖ =
        ‖(-(1 + v * (r : ℚ_[37]) * (t : ℚ_[37])) /
              ((t : ℚ_[37]) * (1 - u * (r : ℚ_[37])))) ^ 2 -
            (A : ℚ_[37]) - u - (r : ℚ_[37])⁻¹ - u‖ := by
          rw [hslope, hrInv]
    _ = ‖((2 : ℚ_[37]) * v * (t : ℚ_[37]) +
              (r : ℚ_[37]) *
                mixedXTranslationTail (A : ℚ_[37]) (B : ℚ_[37])
                  u v (r : ℚ_[37]) (t : ℚ_[37])) /
            (1 - u * (r : ℚ_[37])) ^ 2‖ := by
          rw [hxIdentity]
    _ < 1 := by
      rw [norm_div, norm_pow, hdenNorm]
      simpa only [one_pow, div_one] using hNumerator

/-- In the mixed integral/infinity case, the ordinate produced by the
secant-and-tangent formula is congruent to the integral input ordinate.

Together with `norm_mixed_translated_x_sub_lt_one`, this proves both affine
coordinate cancellations needed for mixed reduction.
-/
theorem norm_mixed_translated_y_sub_lt_one
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {u v x y : ℚ_[37]}
    (hQ : (localPadicCurve A B).toAffine.Nonsingular u v)
    (hS : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hu : ‖u‖ ≤ 1)
    (hredS : finiteReducePoint A B (.some x y hS) = none) :
    ‖-((v - y) / (u - x)) *
          (((v - y) / (u - x)) ^ 2 -
            (A : ℚ_[37]) - u - x - u) -
        2 * v‖ < 1 := by
  have hxNorm :=
    norm_x_gt_one_of_finiteReducePoint_eq_none A B hS hredS
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, norm_zero] at hxNorm
    norm_num at hxNorm
  have hySq := norm_y_sq_eq_norm_x_cube A B hS hxNorm
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0, norm_zero, zero_pow (by norm_num)] at hySq
    have hxCubePos : 0 < ‖x‖ ^ 3 :=
      pow_pos (lt_trans (by norm_num) hxNorm) _
    exact (ne_of_gt hxCubePos) hySq.symm
  have hux : u ≠ x := by
    intro h
    subst x
    linarith
  obtain ⟨t, r, ht, hr, htRed, hrRed, hformal⟩ :=
    GaussianFormalLocal.exists_integral_formal_parameters
      A B hS hredS
  have htNorm : ‖(t : ℚ_[37])‖ < 1 :=
    norm_coe_lt_one_of_toZMod_eq_zero t htRed
  have hrNorm : ‖(r : ℚ_[37])‖ < 1 :=
    norm_coe_lt_one_of_toZMod_eq_zero r hrRed
  have hv : ‖v‖ ≤ 1 :=
    norm_y_le_one_of_norm_x_le_one A B hQ.1 hu
  let uInt : ℤ_[37] := ⟨u, hu⟩
  let vInt : ℤ_[37] := ⟨v, hv⟩
  have hurNorm : ‖u * (r : ℚ_[37])‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg u, norm_nonneg (r : ℚ_[37])]
  have hden : 1 - u * (r : ℚ_[37]) ≠ 0 := by
    intro hzero
    have hone : (1 : ℚ_[37]) = u * (r : ℚ_[37]) :=
      sub_eq_zero.mp hzero
    rw [← hone, norm_one] at hurNorm
    exact (lt_irrefl 1) hurNorm
  have hr0 : (r : ℚ_[37]) ≠ 0 := by
    rw [hr]
    exact inv_ne_zero hx
  have ht0 : (t : ℚ_[37]) ≠ 0 := by
    rw [ht]
    exact div_ne_zero (neg_ne_zero.mpr hx) hy
  have hrInv : ((r : ℚ_[37]))⁻¹ = x := by
    rw [hr]
    exact inv_inv x
  have hslope :
      (v - y) / (u - x) =
        -(1 + v * (r : ℚ_[37]) * (t : ℚ_[37])) /
          ((t : ℚ_[37]) * (1 - u * (r : ℚ_[37]))) := by
    rw [hr, ht]
    exact mixed_secant_slope_eq_formal u v x y hx hy hux
  have hyIdentity :=
    formal_mixed_translated_y_sub
      (A : ℚ_[37]) (B : ℚ_[37]) u v (r : ℚ_[37])
        (t : ℚ_[37]) hformal hr0 ht0 hden
  have hTail :
      ‖mixedYTranslationTail (A : ℚ_[37]) (B : ℚ_[37])
          u v (r : ℚ_[37]) (t : ℚ_[37])‖ ≤ 1 := by
    simpa only [uInt, vInt] using
      norm_mixedYTranslationTail_le_one A B uInt vInt r t
  have hNumerator :
      ‖(t : ℚ_[37]) *
          mixedYTranslationTail (A : ℚ_[37]) (B : ℚ_[37])
            u v (r : ℚ_[37]) (t : ℚ_[37])‖ < 1 := by
    rw [norm_mul]
    calc
      ‖(t : ℚ_[37])‖ *
          ‖mixedYTranslationTail (A : ℚ_[37]) (B : ℚ_[37])
            u v (r : ℚ_[37]) (t : ℚ_[37])‖ ≤
          ‖(t : ℚ_[37])‖ * 1 :=
        mul_le_mul_of_nonneg_left hTail (norm_nonneg (t : ℚ_[37]))
      _ < 1 := by simpa using htNorm
  have hdenNorm : ‖1 - u * (r : ℚ_[37])‖ = 1 := by
    calc
      ‖1 - u * (r : ℚ_[37])‖ =
          ‖(1 : ℚ_[37]) + -(u * (r : ℚ_[37]))‖ := by
            rw [sub_eq_add_neg]
      _ = max ‖(1 : ℚ_[37])‖ ‖-(u * (r : ℚ_[37]))‖ :=
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
          (by simpa only [norm_one, norm_neg] using ne_of_gt hurNorm)
      _ = max 1 ‖u * (r : ℚ_[37])‖ := by
        rw [norm_one, norm_neg]
      _ = 1 := max_eq_left hurNorm.le
  calc
    ‖-((v - y) / (u - x)) *
          (((v - y) / (u - x)) ^ 2 -
            (A : ℚ_[37]) - u - x - u) -
        2 * v‖ =
        ‖-(-(1 + v * (r : ℚ_[37]) * (t : ℚ_[37])) /
              ((t : ℚ_[37]) * (1 - u * (r : ℚ_[37])))) *
            ((-(1 + v * (r : ℚ_[37]) * (t : ℚ_[37])) /
              ((t : ℚ_[37]) * (1 - u * (r : ℚ_[37])))) ^ 2 -
                (A : ℚ_[37]) - u - (r : ℚ_[37])⁻¹ - u) -
            2 * v‖ := by
          rw [hslope, hrInv]
    _ = ‖(t : ℚ_[37]) *
            mixedYTranslationTail (A : ℚ_[37]) (B : ℚ_[37])
              u v (r : ℚ_[37]) (t : ℚ_[37]) /
          (1 - u * (r : ℚ_[37])) ^ 3‖ := by
          rw [hyIdentity]
    _ < 1 := by
      rw [norm_div, norm_pow, hdenNorm]
      simpa only [one_pow, div_one] using hNumerator

/-- Adding an infinity-disk point to an integral affine point preserves the
executable reduction.  This is the complete mixed affine/infinity case of
additivity, with no reduction-homomorphism hypothesis. -/
theorem finiteReducePoint_add_eq_left_of_left_integral_right_none
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {u v x y : ℚ_[37]}
    (hQ : (localPadicCurve A B).toAffine.Nonsingular u v)
    (hS : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hu : ‖u‖ ≤ 1)
    (hredS : finiteReducePoint A B (.some x y hS) = none) :
    finiteReducePoint A B
        ((.some u v hQ : (localPadicCurve A B).toAffine.Point) +
          .some x y hS) =
      finiteReducePoint A B (.some u v hQ) := by
  have hxNorm :=
    norm_x_gt_one_of_finiteReducePoint_eq_none A B hS hredS
  have hux : u ≠ x := by
    intro h
    subst x
    linarith
  have hnot :
      ¬(u = x ∧
        v = (localPadicCurve A B).toAffine.negY x y) :=
    fun h => hux h.1
  have hxDiff :
      ‖(localPadicCurve A B).toAffine.addX u x
            ((localPadicCurve A B).toAffine.slope u x v y) - u‖ < 1 := by
    have h :=
      norm_mixed_translated_x_sub_lt_one A B hQ hS hu hredS
    simp only [WeierstrassCurve.Affine.slope_of_X_ne hux,
      WeierstrassCurve.Affine.addX, localPadicCurve, localCurve,
      WeierstrassCurve.map, map_zero, zero_mul, add_zero]
    rw [show PadicInt.Coe.ringHom A = (A : ℚ_[37]) by rfl]
    exact h
  have hyDiff :
      ‖(localPadicCurve A B).toAffine.addY u x v
            ((localPadicCurve A B).toAffine.slope u x v y) - v‖ < 1 := by
    have h :=
      norm_mixed_translated_y_sub_lt_one A B hQ hS hu hredS
    rw [WeierstrassCurve.Affine.slope_of_X_ne hux]
    simp only [
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX,
      localPadicCurve, localCurve, WeierstrassCurve.map, map_zero,
      zero_mul, add_zero, sub_zero]
    rw [show PadicInt.Coe.ringHom A = (A : ℚ_[37]) by rfl]
    convert h using 1
    ring_nf
  have hxSum :
      ‖(localPadicCurve A B).toAffine.addX u x
          ((localPadicCurve A B).toAffine.slope u x v y)‖ ≤ 1 := by
    calc
      ‖(localPadicCurve A B).toAffine.addX u x
          ((localPadicCurve A B).toAffine.slope u x v y)‖ =
          ‖((localPadicCurve A B).toAffine.addX u x
              ((localPadicCurve A B).toAffine.slope u x v y) - u) +
            u‖ := by
              congr 1
              ring
      _ ≤
          max
            ‖(localPadicCurve A B).toAffine.addX u x
                ((localPadicCurve A B).toAffine.slope u x v y) - u‖
            ‖u‖ :=
        IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le hxDiff.le hu
  rw [WeierstrassCurve.Affine.Point.add_some hnot]
  exact finiteReducePoint_eq_of_norm_coordinate_sub_lt_one
    A B
    (WeierstrassCurve.Affine.nonsingular_add hQ hS hnot) hQ
    hxSum hu hxDiff hyDiff

/-- Translation by an infinity-disk point fixes every non-infinity reduction.
This packages the zero/affine case split around the mixed-coordinate theorem;
the excluded case is exactly addition of two points in the infinity disk. -/
theorem finiteReducePoint_add_eq_left_of_right_none_left_ne_none
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (Q S : (localPadicCurve A B).toAffine.Point)
    (hredS : finiteReducePoint A B S = none)
    (hredQ : finiteReducePoint A B Q ≠ none) :
    finiteReducePoint A B (Q + S) = finiteReducePoint A B Q := by
  rcases Q with (_ | ⟨u, v, hQ⟩)
  · exact (hredQ (finiteReducePoint_zero A B)).elim
  · rcases S with (_ | ⟨x, y, hS⟩)
    · rfl
    · have hu : ‖u‖ ≤ 1 := by
        by_contra hu
        apply hredQ
        exact finiteReducePoint_eq_none_of_norm_x_gt_one A B hQ
          (lt_of_not_ge hu)
      exact
        finiteReducePoint_add_eq_left_of_left_integral_right_none
          A B hQ hS hu hredS

/-- The infinity fibre is closed under addition.  The proof avoids a second
equal-valuation calculation: if `P+S` reduced affinely, translating that
affine reduction by the kernel point `-S` would preserve it by the mixed
theorem, whereas group cancellation gives back the kernel point `P`. -/
theorem finiteReducePoint_add_eq_none_of_eq_none
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P S : (localPadicCurve A B).toAffine.Point)
    (hredP : finiteReducePoint A B P = none)
    (hredS : finiteReducePoint A B S = none) :
    finiteReducePoint A B (P + S) = none := by
  by_contra hredSum
  have hredNegS : finiteReducePoint A B (-S) = none :=
    (finiteReducePoint_neg_eq_none_iff A B S).2 hredS
  have htranslate :=
    finiteReducePoint_add_eq_left_of_right_none_left_ne_none
      A B (P + S) (-S) hredNegS hredSum
  have hcancel : (P + S) + -S = P := by
    abel
  rw [hcancel, hredP] at htranslate
  exact hredSum htranslate.symm

/-- Translation by any point in the infinity fibre preserves executable
reduction, for an arbitrary point `Q`. -/
theorem finiteReducePoint_add_eq_left_of_right_eq_none
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (Q S : (localPadicCurve A B).toAffine.Point)
    (hredS : finiteReducePoint A B S = none) :
    finiteReducePoint A B (Q + S) = finiteReducePoint A B Q := by
  by_cases hredQ : finiteReducePoint A B Q = none
  · rw [hredQ]
    exact finiteReducePoint_add_eq_none_of_eq_none
      A B Q S hredQ hredS
  · exact
      finiteReducePoint_add_eq_left_of_right_none_left_ne_none
        A B Q S hredS hredQ

/-- The converse fibre theorem: two arbitrary local points with the same
executable reduction differ by a point in the infinity fibre. -/
theorem finiteReducePoint_sub_eq_none_of_eq
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P Q : (localPadicCurve A B).toAffine.Point)
    (hred : finiteReducePoint A B P = finiteReducePoint A B Q) :
    finiteReducePoint A B (P - Q) = none := by
  by_cases hredP : finiteReducePoint A B P = none
  · have hredQ : finiteReducePoint A B Q = none :=
      hred.symm.trans hredP
    have hredNegQ : finiteReducePoint A B (-Q) = none :=
      (finiteReducePoint_neg_eq_none_iff A B Q).2 hredQ
    simpa only [sub_eq_add_neg] using
      finiteReducePoint_add_eq_none_of_eq_none
        A B P (-Q) hredP hredNegQ
  · have hredQ : finiteReducePoint A B Q ≠ none := by
      intro hQ
      exact hredP (hred.trans hQ)
    rcases P with (_ | ⟨x₁, y₁, h₁⟩)
    · exact (hredP (finiteReducePoint_zero A B)).elim
    · rcases Q with (_ | ⟨x₂, y₂, h₂⟩)
      · exact (hredQ (finiteReducePoint_zero A B)).elim
      · have hx₁ : ‖x₁‖ ≤ 1 := by
          by_contra hx
          apply hredP
          exact finiteReducePoint_eq_none_of_norm_x_gt_one
            A B h₁ (lt_of_not_ge hx)
        have hx₂ : ‖x₂‖ ≤ 1 := by
          by_contra hx
          apply hredQ
          exact finiteReducePoint_eq_none_of_norm_x_gt_one
            A B h₂ (lt_of_not_ge hx)
        exact finiteReducePoint_sub_eq_none_of_integral_eq
          A B h₁ h₂ hx₁ hx₂ hred

/-- The actual infinity fibre, packaged as an additive subgroup of the local
elliptic-curve group. -/
def infinityKernel
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic] :
    AddSubgroup ((localPadicCurve A B).toAffine.Point) where
  carrier := {P | finiteReducePoint A B P = none}
  zero_mem' := finiteReducePoint_zero A B
  add_mem' hP hS :=
    finiteReducePoint_add_eq_none_of_eq_none A B _ _ hP hS
  neg_mem' hP :=
    (finiteReducePoint_neg_eq_none_iff A B _).2 hP

@[simp] theorem mem_infinityKernel_iff
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P : (localPadicCurve A B).toAffine.Point) :
    P ∈ infinityKernel A B ↔ finiteReducePoint A B P = none :=
  Iff.rfl

/-- Executable reduction fibres are exactly cosets of `infinityKernel`. -/
theorem finiteReducePoint_eq_iff_sub_mem_infinityKernel
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    (P Q : (localPadicCurve A B).toAffine.Point) :
    finiteReducePoint A B P = finiteReducePoint A B Q ↔
      P - Q ∈ infinityKernel A B := by
  constructor
  · intro hred
    exact finiteReducePoint_sub_eq_none_of_eq A B P Q hred
  · intro hmem
    have htranslate :=
      finiteReducePoint_add_eq_left_of_right_eq_none
        A B Q (P - Q) hmem
    have hcancel : Q + (P - Q) = P := by
      abel
    rw [hcancel] at htranslate
    exact htranslate

/-- The mixed secant estimates derived directly from the executable
infinity-fibre hypothesis. -/
theorem mixed_secant_norms_of_finiteReducePoint_eq_none
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic]
    {u v x y : ℚ_[37]}
    (hQ : (localPadicCurve A B).toAffine.Nonsingular u v)
    (hS : (localPadicCurve A B).toAffine.Nonsingular x y)
    (hu : ‖u‖ ≤ 1)
    (hredS : finiteReducePoint A B (.some x y hS) = none) :
    ‖u - x‖ = ‖x‖ ∧
      ‖v - y‖ = ‖y‖ ∧
      ‖(v - y) / (u - x)‖ ^ 2 = ‖x‖ :=
  mixed_secant_norms A B hQ hS hu
    (norm_x_gt_one_of_finiteReducePoint_eq_none A B hS hredS)

end

end GaussianFormalKernelDisk
end Cuboid2
