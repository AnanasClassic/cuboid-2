import Cuboid2.QuadraticReduction.GaussianGoodReduction

/-!
# Specialized projective reduction at the split prime above 37

This file begins the missing actual-point reduction bridge.  It constructs
the reduction of an arbitrary point on an integral two-torsion model over
`ℚ_[37]`: points with integral affine abscissa reduce affinely, while the
remaining projective disk reduces to infinity.  The group-law compatibility
needed by `Split37GoodReduction` is proved separately below this normalization
layer.
-/

namespace Cuboid2
namespace GaussianProjectiveReduction

noncomputable section

open GaussianGoodReduction
open GaussianFinite

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : DecidableEq ℚ_[37] := Classical.decEq _

/-- The integral two-torsion model used by both split embeddings. -/
def localCurve (A B : ℤ_[37]) : WeierstrassCurve ℤ_[37] where
  a₁ := 0
  a₂ := A
  a₃ := 0
  a₄ := B
  a₆ := 0

/-- Its generic fibre over `ℚ_[37]`. -/
def localPadicCurve (A B : ℤ_[37]) : WeierstrassCurve ℚ_[37] :=
  (localCurve A B).map PadicInt.Coe.ringHom

/-- Its special fibre over `𝔽₃₇`. -/
def localResidueCurve (A B : ℤ_[37]) : WeierstrassCurve (ZMod 37) :=
  (localCurve A B).map PadicInt.toZMod

/-- On an integral two-torsion model, integral `x` forces integral `y`. -/
theorem norm_y_le_one_of_norm_x_le_one
    (A B : ℤ_[37]) {x y : ℚ_[37]}
    (hcurve : (localPadicCurve A B).toAffine.Equation x y)
    (hx : ‖x‖ ≤ 1) :
    ‖y‖ ≤ 1 := by
  have hEq :
      y ^ 2 =
        x * (x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37])) := by
    have hcurve' := hcurve
    rw [WeierstrassCurve.Affine.equation_iff] at hcurve'
    simp only [localPadicCurve, localCurve, WeierstrassCurve.map,
      map_zero, zero_mul, add_zero, zero_add] at hcurve'
    calc
      y ^ 2 =
          x ^ 3 + (A : ℚ_[37]) * x ^ 2 + (B : ℚ_[37]) * x := hcurve'
      _ = x * (x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37])) := by
        ring
  have hA : ‖(A : ℚ_[37])‖ ≤ 1 := A.property
  have hB : ‖(B : ℚ_[37])‖ ≤ 1 := B.property
  have hx2 : ‖x ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg x]
  have hAx : ‖(A : ℚ_[37]) * x‖ ≤ 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (A : ℚ_[37]), norm_nonneg x]
  have hinner :
      ‖x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37])‖ ≤ 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    apply max_le
    · exact
        (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx2 hAx)
    · exact hB
  have hrhs :
      ‖x * (x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37]))‖ ≤ 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg x,
      norm_nonneg (x ^ 2 + (A : ℚ_[37]) * x + (B : ℚ_[37]))]
  have hy2 : ‖y‖ ^ 2 ≤ 1 := by
    rw [← norm_pow, hEq]
    exact hrhs
  nlinarith [norm_nonneg y]

/-- Reduction of an arbitrary generic-fibre point.  The nonintegral affine
chart is exactly the projective infinity disk. -/
def reducePoint
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic] :
    (localPadicCurve A B).toAffine.Point →
      (localResidueCurve A B).toAffine.Point
  | .zero => 0
  | .some x y hxy =>
      if hx : ‖x‖ ≤ 1 then
        let xInt : ℤ_[37] := ⟨x, hx⟩
        let yInt : ℤ_[37] :=
          ⟨y, norm_y_le_one_of_norm_x_le_one A B hxy.1 hx⟩
        have hInt :
            (localCurve A B).toAffine.Equation xInt yInt := by
          rw [WeierstrassCurve.Affine.equation_iff]
          simp only [localCurve, zero_mul, add_zero]
          apply Subtype.val_injective
          have hcurve := hxy.1
          rw [WeierstrassCurve.Affine.equation_iff] at hcurve
          change
            y ^ 2 =
              x ^ 3 + (A : ℚ_[37]) * x ^ 2 + (B : ℚ_[37]) * x
          have hcurve' :
              y ^ 2 =
                x ^ 3 + PadicInt.Coe.ringHom A * x ^ 2 +
                  PadicInt.Coe.ringHom B * x := by
            simpa only [localPadicCurve, localCurve,
              WeierstrassCurve.map, map_zero, zero_mul, add_zero] using hcurve
          exact hcurve'.trans (by rfl)
        .mk (hInt.map PadicInt.toZMod)
      else
        0

@[simp] theorem reducePoint_zero
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic] :
    reducePoint A B (0 : (localPadicCurve A B).toAffine.Point) = 0 :=
  rfl

/-- Forget the proof carried by a residue-curve point and retain exactly the
canonical finite row representation used by `GaussianP37Bridge`. -/
def finitePointOfResidue
    {W : WeierstrassCurve (ZMod 37)} :
    W.toAffine.Point → FinitePoint
  | .zero => none
  | .some x y _ => some (x.val, y.val)

/-- The executable finite reduction attached to `reducePoint`. -/
def finiteReducePoint
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic] :
    (localPadicCurve A B).toAffine.Point → FinitePoint :=
  fun P => finitePointOfResidue (reducePoint A B P)

@[simp] theorem finiteReducePoint_zero
    (A B : ℤ_[37])
    [hEll : (localResidueCurve A B).IsElliptic] :
    finiteReducePoint A B
      (0 : (localPadicCurve A B).toAffine.Point) = none :=
  rfl

/-- Two integral affine points with the same generic-fibre abscissa have the
same reduced projective abscissa, even when they lie on different integral
two-torsion models. -/
theorem finiteReducePoint_sameX_of_affine_x_eq
    (A₁ B₁ A₂ B₂ : ℤ_[37])
    [hEll₁ : (localResidueCurve A₁ B₁).IsElliptic]
    [hEll₂ : (localResidueCurve A₂ B₂).IsElliptic]
    {x₁ y₁ x₂ y₂ : ℚ_[37]}
    (h₁ : (localPadicCurve A₁ B₁).toAffine.Nonsingular x₁ y₁)
    (h₂ : (localPadicCurve A₂ B₂).toAffine.Nonsingular x₂ y₂)
    (hx : x₁ = x₂) :
    sameX
        (finiteReducePoint A₁ B₁
          (.some x₁ y₁ h₁))
        (finiteReducePoint A₂ B₂
          (.some x₂ y₂ h₂)) = true := by
  subst x₂
  by_cases hxInt : ‖x₁‖ ≤ 1
  · simp [finiteReducePoint, reducePoint, hxInt,
      finitePointOfResidue, WeierstrassCurve.Affine.Point.mk,
      sameX]
  · simp [finiteReducePoint, reducePoint, hxInt,
      finitePointOfResidue, sameX]

/-- Projectively equal generic-fibre abscissae have equal executable reduced
abscissae.  This includes the common infinity chart. -/
theorem finiteReducePoint_sameX_of_xRep_eq
    (A₁ B₁ A₂ B₂ : ℤ_[37])
    [hEll₁ : (localResidueCurve A₁ B₁).IsElliptic]
    [hEll₂ : (localResidueCurve A₂ B₂).IsElliptic]
    (P₁ : (localPadicCurve A₁ B₁).toAffine.Point)
    (P₂ : (localPadicCurve A₂ B₂).toAffine.Point)
    (hx : P₁.xRep = P₂.xRep) :
    sameX (finiteReducePoint A₁ B₁ P₁)
      (finiteReducePoint A₂ B₂ P₂) = true := by
  rcases P₁ with (_ | ⟨x₁, y₁, h₁⟩) <;>
    rcases P₂ with (_ | ⟨x₂, y₂, h₂⟩)
  · rfl
  · simp [WeierstrassCurve.Affine.Point.xRep] at hx
  · simp [WeierstrassCurve.Affine.Point.xRep] at hx
  · apply finiteReducePoint_sameX_of_affine_x_eq
    simpa [WeierstrassCurve.Affine.Point.xRep] using hx

/-! ## The two actual split embeddings -/

/-- The two integral coefficients at the plus prime above `37`. -/
abbrev plusA : ℤ_[37] := gaussianE0IntegralPlus.a₂
abbrev plusB : ℤ_[37] := gaussianE0IntegralPlus.a₄

/-- The two integral coefficients at the minus prime above `37`. -/
abbrev minusA : ℤ_[37] := gaussianE0IntegralMinus.a₂
abbrev minusB : ℤ_[37] := gaussianE0IntegralMinus.a₄

theorem localCurve_plus_eq :
    localCurve plusA plusB = gaussianE0IntegralPlus := by
  rfl

theorem localCurve_minus_eq :
    localCurve minusA minusB = gaussianE0IntegralMinus := by
  rfl

theorem localResidueCurve_plus_eq :
    localResidueCurve plusA plusB = gaussianE0ResiduePlus := by
  rw [localResidueCurve, localCurve_plus_eq]
  rfl

theorem localResidueCurve_minus_eq :
    localResidueCurve minusA minusB = gaussianE0ResidueMinus := by
  rw [localResidueCurve, localCurve_minus_eq]
  rfl

theorem localPadicCurve_plus_eq :
    localPadicCurve plusA plusB = gaussianE0PadicPlus := by
  rw [localPadicCurve, localCurve_plus_eq]
  exact gaussianE0IntegralPlus_baseChange

theorem localPadicCurve_minus_eq :
    localPadicCurve minusA minusB = gaussianE0PadicMinus := by
  rw [localPadicCurve, localCurve_minus_eq]
  exact gaussianE0IntegralMinus_baseChange

instance localResidueCurvePlus_isElliptic :
    (localResidueCurve plusA plusB).IsElliptic := by
  rw [localResidueCurve_plus_eq]
  infer_instance

instance localResidueCurveMinus_isElliptic :
    (localResidueCurve minusA minusB).IsElliptic := by
  rw [localResidueCurve_minus_eq]
  infer_instance

/-- Transport points across an equality of displayed Weierstrass models. -/
def castPoint
    {W V : WeierstrassCurve ℚ_[37]} (h : W = V) :
    W.toAffine.Point → V.toAffine.Point :=
  fun P => Eq.mp (congrArg (fun C => C.toAffine.Point) h) P

/-- Transporting the ambient curve does not change the projective
`x`-representative. -/
@[simp] theorem castPoint_xRep
    {W V : WeierstrassCurve ℚ_[37]} (h : W = V)
    (P : W.toAffine.Point) :
    (castPoint h P).xRep = P.xRep := by
  subst V
  rfl

/-- Base change through the plus embedding, transported to the normalized
local model consumed by `finiteReducePoint`. -/
def mapE0PointPlusLocal
    (Q : GaussianP37Bridge.E0Point) :
    (localPadicCurve plusA plusB).toAffine.Point :=
  castPoint localPadicCurve_plus_eq.symm (mapE0PointPlus Q)

/-- Base change through the minus embedding on the same normalized model. -/
def mapE0PointMinusLocal
    (Q : GaussianP37Bridge.E0Point) :
    (localPadicCurve minusA minusB).toAffine.Point :=
  castPoint localPadicCurve_minus_eq.symm (mapE0PointMinus Q)

@[simp] theorem mapE0PointPlusLocal_xRep
    (Q : GaussianP37Bridge.E0Point) :
    (mapE0PointPlusLocal Q).xRep = (mapE0PointPlus Q).xRep := by
  unfold mapE0PointPlusLocal
  exact castPoint_xRep _ _

@[simp] theorem mapE0PointMinusLocal_xRep
    (Q : GaussianP37Bridge.E0Point) :
    (mapE0PointMinusLocal Q).xRep = (mapE0PointMinus Q).xRep := by
  unfold mapE0PointMinusLocal
  exact castPoint_xRep _ _

/-- The actual executable plus reduction of an `E₀(ℚ(i))` point. -/
def reduceE0Plus (Q : GaussianP37Bridge.E0Point) : FinitePoint :=
  finiteReducePoint plusA plusB (mapE0PointPlusLocal Q)

/-- The actual executable minus reduction of an `E₀(ℚ(i))` point. -/
def reduceE0Minus (Q : GaussianP37Bridge.E0Point) : FinitePoint :=
  finiteReducePoint minusA minusB (mapE0PointMinusLocal Q)

/-- A rational Gaussian abscissa has the same projective abscissa after the
two split embeddings. -/
theorem mapE0PointLocal_xRep_eq_of_rational
    (Q : GaussianP37Bridge.E0Point)
    (hx : GaussianP37Bridge.HasRationalAffineX Q) :
    (mapE0PointPlusLocal Q).xRep =
      (mapE0PointMinusLocal Q).xRep := by
  rw [mapE0PointPlusLocal_xRep, mapE0PointMinusLocal_xRep]
  rcases Q with (_ | ⟨x, y, hxy⟩)
  · simp [GaussianP37Bridge.HasRationalAffineX] at hx
  · rcases hx with ⟨q, hq⟩
    subst x
    change
      ![gaussianToPadicPlus (gaussianOfRat q), (1 : ℚ_[37])] =
        ![gaussianToPadicMinus (gaussianOfRat q), (1 : ℚ_[37])]
    funext j
    fin_cases j
    · simp [gaussianOfRat]
    · rfl

/-- The two actual normalized reductions have a common projective
`x`-coordinate on the rational `x`-line. -/
theorem reduceE0_sameX_of_rational
    (Q : GaussianP37Bridge.E0Point)
    (hx : GaussianP37Bridge.HasRationalAffineX Q) :
    sameX (reduceE0Plus Q) (reduceE0Minus Q) = true := by
  apply finiteReducePoint_sameX_of_xRep_eq
  exact mapE0PointLocal_xRep_eq_of_rational Q hx

/-- Boolean equality of projective finite abscissae can be unpacked into the
two constructors required by `Split37ProjectiveReduction`. -/
theorem finitePoints_common_of_sameX
    (P Q : FinitePoint) (h : sameX P Q = true) :
    (P = none ∧ Q = none) ∨
      ∃ x yP yQ : ℕ,
        P = some (x, yP) ∧ Q = some (x, yQ) := by
  rcases P with (_ | ⟨xP, yP⟩) <;>
    rcases Q with (_ | ⟨xQ, yQ⟩)
  · exact Or.inl ⟨rfl, rfl⟩
  · simp [sameX] at h
  · simp [sameX] at h
  · have hx : xP = xQ := by
      simpa [sameX] using h
    subst xQ
    exact Or.inr ⟨xP, yP, yQ, rfl, rfl⟩

/-- Constructor-level common reduced abscissa for the two actual split
reductions. -/
theorem reduceE0_common_of_rational
    (Q : GaussianP37Bridge.E0Point)
    (hx : GaussianP37Bridge.HasRationalAffineX Q) :
    (reduceE0Plus Q = none ∧ reduceE0Minus Q = none) ∨
      ∃ x yPlus yMinus : ℕ,
        reduceE0Plus Q = some (x, yPlus) ∧
          reduceE0Minus Q = some (x, yMinus) :=
  finitePoints_common_of_sameX _ _ (reduceE0_sameX_of_rational Q hx)

end

end GaussianProjectiveReduction
end Cuboid2
