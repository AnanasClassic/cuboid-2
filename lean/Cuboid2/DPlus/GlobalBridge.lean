import Cuboid2.DPlus.Basic

/-!
# Global classification interface for `D+`

The direct `p = 3` certificate ultimately classifies affine rational points
on `D+` whose abscissa is a square.  This file isolates that one genuinely
global assertion and proves, without any arithmetic-geometric premise, its
exact relation to the octic cover used by the quadratic-cubic reduction.

In particular, the exceptional fibre `a = 0` does not lift to a rational
point of the octic cover: it would require a rational square root of `5`.
-/

namespace Cuboid2

noncomputable section

/-- Extensionality for the two affine coordinates. -/
private theorem dplusPoint_ext
    {P Q : DPlusAffinePoint} (ha : P.a = Q.a) (hR : P.R = Q.R) :
    P = Q := by
  cases P
  cases Q
  simpa only [DPlusAffinePoint.mk.injEq] using And.intro ha hR

/-- The precise affine conclusion supplied by the direct `D+` argument. -/
def DPlusSquareAbscissaClassified : Prop :=
  ∀ P : DPlusAffinePoint, P.HasSquareAbscissa →
    P = dplusZero ∨ P = dplusOnePlus ∨ P = dplusOneMinus

/-- The corresponding rational-point conclusion on the octic cover. -/
def OcticRationalPointsClassified : Prop :=
  ∀ P : OcticPoint,
    (P.u = 1 ∧ P.r = 1) ∨
    (P.u = 1 ∧ P.r = -1) ∨
    (P.u = -1 ∧ P.r = 1) ∨
    (P.u = -1 ∧ P.r = -1)

/-- There is no rational square root of `5`. -/
theorem five_not_rational_square : ¬ ∃ r : ℚ, r ^ 2 = 5 := by
  intro h
  have hsquare : IsSquare (5 : ℚ) := by
    rcases h with ⟨r, hr⟩
    exact ⟨r, by simpa [pow_two] using hr.symm⟩
  have : ¬ IsSquare (5 : ℚ) := by norm_num
  exact this hsquare

/-- A square-abscissa point above `a = 0` is the known Weierstrass point. -/
theorem dplus_eq_zero_of_abscissa_eq_zero
    (P : DPlusAffinePoint) (ha : P.a = 0) :
    P = dplusZero := by
  have hR : P.R = 0 := by
    have hsquare : P.R ^ 2 = 0 := by
      simpa [dplusRhs, ha] using P.onCurve
    nlinarith [sq_nonneg P.R]
  cases P
  simp_all [dplusZero]

/--
Every nonzero square-abscissa point on `D+` lifts exactly to the octic
cover.  The ordinate is forced to be `R/u`.
-/
def DPlusAffinePoint.toOcticOfSquare
    (P : DPlusAffinePoint) (u : ℚ) (ha : P.a = u ^ 2)
    (hu : u ≠ 0) : OcticPoint where
  u := u
  r := P.R / u
  onCurve := by
    have hquot :
        (P.R / u) ^ 2 = dplusRhs (u ^ 2) / u ^ 2 := by
      calc
        (P.R / u) ^ 2 = P.R ^ 2 / u ^ 2 := by ring
        _ = dplusRhs P.a / u ^ 2 := by rw [P.onCurve]
        _ = dplusRhs (u ^ 2) / u ^ 2 := by rw [ha]
    rw [dplus_pullback_identity] at hquot
    calc
      (P.R / u) ^ 2 = (u ^ 2 * octicRhs u) / u ^ 2 := hquot
      _ = octicRhs u := by field_simp [hu]

@[simp] theorem DPlusAffinePoint.toOcticOfSquare_toDPlus
    (P : DPlusAffinePoint) (u : ℚ) (ha : P.a = u ^ 2)
    (hu : u ≠ 0) :
    (P.toOcticOfSquare u ha hu).toDPlus = P := by
  apply dplusPoint_ext
  · exact ha.symm
  · simp [DPlusAffinePoint.toOcticOfSquare, OcticPoint.toDPlus]
    field_simp [hu]

/--
The point of `D+` associated to an octic point can never be the
Weierstrass point `(0,0)`.
-/
theorem OcticPoint.toDPlus_ne_zero (P : OcticPoint) :
    P.toDPlus ≠ dplusZero := by
  intro h
  have hu2 : P.u ^ 2 = 0 := by
    simpa [OcticPoint.toDPlus, dplusZero] using
      congrArg DPlusAffinePoint.a h
  have hu : P.u = 0 := by nlinarith [sq_nonneg P.u]
  have hr : P.r ^ 2 = 5 := by
    simpa [octicRhs, hu] using P.onCurve
  exact five_not_rational_square ⟨P.r, hr⟩

/--
The global `D+` classification immediately supplies the four exact lifts on
the octic cover.
-/
theorem octic_classified_of_dplus_classified
    (hclass : DPlusSquareAbscissaClassified) :
    OcticRationalPointsClassified := by
  intro P
  have himage := hclass P.toDPlus P.toDPlus_hasSquareAbscissa
  rcases himage with hzero | hplus | hminus
  · exact (P.toDPlus_ne_zero hzero).elim
  · have hu2 : P.u ^ 2 = 1 := by
      simpa [OcticPoint.toDPlus, dplusOnePlus] using
        congrArg DPlusAffinePoint.a hplus
    have hR : P.u * P.r = 1 := by
      simpa [OcticPoint.toDPlus, dplusOnePlus] using
        congrArg DPlusAffinePoint.R hplus
    have hu : P.u = 1 ∨ P.u = -1 := by
      have : (P.u - 1) * (P.u + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rcases hu with hu | hu
    · left
      constructor
      · exact hu
      · nlinarith
    ·
      right
      right
      right
      constructor
      · exact hu
      · nlinarith
  · have hu2 : P.u ^ 2 = 1 := by
      simpa [OcticPoint.toDPlus, dplusOneMinus] using
        congrArg DPlusAffinePoint.a hminus
    have hR : P.u * P.r = -1 := by
      simpa [OcticPoint.toDPlus, dplusOneMinus] using
        congrArg DPlusAffinePoint.R hminus
    have hu : P.u = 1 ∨ P.u = -1 := by
      have : (P.u - 1) * (P.u + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rcases hu with hu | hu
    · right
      left
      constructor
      · exact hu
      · nlinarith
    ·
      right
      right
      left
      constructor
      · exact hu
      · nlinarith

/--
Conversely, the octic classification plus the elementary exceptional-fibre
calculation gives the full affine square-abscissa classification on `D+`.
-/
theorem dplus_classified_of_octic_classified
    (hclass : OcticRationalPointsClassified) :
    DPlusSquareAbscissaClassified := by
  intro P hsquare
  rcases hsquare with ⟨u, ha⟩
  by_cases hu : u = 0
  · left
    apply dplus_eq_zero_of_abscissa_eq_zero P
    simp [ha, hu]
  · have hlift := hclass (P.toOcticOfSquare u ha hu)
    rcases hlift with hpp | hpm | hmp | hmm
    · right
      left
      rcases hpp with ⟨hu1, hr1⟩
      have hu1' : u = 1 := by
        simpa [DPlusAffinePoint.toOcticOfSquare] using hu1
      have hR : P.R = 1 := by
        have := hr1
        simp [DPlusAffinePoint.toOcticOfSquare, hu1'] at this
        exact this
      apply dplusPoint_ext
      · simp [ha, hu1', dplusOnePlus]
      · simp [hR, dplusOnePlus]
    · right
      right
      rcases hpm with ⟨hu1, hr1⟩
      have hu1' : u = 1 := by
        simpa [DPlusAffinePoint.toOcticOfSquare] using hu1
      have hR : P.R = -1 := by
        have := hr1
        simp [DPlusAffinePoint.toOcticOfSquare, hu1'] at this
        exact this
      apply dplusPoint_ext
      · simp [ha, hu1', dplusOneMinus]
      · simp [hR, dplusOneMinus]
    · right
      right
      rcases hmp with ⟨hu1, hr1⟩
      have hu1' : u = -1 := by
        simpa [DPlusAffinePoint.toOcticOfSquare] using hu1
      have hR : P.R = -1 := by
        have := hr1
        simp [DPlusAffinePoint.toOcticOfSquare, hu1'] at this
        linarith
      apply dplusPoint_ext
      · simp [ha, hu1', dplusOneMinus]
      · simp [hR, dplusOneMinus]
    · right
      left
      rcases hmm with ⟨hu1, hr1⟩
      have hu1' : u = -1 := by
        simpa [DPlusAffinePoint.toOcticOfSquare] using hu1
      have hR : P.R = 1 := by
        have := hr1
        simp [DPlusAffinePoint.toOcticOfSquare, hu1'] at this
        linarith
      apply dplusPoint_ext
      · simp [ha, hu1', dplusOnePlus]
      · simp [hR, dplusOnePlus]

/-- The two global formulations are exactly equivalent. -/
theorem dplus_classified_iff_octic_classified :
    DPlusSquareAbscissaClassified ↔ OcticRationalPointsClassified :=
  ⟨octic_classified_of_dplus_classified,
    dplus_classified_of_octic_classified⟩

end

end Cuboid2
