import Cuboid2.QuadraticReduction.GaussianSplit

/-!
# From the Gaussian elliptic quotients back to the octic curve

This module isolates the exact conclusions needed from the global
Mordell--Weil and split-37 argument.  It then proves, by elementary
coordinate algebra, that these conclusions imply the four rational points
on the octic curve.
-/

namespace Cuboid2

noncomputable section

open scoped QuadraticAlgebra

/-- The exact rank-one elliptic-Chabauty conclusion required on the first
Gaussian cover. -/
def GaussianCoverZeroClassified : Prop :=
  ∀ C : GaussianCoverZeroPoint,
    C.toE0 = gaussianE0P ∨ C.toE0 = -gaussianE0P

/-- The exact rank-zero conclusion required on the twisted Gaussian cover. -/
def GaussianCoverOneEllipticClassified : Prop :=
  ∀ C : GaussianCoverOnePoint,
    C.toE1 = 0 ∨ C.toE1 = gaussianE1T

/-- No point of the twisted quartic can map to infinity, since its elliptic
image is constructed on the affine chart. -/
theorem gaussianCoverOne_toE1_ne_zero (C : GaussianCoverOnePoint) :
    C.toE1 ≠ 0 := by
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-- The torsion point `(0,0)` is not in the image of the twisted quartic.
At `u=0` its equation would make the rational norm of `w` a square root of
`5`. -/
theorem gaussianCoverOne_toE1_ne_torsion (C : GaussianCoverOnePoint) :
    C.toE1 ≠ gaussianE1T := by
  intro hT
  have hx :
      -2 * gaussianI * gaussianOfRat (C.u ^ 2) = 0 := by
    have hxRep := congrArg
      (fun Q : gaussianE1.toAffine.Point => Q.xRep 0) hT
    simpa [GaussianCoverOnePoint.toE1, gaussianE1T,
      WeierstrassCurve.Affine.Point.mk,
      WeierstrassCurve.Affine.Point.xRep] using hxRep
  have hu : C.u = 0 := by
    have hxim := congrArg QuadraticAlgebra.im hx
    simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_neg,
      QuadraticAlgebra.re_neg, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat, gaussianI_re, gaussianI_im,
      gaussianOfRat_re, gaussianOfRat_im,
      QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at hxim
    norm_num at hxim
    exact hxim
  have hw : C.w ^ 2 = (⟨-2, 1⟩ : GaussianRat) := by
    rw [C.onCurve]
    rw [hu]
    ext <;>
      norm_num [gaussianQuartic, gaussianI, gaussianOfRat, pow_two,
        QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hnorm :
      gaussianNorm C.w ^ 2 = 5 := by
    calc
      gaussianNorm C.w ^ 2 =
          gaussianNorm (C.w ^ 2) := by
            calc
              gaussianNorm C.w ^ 2 =
                  gaussianNorm C.w * gaussianNorm C.w := by ring
              _ = gaussianNorm (C.w * C.w) :=
                (gaussianNorm_mul C.w C.w).symm
              _ = gaussianNorm (C.w ^ 2) := by rw [pow_two]
      _ = gaussianNorm (⟨-2, 1⟩ : GaussianRat) := by rw [hw]
      _ = 5 := by norm_num
  exact five_not_rational_square ⟨gaussianNorm C.w, hnorm⟩

/-- The displayed rank-zero elliptic classification makes the twisted
Gaussian cover empty. -/
theorem gaussianCoverOne_empty
    (hclass : GaussianCoverOneEllipticClassified) :
    IsEmpty GaussianCoverOnePoint := by
  refine ⟨fun C => ?_⟩
  rcases hclass C with hzero | hT
  · exact gaussianCoverOne_toE1_ne_zero C hzero
  · exact gaussianCoverOne_toE1_ne_torsion C hT

/-- Either of the two surviving elliptic points on the first quotient has
abscissa `2`, forcing the quartic coordinate to satisfy `u²=1`. -/
theorem gaussianCoverZero_u_sq_eq_one
    (hclass : GaussianCoverZeroClassified)
    (C : GaussianCoverZeroPoint) :
    C.u ^ 2 = 1 := by
  rcases hclass C with hP | hP
  · have hx :
        2 * gaussianOfRat (C.u ^ 2) = 2 := by
      have hxRep := congrArg
        (fun Q : gaussianE0.toAffine.Point => Q.xRep 0) hP
      simpa [GaussianCoverZeroPoint.toE0, gaussianE0P,
        WeierstrassCurve.Affine.Point.mk,
        WeierstrassCurve.Affine.Point.xRep] using hxRep
    have hxRe := congrArg QuadraticAlgebra.re hx
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat,
      gaussianOfRat_re, gaussianOfRat_im] at hxRe
    linarith
  · have hx :
        2 * gaussianOfRat (C.u ^ 2) = 2 := by
      have hxRep := congrArg
        (fun Q : gaussianE0.toAffine.Point => Q.xRep 0) hP
      simpa [GaussianCoverZeroPoint.toE0, gaussianE0P,
        WeierstrassCurve.Affine.Point.mk,
        WeierstrassCurve.Affine.Point.xRep] using hxRep
    have hxRe := congrArg QuadraticAlgebra.re hx
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat,
      gaussianOfRat_re, gaussianOfRat_im] at hxRe
    linarith

/-- The two exact elliptic conclusions imply the four rational points on the
original octic curve. -/
theorem octic_classified_of_gaussian_covers
    (hzero : GaussianCoverZeroClassified)
    (hone : GaussianCoverOneEllipticClassified) :
    OcticRationalPointsClassified := by
  intro P
  rcases octic_to_gaussian_cover P with hC | hC
  · obtain ⟨C, hCu⟩ := hC
    have hu2 : P.u ^ 2 = 1 := by
      rw [← hCu]
      exact gaussianCoverZero_u_sq_eq_one hzero C
    have hu : P.u = 1 ∨ P.u = -1 := by
      have hfactor : (P.u - 1) * (P.u + 1) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hfactor with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    have hr2 : P.r ^ 2 = 1 := by
      rw [P.onCurve]
      rcases hu with hu | hu <;> rw [hu] <;> norm_num [octicRhs]
    have hr : P.r = 1 ∨ P.r = -1 := by
      have hfactor : (P.r - 1) * (P.r + 1) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hfactor with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rcases hu with hu | hu <;> rcases hr with hr | hr
    · exact Or.inl ⟨hu, hr⟩
    · exact Or.inr (Or.inl ⟨hu, hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hu, hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hu, hr⟩))
  · obtain ⟨C, -⟩ := hC
    exact (isEmpty_iff.mp (gaussianCoverOne_empty hone) C).elim

end

end Cuboid2
