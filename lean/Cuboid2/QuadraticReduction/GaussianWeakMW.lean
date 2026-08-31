import Cuboid2.QuadraticReduction.GaussianDualTranslation
import Cuboid2.QuadraticReduction.GaussianHeight

/-!
# Weak Mordell--Weil from the two-class dual descent

If the dual Kummer image consists only of the identity and the class of the
dual two-torsion point, constructive exactness of the two isogenies identifies
the kernel of the source Kummer map with the image of doubling.  A finite
source Kummer image then gives finite index of doubling and hence finite
generation by the height descent developed in `GaussianHeight`.
-/

namespace Cuboid2

noncomputable section

namespace GaussianWeakMW

open GaussianDescent

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

/-- If the dual Kummer image has only its identity and torsion classes, the
kernel of the source Kummer map is exactly the image of doubling.
-/
theorem alpha_eq_one_iff_two_smul_of_dual_classification
    (A B : GaussianRat) (hB : B ≠ 0) (hC : A ^ 2 - 4 * B ≠ 0)
    (hdual : ∀ Q : (dualCurve A B).toAffine.Point,
      alphaDual A B hB hC Q = 1 ∨
        alphaDual A B hB hC Q =
          alphaDual A B hB hC (dualTorsion A B hB hC))
    (P : (curve A B).toAffine.Point) :
    alpha A B hB hC P = 1 ↔
      ∃ U : (curve A B).toAffine.Point, P = 2 • U := by
  constructor
  · intro hP
    obtain ⟨Q, hQ⟩ :=
      (alpha_eq_one_iff_phiHat_image A B hB hC P).mp hP
    rcases hdual Q with hQdual | hQdual
    · obtain ⟨U, hU⟩ :=
        (alphaDual_eq_one_iff_phi_image A B hB hC Q).mp hQdual
      refine ⟨U, ?_⟩
      calc
        P = phiHat A B hB hC Q := hQ.symm
        _ = phiHat A B hB hC (phi A B hB hC U) := by rw [hU]
        _ = 2 • U := phiHat_phi A B hB hC U
    · let T : (dualCurve A B).toAffine.Point :=
        dualTorsion A B hB hC
      have hsubZero :
          alphaDualHom A B hB hC (Q - T) = 0 := by
        rw [map_sub]
        simp only [alphaDualHom_apply, T, hQdual, sub_self]
      have hsubAlpha :
          alphaDual A B hB hC (Q - T) = 1 := by
        exact hsubZero
      obtain ⟨U, hU⟩ :=
        (alphaDual_eq_one_iff_phi_image A B hB hC (Q - T)).mp
          hsubAlpha
      have htranslate : T + (Q - T) = Q := by abel
      refine ⟨U, ?_⟩
      calc
        P = phiHat A B hB hC Q := hQ.symm
        _ = phiHat A B hB hC (T + (Q - T)) := by rw [htranslate]
        _ = phiHat A B hB hC (Q - T) := by
          exact phiHat_dualTorsion_add A B hB hC (Q - T)
        _ = phiHat A B hB hC (phi A B hB hC U) := by rw [hU]
        _ = 2 • U := phiHat_phi A B hB hC U
  · rintro ⟨U, rfl⟩
    rw [← phiHat_phi A B hB hC U]
    exact alpha_phiHat_eq_one A B hB hC (phi A B hB hC U)

/-- Equality of source Kummer classes is equivalently divisibility of the
point difference by two.
-/
theorem alpha_eq_alpha_iff_sub_eq_two_smul_of_dual_classification
    (A B : GaussianRat) (hB : B ≠ 0) (hC : A ^ 2 - 4 * B ≠ 0)
    (hdual : ∀ Q : (dualCurve A B).toAffine.Point,
      alphaDual A B hB hC Q = 1 ∨
        alphaDual A B hB hC Q =
          alphaDual A B hB hC (dualTorsion A B hB hC))
    (P R : (curve A B).toAffine.Point) :
    alpha A B hB hC P = alpha A B hB hC R ↔
      ∃ U : (curve A B).toAffine.Point, P - R = 2 • U := by
  have hkernel :=
    alpha_eq_one_iff_two_smul_of_dual_classification
      A B hB hC hdual (P - R)
  constructor
  · intro hPR
    apply hkernel.mp
    have hzero :
        alphaHom A B hB hC (P - R) = 0 := by
      rw [map_sub]
      simp only [alphaHom_apply, hPR, sub_self]
    exact hzero
  · intro htwo
    have hzero :
        alphaHom A B hB hC (P - R) = 0 := by
      exact hkernel.mpr htwo
    have hEqAdd :
        alphaHom A B hB hC P = alphaHom A B hB hC R := by
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact hzero
    exact congrArg Additive.toMul hEqAdd

/-- Under the two-class dual classification, a finite source Kummer image
makes the actual doubling image finite-index.
-/
theorem finiteIndex_two_of_finite_alpha_and_dual_classification
    (A B : GaussianRat) (hB : B ≠ 0) (hC : A ^ 2 - 4 * B ≠ 0)
    (hdual : ∀ Q : (dualCurve A B).toAffine.Point,
      alphaDual A B hB hC Q = 1 ∨
        alphaDual A B hB hC Q =
          alphaDual A B hB hC (dualTorsion A B hB hC))
    [Finite (alphaHom A B hB hC).range] :
    (nsmulAddMonoidHom
      (α := (curve A B).toAffine.Point) 2).range.FiniteIndex := by
  have hrange :
      (nsmulAddMonoidHom
          (α := (curve A B).toAffine.Point) 2).range =
        (alphaHom A B hB hC).ker := by
    ext P
    change
      (∃ U : (curve A B).toAffine.Point, 2 • U = P) ↔
        alpha A B hB hC P = 1
    rw [alpha_eq_one_iff_two_smul_of_dual_classification
      A B hB hC hdual P]
    constructor <;> rintro ⟨U, hU⟩
    · exact ⟨U, hU.symm⟩
    · exact ⟨U, hU.symm⟩
  rw [hrange]
  infer_instance

local instance gaussianRatNumberField : NumberField GaussianRat where

/-- Honest weak Mordell--Weil consumer: finite source Kummer image and the
two-class dual classification imply finite generation of the source curve.
-/
theorem fg_of_finite_alpha_and_dual_classification
    (A B : GaussianRat) (hB : B ≠ 0) (hC : A ^ 2 - 4 * B ≠ 0)
    (hdual : ∀ Q : (dualCurve A B).toAffine.Point,
      alphaDual A B hB hC Q = 1 ∨
        alphaDual A B hB hC Q =
          alphaDual A B hB hC (dualTorsion A B hB hC))
    [Finite (alphaHom A B hB hC).range] :
    AddGroup.FG (curve A B).toAffine.Point := by
  let _ : (curve A B).IsElliptic :=
    { isUnit := isUnit_iff_ne_zero.mpr
        (curve_discriminant_ne_zero hB hC) }
  exact GaussianHeight.Point.fg_of_finiteIndex_two (curve A B)
    (finiteIndex_two_of_finite_alpha_and_dual_classification
      A B hB hC hdual)

end GaussianWeakMW

end

end Cuboid2
