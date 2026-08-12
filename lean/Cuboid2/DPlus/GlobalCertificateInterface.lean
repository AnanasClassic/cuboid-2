import Cuboid2.DPlus.FiniteGroup
import Cuboid2.DPlus.GlobalBridge
import Cuboid2.DPlus.GlobalMumfordCertificate
import Cuboid2.DPlus.LocalP3

/-!
# Exact boundary of the direct `D+` global certificate

This module records the arithmetic-geometric theorem needed by the direct
`p = 3` proof as an explicit proposition, and proves all formal consequences
of such a theorem.  It does not postulate the theorem.

The finite inputs already checked in Lean are:

* the complete `42`-element reduction at `7`;
* the exact order `21` of the reduction of `D`;
* the integral `3`-saturation consequence;
* the five affine residue points at `3`;
* the universal valuation inequalities for all local-series tails; and
* the exact rational Mumford curve identity for the pinned output used to
  calculate the logarithm direction.

What remains genuinely global is the Schaefer--Stoll rank theorem together
with the Coleman/Strassmann passage from the rational Mordell--Weil group to
uniqueness in the four relevant residue disks.
-/

namespace Cuboid2

noncomputable section

/--
The one global conclusion needed downstream from all exact `D+`
certificates.  Keeping it as a proposition (not an axiom) makes the remaining
dependency precise and auditable.
-/
def DPlusDirectP3Conclusion : Prop :=
  DPlusSquareAbscissaClassified

/-- The direct global conclusion is exactly the public affine classification. -/
theorem dplusDirectP3Conclusion_iff :
    DPlusDirectP3Conclusion ↔ DPlusSquareAbscissaClassified :=
  Iff.rfl

/-- The direct global conclusion closes the octic rational-point problem. -/
theorem octic_classification_of_dplusDirectP3Conclusion
    (h : DPlusDirectP3Conclusion) :
    OcticRationalPointsClassified :=
  octic_classified_of_dplus_classified h

/--
In the exact finite model at `7`, every odd rational index compatible with
the checked reduction is prime to `3`.
-/
theorem dplus_direct_certificate_three_saturation
    {generator : DPlusJacobianIndexF7} {m : ℕ}
    (hrel : dplusGeneratorIndexF7 = m • generator)
    (hm : Odd m) :
    ¬ 3 ∣ m :=
  dplusIndex_odd_multiplier_not_divisible_by_three hrel hm

/--
The direct certificate's affine residue-disk reduction at `3`: only the
zero and the two `a=1` disks can contain a square abscissa.
-/
theorem dplus_direct_certificate_square_residue_disks
    (P : DPlusFiniteAffinePoint (ZMod 3))
    (hP : P.Valid)
    (hsquare : ∃ u : ZMod 3, P.a = u ^ 2) :
    P = ⟨0, 0⟩ ∨ P = ⟨1, 1⟩ ∨ P = ⟨1, 2⟩ :=
  dplusF3_valid_square_abscissa P hP hsquare

/-- The checked rational output underlying the annihilator is on `D+`. -/
theorem dplus_direct_certificate_mumford_output_valid :
    dplusElevenD.ValidOn dplusPolynomial :=
  dplusElevenD_valid

/--
The universal local tail bound used at infinity, stated in the exact
subtraction form consumed by the certificate.
-/
theorem dplus_direct_certificate_infinity_tail
    {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ n - 1 - padicValNat 3 n :=
  one_le_degree_sub_one_sub_padicValNat_three hn

/-- The first universal local tail bound in the two disks above `a=1`. -/
theorem dplus_direct_certificate_one_disk_tail₁
    {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ 2 * n - 2 - padicValNat 3 n :=
  one_le_twice_degree_sub_two_sub_padicValNat_three hn

/-- The second universal local tail bound in the two disks above `a=1`. -/
theorem dplus_direct_certificate_one_disk_tail₂
    {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ 2 * n - 3 - padicValNat 3 n :=
  one_le_twice_degree_sub_three_sub_padicValNat_three hn

end

end Cuboid2
