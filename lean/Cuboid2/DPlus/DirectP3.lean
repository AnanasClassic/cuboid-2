import Cuboid2.DPlus.FormalLogP3
import Cuboid2.DPlus.GlobalDescent
import Cuboid2.DPlus.GlobalPointClass
import Cuboid2.DPlus.GlobalCertificateInterface
import Cuboid2.DPlus.SquareDiskReduction

/-!
# Audited direct `p = 3` certificate surface for `D+`

All theorems here are consequences of checked finite or polynomial data.
There is intentionally no unconditional
`dplus_squareAbscissa_classified`: the current repository does not yet
define the rational Jacobian, the Schaefer--Stoll Kummer map, Coleman
integration, or the map from an arbitrary rational point to a divisor class.
Adding the desired conclusion without those bridges would merely hide it in
an assumption.
-/

namespace Cuboid2

noncomputable section

/-- The complete finite-field square-abscissa disk row. -/
theorem dplus_direct_p3_affine_disk_row
    (P : DPlusFiniteAffinePoint (ZMod 3))
    (hP : P.Valid)
    (hsquare : ∃ u : ZMod 3, P.a = u ^ 2) :
    P = ⟨0, 0⟩ ∨ P = ⟨1, 1⟩ ∨ P = ⟨1, 2⟩ :=
  dplusF3_valid_square_abscissa P hP hsquare

/-- The exact zero-disk quotient identity used to exclude nonzero points
whose square abscissa has positive `3`-adic valuation. -/
theorem dplus_direct_p3_zero_disk_row
    {a R u : ℚ}
    (ha : a = u ^ 2)
    (hcurve : R ^ 2 = dplusRhs a)
    (hu : u ≠ 0) :
    (R / u) ^ 2 = dplusCofactor a :=
  dplus_zero_disk_square_quotient ha hcurve hu

/-- The checked integral saturation conclusion needed in the two `a=1`
disks. -/
theorem dplus_direct_p3_saturation_row
    {generator : DPlusJacobianIndexF7} {m : ℕ}
    (hrel : dplusGeneratorIndexF7 = m • generator)
    (hm : Odd m) :
    ¬ 3 ∣ m :=
  dplus_three_saturated_odd_relation hrel hm

/-- The exact logarithm-ratio row and its first nonzero congruence. -/
theorem dplus_direct_p3_lambda_row :
    3 ≤ padicValRat 3 (dplusLambdaApprox - 7) ∧
      padicValRat 3 (dplusLambdaApprox - 1) = 1 :=
  ⟨dplusLambdaApprox_mod_twentySeven,
    dplusLambdaApprox_sub_one_valuation⟩

/-- The two normalized `a=1` rows have unit linear term. -/
theorem dplus_direct_p3_one_disk_linear_units :
    padicValRat 3 (dplusOneDiskNormalizedTrunc.coeff 1) = 0 ∧
      padicValRat 3 (dplusOneDiskNormalizedTruncNeg.coeff 1) = 0 :=
  ⟨dplusOneDiskNormalizedTrunc_valuation_row.1,
    dplusOneDiskNormalizedTruncNeg_linear_unit⟩

/-- The normalized infinity row has a unit linear term. -/
theorem dplus_direct_p3_infinity_linear_unit :
    padicValRat 3 (dplusInfinityNormalizedTrunc.coeff 1) = 0 :=
  dplusInfinityNormalizedTrunc_valuation_row.1

/-- The exact infinity chart has genuine unit partial derivative. -/
theorem dplus_direct_p3_infinity_implicit_unit :
    Polynomial.eval 0 (Polynomial.derivative (dplusInfinityPolynomialW 0)) = 1 :=
  dplusInfinityPolynomialW_derivative_at_origin

/-- Every affine rational point has the genuine square-norm Kummer value
required at the source boundary of the global descent. -/
theorem dplus_direct_p3_point_kummer_norm
    (P : DPlusAffinePoint) :
    dplusEtaleNorm (dplusPointKummerValue P) =
      (P.R / 2) ^ 2 :=
  dplusPointKummerValue_norm P

/-- Every affine rational point also gives a valid generator of the exact
fixed-curve Cantor presentation. -/
theorem dplus_direct_p3_point_mumford_valid
    (P : DPlusAffinePoint) :
    (dplusPointMumfordPair P).ValidOn dplusPolynomial :=
  dplusPointMumfordPair_valid P

end

end Cuboid2
