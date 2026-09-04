# The local / saturation half of the Gaussian route (Lean sources `lean/Cuboid2/QuadraticReduction/Gaussian*.lean`)

All theorem names below are in namespace `Cuboid2` (sub-namespaces given where relevant).
Notation: `σ₊, σ₋ : ℚ(i) → ℚ₃₇` are the two split embeddings, `E₀ : y² = x³ + 2i x² − (2+4i)x`,
`E₁ : y² = x³ + 2x² + (2+4i)x`, `P = (2,2) ∈ E₀(ℚ(i))`, `T = (0,0) ∈ E₀(ℚ(i))`, `T₁ = (0,0) ∈ E₁(ℚ(i))`.
Covers (file `GaussianCover.lean`): `q(u) = (2u⁴ − 1) + i(2u² − 2)`,
`C₀ : v² = q(u)` (`GaussianCoverZeroPoint`), `C₁ : w² = −i·q(u)` (`GaussianCoverOnePoint`),
`C₀ → E₀ : (u,v) ↦ (2u², 2uv)` (`GaussianCoverZeroPoint.toE0`),
`C₁ → E₁ : (u,w) ↦ (−2iu², −2iuw)` (`GaussianCoverOnePoint.toE1`).
The octic is `r² = 4u⁸ − 8u² + 5 = N_{ℚ(i)/ℚ}(q(u))` (`octicRhs`, `gaussianQuartic_norm`).

---------------------------------------------------------------------------------------------------

## (a) The mathematical argument

### a.1 The two embeddings ℚ(i) → ℚ₃₇ (file `GaussianGoodReduction.lean`)

* `37 ≡ 1 (mod 4)` splits; `6² = 36 ≡ −1 (mod 37)`, `31 = −6`.
* Hensel: with `f = X² + 1` (`splitPolynomial`), `f(6) = 37`, `f'(6) = 12`, so
  `|f(6)|₃₇ = 37⁻¹ < |f'(6)|₃₇² = 1` (`splitPolynomial_hensel_at_six`). Mathlib's `hensels_lemma`
  gives `r₊ := splitRootPlus ∈ ℤ₃₇` with `r₊² = −1` (`splitRootPlus_sq`) and `|r₊ − 6| < 1`
  (`splitRootPlus_norm_sub_six`), hence `r₊ mod 37 = 6` (`splitRootPlus_toZMod`). `r₋ := −r₊`
  (`splitRootMinus`), `r₋ mod 37 = 31` (`splitRootMinus_toZMod`).
* Lifts modulo `37² = 1369`: `r₊ ≡ 117`, `r₋ ≡ 1252` (`GaussianP37ActualTrace.splitRootPlus_toZModPow_two`,
  `splitRootMinus_toZModPow_two`; certificate `GaussianP37.splitRootLifts`: `117² ≡ 1252² ≡ 1368 (mod 1369)`,
  `117 ≡ 6`, `1252 ≡ 31 (mod 37)`).
* `σ₊ = gaussianToPadicPlus : ℚ(i) →ₐ[ℚ] ℚ₃₇`, `σ₊(i) = r₊`; `σ₋ = gaussianToPadicMinus`, `σ₋(i) = r₋`
  (built with `QuadraticAlgebra.lift`).

### a.2 Integral local models and good reduction

Generic integral two-torsion model (file `GaussianProjectiveReduction.lean`):
`localCurve A B : y² = x³ + A x² + B x` over `ℤ₃₇`, generic fibre `localPadicCurve A B` over `ℚ₃₇`,
special fibre `localResidueCurve A B` over `𝔽₃₇`.

For `E₀`: `A = 2r`, `B = −2 − 4r` (`gaussianE0IntegralPlus`, `gaussianE0IntegralMinus`; abbreviations
`plusA, plusB, minusA, minusB`). Residue coefficients:
* plus (`i ↦ 6`): `(a₂, a₄) = (12, 11)` (`gaussianE0ResiduePlus_coefficients`; `−2 − 24 = −26 ≡ 11`).
* minus (`i ↦ 31`): `(a₂, a₄) = (25, 22)` (`gaussianE0ResidueMinus_coefficients`).
Both discriminants are nonzero mod 37 (`native_decide`), so the special fibres are elliptic
(`gaussianE0ResiduePlus_isElliptic`, `…Minus_isElliptic`), `Δ` is a 37-adic unit
(`gaussianE0IntegralPlus_discriminant_isUnit`), the model is Mathlib-`IsIntegral`, `IsMinimal`, and
`HasGoodReduction ℤ₃₇` (`gaussianE0PadicPlus_hasGoodReduction`, `…Minus_hasGoodReduction`).
`gaussianE0PadicPlus := gaussianE0.map σ₊` equals the base change of the integral model
(`gaussianE0IntegralPlus_baseChange`, `localPadicCurve_plus_eq`).

For `E₁` (file `GaussianE1LocalReduction.lean`): `A = 2`, `B = 2 + 4r`; residues
plus `(2, 26)`, minus `(2, 15)` (`plus_coefficients`, `minus_coefficients`; certificates
`GaussianFiniteExponent.e1Plus_all_twentyEight`, `e1Minus_all_thirtyFour`).

Base change of points: `mapE0PointPlus : E₀(ℚ(i)) →+ E₀^{σ₊}(ℚ₃₇)` is Mathlib's
`WeierstrassCurve.Affine.Point.map` (a group homomorphism); transported to the normalized model
by `castPoint` giving `mapE0PointPlusLocal`, `mapE0PointMinusLocal` (additive:
`mapE0PointPlusLocal_add`, `…_neg`, `…_zero` in `GaussianProjectiveReductionHom`).
They are **injective** because `σ±` are field embeddings
(`GaussianLocalMapInjective.mapE0PointPlusLocal_injective`, `mapE1PointPlusLocal_injective`, …);
packaged as `mapE0PointPlusLocalHom`, `mapE1PointPlusLocalHom`, etc.

### a.3 Projective reduction and the proof that it is a homomorphism

Definition (`GaussianProjectiveReduction.reducePoint`): for `(x,y)` on the generic fibre,
if `‖x‖ ≤ 1` then `‖y‖ ≤ 1` too (`norm_y_le_one_of_norm_x_le_one`, since `y² = x(x²+Ax+B)`),
and the point reduces to `(x̄, ȳ)`; if `‖x‖ > 1` it reduces to `∞`; `∞ ↦ ∞`.
The executable version `finiteReducePoint A B : Point → FinitePoint = Option (ℕ×ℕ)` forgets proofs
(`finitePointOfResidue`), so that the values live in the `GaussianFinite` tables. Specialized:
`reduceE0Plus`, `reduceE0Minus` (for `E₀`), `reduceE1Plus`, `reduceE1Minus` (for `E₁`).

Easy parts (`GaussianProjectiveReductionHom`): compatibility with `0` and with negation
(`reducePoint_neg`, `finiteReducePoint_neg`, `reduceE0Plus_neg`, `reduceE0Plus_add_neg`, …).
Values on the visible points (`GaussianVisibleReduction`): `reduceE0Plus P = some (2,2)`,
`reduceE0Minus P = some (2,2)`, `reduceE0Plus T = reduceE0Minus T = some (0,0)`,
`reduceE0Plus (−P) = some (2,35)`, `P + T = (−1−2i, 1+2i)` (`gaussianE0P_add_gaussianE0T`) reduces to
`(24,13)` at plus and `(11,26)` at minus. `E₁`: `reduceE1Plus T₁ = reduceE1Minus T₁ = some (0,0)`.

The **infinity disk / formal kernel** (file `GaussianFormalKernelDisk.lean`):
`InInfinityDisk A B P :⇔ P = ∞ ∨ ‖x(P)‖ > 1`; this is exactly the fibre of reduction over `∞`
(`finiteReducePoint_eq_none_iff_inInfinityDisk`). Key estimates for `‖x‖ > 1`:
`‖x² + Ax + B‖ = ‖x‖²` (`norm_inner_eq_norm_x_sq`), `‖y‖² = ‖x‖³` (`norm_y_sq_eq_norm_x_cube`), so
`t := −x/y` has `‖t‖² = ‖x‖⁻¹ < 1` (`GaussianFormalLocal.norm_parameter_lt_one`) and `r := 1/x` has
`‖r‖ < 1`, with the exact relation `r = t²(1 + A r + B r²)`
(`GaussianFormalLocal.reciprocal_eq_parameter_sq_mul`, `exists_integral_formal_parameters`).

Homomorphism proof, in the order of the files:

1. *Mixed case* `Q = (u,v)` integral, `S = (x,y)` in the disk (`GaussianFormalKernelDisk`):
   `‖u − x‖ = ‖x‖`, `‖v − y‖ = ‖y‖`, `‖λ‖² = ‖x‖` for the secant slope `λ = (v−y)/(u−x)`
   (`mixed_secant_norms`). Writing `λ = −(1 + v r t)/(t(1 − u r))` (`mixed_secant_slope_eq_formal`)
   one gets the *exact* identities
   `x(Q+S) − u = (2 v t + r·mixedXTranslationTail)/(1 − u r)²` (`formal_mixed_translated_x_sub`) and
   `y(Q+S) − v = t·mixedYTranslationTail/(1 − u r)³` (`formal_mixed_translated_y_sub`) with integral tails
   (`norm_mixedXTranslationTail_le_one`, `norm_mixedYTranslationTail_le_one`); since `‖t‖,‖r‖ < 1` both
   differences lie in the maximal ideal (`norm_mixed_translated_x_sub_lt_one`, `…_y_sub_lt_one`), so
   `red(Q+S) = red(Q)` (`finiteReducePoint_add_eq_left_of_left_integral_right_none`).
2. *Kernel closed under addition* (`finiteReducePoint_add_eq_none_of_eq_none`): if `P, S` both reduce to
   `∞` but `P+S` reduced affinely, translating `P+S` by the kernel point `−S` would preserve its
   affine reduction by (1), contradicting `(P+S) − S = P`. Hence `infinityKernel A B` is an additive
   subgroup and translation by it fixes every reduction (`finiteReducePoint_add_eq_left_of_right_eq_none`).
3. *Coincident reductions differ by a kernel point* (`finiteReducePoint_sub_eq_none_of_integral_eq`):
   for integral `P₁=(x₁,y₁), P₂=(x₂,y₂)` with equal reductions, the slope of `P₁ − P₂` has norm `> 1`:
   if `x₁ ≠ x₂` it is `(y₁ + y₂)/(x₁ − x₂)` with denominator in the maximal ideal and numerator a unit
   when `ȳ ≠ 0`, while on the residue two-torsion branch (`ȳ = 0`) the curve equation replaces the
   numerator by the unit cubic divided difference `x₁² + x₁x₂ + x₂² + A(x₁+x₂) + B`
   (`norm_curve_dividedDifference_eq_one_of_common_residue_y_zero`,
   `norm_difference_secant_slope_gt_one_of_X_ne`); if `x₁ = x₂` then `y₂ = −y₁`, `ȳ₁ = 0`, and the tangent
   slope `(3x² + 2Ax + B)/(2y)` has unit numerator (nonsingularity of the residue point,
   `residue_derivative_ne_zero_of_y_eq_zero`) and non-unit denominator
   (`norm_tangent_slope_gt_one_of_residue_y_zero`). A slope of norm `> 1` forces
   `x₃ = λ² − A − x₁ − x₂` into the infinity chart (`norm_addX_gt_one_of_integral_of_norm_slope_gt_one`).
   Consequently reduction fibres are exactly the cosets of `infinityKernel`
   (`finiteReducePoint_eq_iff_sub_mem_infinityKernel`, `finiteReducePoint_sub_eq_none_of_eq`).
4. *Integral points with distinct residues / equal residue and `ȳ ≠ 0`* (`GaussianSplit37ReductionActual`):
   the executable natural-number formulas `finiteAdd` agree with the geometric group law on the special
   fibre (`finitePointOfResidue_add`, via `residueInv_val_37`, `secantSlope_val_37`, `tangentSlope_val_37`, …),
   and reduction commutes with division by a unit (`toZMod_integral_quotient`), so the secant formula
   commutes with reduction when `x̄ ≠ X̄` (`finiteReducePoint_add_of_integral_residue_x_ne`) and the
   tangent formula when `ȳ ≠ 0` (`finiteReducePoint_add_self_of_integral_residue_y_ne_zero`).
5. *Assembly* (`GaussianSplit37ReductionActual.finiteReducePoint_add`): if either input reduces to `∞`
   use (2); otherwise both are integral with reductions `R_P, R_Q`; if `R_P = −R_Q` the sum lies in the
   kernel by (3) and `finiteAdd` gives `∞`; if `R_P = R_Q` replace `Q` by `P` (same coset, (3)) and use the
   tangent case of (4) (`ȳ ≠ 0` because `R_P ≠ −R_P`); otherwise `x̄ ≠ X̄` and use the secant case of (4).
   Hence `finiteReducePoint A B (P+Q) = finiteAdd 37 Ā B̄ (red P) (red Q)` for every integral two-torsion
   model with smooth special fibre, and in particular
   `reduceE0Plus_add`, `reduceE0Minus_add`, `reduceE1Plus_add`, `reduceE1Minus_add`
   (`GaussianE1Split37ReductionActual`). The maps are packaged as
   `split37GoodReductionActual : Split37GoodReduction`, `split37ProjectiveReductionActual`,
   `split37CoverReductionActual`.
6. *Surjectivity* (`GaussianReductionSurjective.reducePoint_surjective`, not needed downstream): residue-form
   Hensel lifting in `y` when `ȳ ≠ 0`, in `x` (with `y = 0`) when `ȳ = 0`.
7. Every reduction lies in the exhaustive table `finitePoints 37 Ā B̄`
   (`finiteReducePoint_mem_finitePoints`, `reduceE0Plus_mem_finitePoints`, `reduceE1Plus_mem_finitePoints`, …),
   so the exponent certificates apply: `red(nQ) = finiteMul … (red Q) n`
   (`GaussianFiniteExponent.map_nsmul_finite`).

### a.4 Formal group coordinates, oddness, torsion-freeness of the kernel (file `GaussianFormalKernelTorsion.lean`)

Coordinates on the affine points: `t := parameter = −x/y`, `w := auxiliary = −1/y` (both `0` at `∞`).
Exact formal-curve equation (`auxiliary_eq_parameter`): `w = t³ + A t² w + B t w²`.
On the kernel: `x, y ≠ 0` for affine kernel points, `‖t‖ < 1` (`norm_parameter_lt_one_of_mem_kernel`),
`‖w‖ = ‖t‖³` (`norm_auxiliary_eq_parameter_cube_of_mem_kernel`), `w` is uniquely determined by `t`
(`auxiliary_unique`), and `t` determines the point (`formal_coordinates_determine_point`,
`parameter_eq_zero_iff : t(P) = 0 ↔ P = 0`).
**Oddness**: `y ↦ −y` gives `t(−P) = −t(P)`, `w(−P) = −w(P)` (`parameter_neg`, `auxiliary_neg`);
this is what makes the case `P + Q = 0` exact (`t(P)+t(Q) = 0`) and, together with `‖w‖ = ‖t‖³`,
makes the nonlinear error of the group law start in degree three.
Chord: through `(t₁,w₁),(t₂,w₂)` write `w = c t + h`, `c = (w₂−w₁)/(t₂−t₁)`; then
`‖c‖ ≤ max(‖t₁‖,‖t₂‖)²`, `‖h‖ ≤ max³`, and the exact identity
`t(P+Q) = t₁ + t₂ + h(A + 2Bc)/(1 + Ac + Bc²)` (`chord_parameter_identity`,
`parameter_add_eq_chord_of_X_ne`), with `‖1 + Ac + Bc²‖ = 1`, `‖A + 2Bc‖ ≤ 1`, so the error is
`≤ max(‖t₁‖,‖t₂‖)³` (`norm_chordError_le_max_cube`). Tangent (doubling):
`c = (3t² + 2Atw + Bw²)/(1 − At² − 2Btw)`, `h = −2w/(1 − At² − 2Btw)`,
`t(2P) = 2t + h(A+2Bc)/(1+Ac+Bc²)`, error `≤ ‖t‖³` (`tangent_parameter_identity`,
`parameter_two_nsmul_eq_tangent`, `norm_tangentError_le_cube`).
Main estimate: `‖t(P+Q) − t(P) − t(Q)‖ ≤ max(‖t(P)‖,‖t(Q)‖)³` (`norm_parameter_add_sub_le_max_cube`),
hence by induction `‖t(nP) − n·t(P)‖ ≤ ‖t(P)‖³` and `‖t(nP)‖ ≤ ‖t(P)‖`
(`norm_parameter_nsmul_sub_le_cube`, `norm_parameter_zsmul_sub_le_cube`, `norm_parameter_nsmul_le`).
Consequences: for `37 ∤ n`, `‖t(nP)‖ = ‖t(P)‖` (`norm_parameter_nsmul_eq_of_not_dvd`; since
`‖t‖³ < ‖t‖ = ‖n t‖`); `‖t(37P)‖ = 37⁻¹‖t(P)‖` (`norm_parameter_37_nsmul_eq`; uses `‖t‖ ≤ 37⁻¹` so
`‖t‖³ < 37⁻¹‖t‖`). Therefore `nP = 0 ⇒ P = 0` for every `n ≠ 0`
(`nsmul_eq_zero_iff_of_not_dvd_37`, `nsmul_37_eq_zero_iff`, `infinityKernel_nsmul_right_injective`):
`infinityKernel A B` is torsion-free (`infinityKernel_isAddTorsionFree`).

### a.5 Point counts, exponents, multiples of P (files `GaussianP37.lean`, `GaussianFiniteExponent.lean`)

Coefficients `e0Coefficients p root = (2·root mod p, (p−2) − 4·root mod p)`; `plusCoefficients = (12,11)`,
`minusCoefficients = (25,22)`.
* `#E₀^{σ₊}(𝔽₃₇) = 48`, exponent `12`, `ord(2,2) = 12` (`plusGroupRow`); every point is killed by 12
  (`plus_all_twelve`).
* `#E₀^{σ₋}(𝔽₃₇) = 42`, exponent `42` (cyclic, generator `(5,3)`), `ord(2,2) = 6` (`minusGroupRow`);
  every point is killed by 42 (`minus_all_fortyTwo`). `gcd(12,42) = 6`
  (`six_nsmul_eq_zero_of_twelve_and_fortyTwo`).
* `#E₁^{σ₊}(𝔽₃₇) = 28`, `#E₁^{σ₋}(𝔽₃₇) = 34` (`e1Plus_all_twentyEight`, `e1Minus_all_thirtyFour`);
  `gcd(28,34) = 2` (`two_nsmul_eq_zero_of_twentyEight_and_thirtyFour`).
Multiples `nP̄` for `n = 0..11` (`plusPointRows`, `minusPointRows`):
* plus: `∞, (2,2), (10,4), (20,12), (33,26), (6,14), (26,0), (6,23), (33,11), (20,25), (10,33), (2,35)`;
  twisted by `T̄ = (0,0)`: `(0,0), (24,13), (27,4), (32,3), (25,33), (8,6), (36,0), (8,31), (25,4), (32,34), (27,33), (24,24)`.
* minus: `∞, (2,2), (11,11), (0,0), (11,26), (2,35), ∞, (2,2), (11,11), (0,0), (11,26), (2,35)`;
  twisted: `(0,0), (11,26), (2,35), ∞, (2,2), (11,11), (0,0), (11,26), (2,35), ∞, (2,2), (11,11)`.
Paired-x comparison (`pairedXRows`): the indices `n (mod 12)` where plus and minus rows have the same
projective abscissa are `{0, 1, 11}` for the plain row and `{0}` for the `T`-twisted row
(`AllowedRow`, `commonX_row_classification_fin` in `GaussianP37Bridge`).

Torsion of `E₀(ℚ(i))` and `E₁(ℚ(i))` (file `GaussianActualTorsion.lean`): for torsion `Q ∈ E₀(ℚ(i))`,
`reduceE0Plus(12Q) = finiteMul(red Q, 12) = ∞`, so `σ₊(12Q) ∈ infinityKernel`; a torsion point of a
torsion-free group is `0`, and injectivity of `σ₊` on points gives `12Q = 0`
(`gaussianE0_torsion_twelve`, via `eq_zero_of_torsion_map_mem_infinityKernel`); similarly `42Q = 0`
(`gaussianE0_torsion_fortyTwo`), so `6Q = 0` (`gaussianE0_torsion_six`). Three-torsion is excluded at the
inert prime 11 (`GaussianThreeTorsion`), two-torsion is `{0, T}` (`GaussianTwoTorsion`, discriminant
`4(1+4i)` of norm `272`, not a square), rank one from 2-descent (`GaussianMordellWeil.gaussianE0_freeRank`),
hence `E₀(ℚ(i)) ≅ ℤ × ℤ/2` (`gaussianE0_equiv`). For `E₁`: `28Q = 0` and `34Q = 0` ⇒ `2Q = 0`
(`gaussianE1_torsion_two`); rank zero ⇒ `E₁(ℚ(i)) = {0, T₁}` (`gaussianE1_point_classified`).

### a.6 The cover point and the two boundary rows (files `GaussianP37Bridge.lean`, `GaussianCoverReductionActual.lean`)

Every `C ∈ C₀(ℚ)` has `x(C.toE0) = 2u² ∈ ℚ` (`coverZero_toE0_hasRationalAffineX`). A rational abscissa is
sent to the *same* element of `ℚ₃₇` by `σ₊` and `σ₋`, so the projective abscissae of `σ₊(Q)` and `σ₋(Q)`
agree (`mapE0PointLocal_xRep_eq_of_rational`), hence `sameX (reduceE0Plus Q) (reduceE0Minus Q) = true`
(`reduceE0_sameX_of_rational`, `reduceE0_common_of_rational`): either both reduce to `∞` or both to
affine points with the same `x̄` (`CommonReducedX`). This is the "paired x-coordinates" argument.

Two boundary rows are excluded by residue nonsquares (`GaussianCoverReductionActual`):
* If `reduceE0Plus(C.toE0) = ∞` then `‖u‖₃₇ > 1`; with `t = 1/u`, `(v/u²)² = 2 − t⁴ + r₊(2t² − 2t⁴)` is a 37-adic
  integer reducing to `2`, so `2` would be a square mod 37 (`infinity_forces_leading_square_actual`);
  but `2` is a nonsquare (`GaussianP37.infinityDisk_no_square_root`, `isSquareMod 37 2 = false`).
* If `reduceE0Plus(C.toE0) = (0,0)` then `ū = 0` and `v² = q(u)` reduces to `q(0) = −1 − 2i ≡ −1 − 12 = 24`
  (`torsion_forces_q0_square_actual`); `24` is a nonsquare mod 37 (`torsionDisk_no_square_root`).
Combined with the paired-x classification this leaves only the plain rows `n ≡ ±1 (mod 12)`
(`coverZero_survivingRows`, and index-independent form
`GaussianIndexIndependentReduction.coverZero_indexIndependent_survivingRows_actual`).

### a.7 Translated coordinates at ±P (file `GaussianFormalLocal.lean`)

For a kernel point `S = (x,y)` (`‖x‖ > 1`) and `sign = ±1`, the abscissa of `S + (2, 2·sign)` is
`((2·sign − y)/(2 − x))² − A − 2 − x`. Writing the secant slope as
`−(1 + 2·sign·r t)/(t(1 − 2r))` (`secant_slope_eq_formal`) and using `r = t²(1+Ar+Br²)`, the exact
factorization `translationNumerator = r²·(…)` (`GaussianP37.translationAtP_factor`, `translationAtNegP_factor`,
`translationNumeratorLocal_factor`) gives
`x(S ± P) = 2 ± 4t + t²·tail`, `tail ∈ ℤ₃₇`
(`exists_integral_first_order_translation`, `exists_integral_translation_at_P`,
`exists_integral_translation_at_negP`; the tail is
`(1+Ar+Br²)·[(B+4A+12) − 4(A+4)r ± 4t((A+4)+(B−4)r) + 4t²(1+Ar+Br²)]/(1−2r)²`).

### a.8 Paired formal separation (files `GaussianPairedFormalNorm.lean`, `GaussianTranslationSeparation.lean`)

Definition (`PairedKernelSeparated P₊ P₋`): `P₊ ∈ infinityKernel plusA plusB`, `P₋ ∈ infinityKernel minusA minusB`,
`‖t(P₊)‖ = ‖t(P₋)‖ =: ρ > 0`, and `‖t(P₊) − t(P₋)‖ = ρ`.
* Stable under `n•` for `37 ∤ n` (norms preserved, and `‖(t(nP₊) − t(nP₋)) − n(t(P₊) − t(P₋))‖ ≤ ρ³ < ρ`)
  (`PairedKernelSeparated.nsmul_of_not_dvd`), under `37•` (all three norms scale by `37⁻¹`; uses `ρ³ < 37⁻¹ρ`)
  (`thirtySeven_nsmul`), hence under every nonzero integer (`nsmul`, `neg`, `zsmul`).
* *Reflected* by `n•` with `37 ∤ n`: if `(nP₊, nP₋)` is separated so is `(P₊, P₋)`
  (`pairedKernelSeparated_of_nsmul_of_not_dvd`, integer wrapper `pairedKernelSeparated_of_natAbs_nsmul_of_not_dvd`).
* The base pair `actualBasePlus = 12•σ₊(P)`, `actualBaseMinus = 12•σ₋(P)` is separated
  (`actualBase_pairSeparated`): `t(12P)₊ = 37·q₊`, `t(12P)₋ = 37·q₋` with `q₊ ≡ 17`, `q₋ ≡ 19 (mod 37)`
  (`GaussianP37ActualTrace.plus_actual_formal_parameter_first_layer`, `minus_actual_formal_parameter_first_layer`),
  so `ρ = 37⁻¹` and `q₊ − q₋ ≡ −2` is a unit.
Separation lemma (`GaussianTranslationSeparation.firstOrderTranslation_eq_impossible`): if `‖t₁‖ = ‖t₂‖ = ‖t₁ − t₂‖ = ρ > 0`,
`ρ < 1`, and `2 + 4s t₁ + t₁²τ₁ = 2 + 4s t₂ + t₂²τ₂` with `s` a unit and `τᵢ` integral, then `‖4s(t₁ − t₂)‖ = ρ`
while `‖t₁²τ₁ − t₂²τ₂‖ ≤ ρ² < ρ`: contradiction (`plusFirstOrderTranslations_ne`, `minusFirstOrderTranslations_ne`).
Application (`GaussianCoverZeroTranslationActual.no_pairedKernelSeparated_sub_P`, `…_sub_negP`, `…_add_P`):
for `C ∈ C₀(ℚ)`, `(σ₊(C.toE0 − P), σ₋(C.toE0 − P))` is never separated, because
`σ±(C.toE0) = σ±(C.toE0 − P) + (2,2)` has the common rational abscissa `2u²` under both embeddings
(`translated_xRep_at_P`), and a.7 writes it as `2 + 4t± + t±²τ±`.

### a.9 What replaces the elliptic logarithm; the all-level formulation (files `GaussianP37.lean`, `GaussianP37Bridge.lean`, `GaussianRationalFormalUniqueness.lean`)

There is no `p`-adic elliptic logarithm anywhere. Its role is played by the formal parameter `t = −x/y` with
the quantitative estimates of a.4 (`|t(nS) − n t(S)| ≤ |t(S)|³`, exact scaling by `37`) and the nonarchimedean
invariant of a.8. An earlier, equivalent bookkeeping is also formalized: `GaussianP37.RationalXCongruentAtAllLevels disk q`
says that for all `n`, `37^{n+1} ∣ (unit·denominator)·numerator + 37·numerator·tail n`, where the unit is
`Disk.linearUnit = 29` at `P` (`4·(17−19) ≡ 29`, `plusLinearCoefficient`) and `8` at `−P` (`−4·(17−19) = 8`,
`minusLinearCoefficient`); `allLevel_unitLinear_unique` / `rationalX_parameter_unique` show the numerator must
vanish (`GaussianRationalFormalUniqueness.numerator_eq_zero_of_cleared_unit_allLevels`,
`parameterAtP_local_unique`, `parameterAtNegP_local_unique`, `point_eq_visible_of_rational_allLevels`).
The structures `Split37FormalKernel`, `Split37TranslationComparison`, `Split37FormalComparison` in
`GaussianP37Bridge` describe how such congruences would be produced; **they are never inhabited** and the final
theorem does not use them — the norm-separation argument of a.8 replaces them. The only theorem of
`GaussianRationalFormalUniqueness` consumed by the final chain is `zsmul_injective_of_isCoprime_84`.

### a.10 Saturation of P: `P = mG + δT` with `m` coprime to 2, 3, 7, 37

Normal form (`GaussianIndexIndependent`): given `e : E₀(ℚ(i)) ≃+ ℤ × ℤ/2`, `G := freeGenerator e = e⁻¹(1,0)`;
`e(T) = (0,1)` is forced (`gaussianE0T_image`); every `Q = kG + εT` with `ε ∈ {0,1}` (`exists_normalForm`);
in particular `P = mG + δT` (`exists_visible_and_point_normalForms`). Nothing assumes `m = ±1`.
* **2** (`visibleCoefficient_odd`): the Kummer map `α : E₀(ℚ(i)) → ℚ(i)^×/squares`, `α(x,y) = [x]`, `α(T) = [B]`
  (`GaussianDescent.alpha`, `alphaHom`), has `α(P) = [2] = [i]` (`classI`) and `α(T) = [−2−4i] = [i(1+2i)]`
  (`classIPi`). If `m` were even, `α(P) = α(δT) ∈ {1, classIPi}`, contradicting `classI_ne_one`,
  `classI_ne_classIPi`. So `m` is odd.
* Odd `ℓ ∣ m ⇒ P = ℓ·(aG + δT)` because odd multiplication fixes `T`
  (`GaussianSaturationBridge.odd_nsmul_twoTorsion`, `point_divisible_of_odd_dvd_freeCoefficient`,
  `visiblePoint_divisible_of_odd_dvd_coefficient`).
* **3** (`GaussianP37SaturationActual.visiblePoint_not_three_divisible`, `three_not_dvd_visiblePoint_coefficient`):
  if `3Q = P` then at the plus prime above 37, `finiteMul(red Q, 3) = (2,2)` with `red Q` in the 48-point table,
  but exhaustive search shows `(2,2) ∉ 3·E₀^{σ₊}(𝔽₃₇)` (`GaussianSaturationFinite.p37_not_three_divisible`).
* **7** (`GaussianP29PolynomialRootBridge.visiblePoint_not_seven_divisible`, `seven_not_dvd_visiblePoint_coefficient`),
  at the split prime above 29 with `i ↦ 12` (`12² = 144 ≡ −1 (mod 29)`; `residueHom29 : ℤ[i] → 𝔽₂₉`), residue
  coefficients `A = 24`, `B = 8`. If `7Q = P` with `Q = (x,y)` (and `Q` of nonzero free coordinate, which follows
  from `m` odd: `visiblePoint_freeCoordinate_ne_zero`), the denominator-free chain
  `Q → 2Q → 3Q → 6Q → 7Q` (`weightedTwo, weightedThree, weightedSix, weightedSeven`) is nondegenerate
  (`2Q, 6Q ∉ {0, ±Q}`), represents the actual multiples (`weightedDouble_represents_double`,
  `weightedAddBase_represents_add`), and its abscissa is `φ₇(x)/ψ₇(x)²` (`weightedSeven_cross`; the explicit
  recurrences agree with Mathlib's `Ψ₂Sq, Ψ₃, preΨ₄, preΨ n, ΨSq 7, Φ 7`: `psiSevenSq_eq_divisionPolynomial`,
  `phiSeven_eq_divisionPolynomial`). Hence `x` is a root of the monic degree-49 polynomial
  `sevenPreimagePolynomial = Φ₇ − 2·Ψ₇²` (`exists_weighted_seven_preimage`, `sevenPreimagePolynomial_monic`),
  so `x ∈ ℤ[i]` (rational root theorem, `exists_gaussianInt_of_root`), and its image in `𝔽₂₉` is a root of the
  reduced polynomial — but `sevenPreimageValue 24 8 x ≠ 0` for all `x ∈ 𝔽₂₉` (`p29_sevenPreimagePolynomial_no_root`).
  (The finite certificate `p29_not_seven_divisible` — `(2,2) ∉ 7·E₀(𝔽₂₉)`, with `#E = 28`, `ord P̄ = 14`,
  `7P̄ = (0,0)` — exists but is *not* used, because no reduction homomorphism is constructed at 29.)
* **37** (`GaussianP37IndexSaturationActual.visiblePoint_not_thirtySeven_divisible`,
  `thirtySeven_not_dvd_visiblePoint_coefficient`): if `37Q = P`, then `V := σ₊(12Q)` lies in the plus kernel
  (`reduceE0Plus(12Q) = ∞` by the exponent 12) and `37V = σ₊(12P)`. By a.4, `‖t(37V)‖ = 37⁻¹‖t(V)‖ < 37⁻¹`.
  But the actual trace gives `t(σ₊(12P)) = 37q` with `q ≡ 17 (mod 37)` a unit, so `‖t(σ₊(12P))‖ = 37⁻¹`.
  Contradiction. (The 157-certificate `p157_not_thirtySeven_divisible`, `i ↦ 28`, `#E = 148`, `ord P̄ = 74`,
  is not used.)
  The actual trace (`GaussianP37ActualTrace`): weighted coordinates `x = X/Z², y = Y/Z³`, chain
  `P → 2P → 3P → 6P → 12P` by `weightedDouble`/`weightedAddP`, reduced mod `37²`:
  plus `12P ↦ (X,Y,Z) ≡ (860, 935, 518)`, `t = −XZ/Y ≡ 629 = 37·17`; minus `(490, 1231, 740)`, `t ≡ 703 = 37·19`
  (`plus_weighted_chain_mod37Sq`, `minus_weighted_chain_mod37Sq`; nondegeneracy from `X(2P) − 2Z(2P)² ≡ 128 ≠ 0`,
  `Y(3P) ≡ 553`, `Y(6P) ≡ 296` at plus, `1217, 777, 1022` at minus). The independent affine certificates
  `GaussianP37.plusFormalParameterTrace` (coefficients `(234, 899)` mod 1369, `6P = (655,370)`, doubling trace
  `⟨998,740,741,1111,740⟩`, parameter `629`) and `minusFormalParameterTrace` (`(1135,466)`, `3P = (0,444)`,
  `t(6P) = 1036`, `t(12P) = 703 = 2·1036 mod 1369`) give the same numbers.
* Packaging (`GaussianIndexCoprime`): `m` odd, `3 ∤ m`, `7 ∤ m` ⇒ `gcd(m, 84) = 1` where `84 = 2²·3·7`
  (`isCoprime_84_of_odd_of_not_dvd_three_of_not_dvd_seven`); `37 ∤ m` ⇒ `gcd(m,37) = 1` (`isCoprime_37_of_not_dvd`).

### a.11 Index-independent bookkeeping (files `GaussianIndexIndependent.lean`, `GaussianIndexIndependentReduction.lean`, `GaussianCoverZeroIndexPair.lean`)

Why `84`: `84 = lcm(12, 42)` is a common multiple of the two split-fibre exponents, so both reductions kill
`84G` for *every* `G` (`reduceE0Plus_eightyFour_nsmul_freeGenerator`, `reduceE0Minus_eightyFour_nsmul_freeGenerator`,
signed versions `…_zsmul_eightyFour_freeGenerator`). Let `n := inverseMod84 m` (`m n ≡ 1 (mod 84)`,
`mul_inverseMod84_modEq`). From `P = mG + δT`, `Q = kG + εT`:
`Q = (kn)•P + (ε − knδ)•T + c•(84G)` for some `c ∈ ℤ` (`exists_row_error_multiple`), i.e.
`Q = globalRowPoint (kn) twist + c•84G` with `twist = rowTwist k n δ ε = plain iff ε ≡ knδ (mod 2)`.
Therefore `reduceE0Plus Q = plusRowPoint (rowResidue k n) twist` with `rowResidue k n = kn mod 12`, and
similarly at minus (`actual_reductions_eq_reindexed_rows`). Rational `x` forces `(kn mod 12, twist)` into
`AllowedRow` (`actual_reindexed_allowedRow`), and the two nonsquare exclusions leave `twist = plain` and
`kn ≡ 1` or `11 (mod 12)` (`coverZero_indexIndependent_survivingRows_actual`).
Then `k ≡ ±m (mod 12)` (`coefficient_modEq_of_inverseMod84_row_one`, `…_row_eleven`), `mε ≡ kδ (mod 2)`
(`torsionCoefficient_modEq_of_plain`), and the exact characteristic-zero identity `m•Q = k•P`
(`indexCleared_point_eq`, `indexIndependent_row_one`, `indexIndependent_row_eleven`). Note that this never
writes `Q = k'P + εT`.
Rational parameters (`parameterAtP`, `parameterAtNegP`): numerator `(k ∓ m)/12`, denominator `|m|` (coprime to 37).

Endgame (`GaussianCoverZeroRowCompletion.coverZero_toE0_eq_visible_or_neg`), row `+P` (row `−P` symmetric):
let `a := (k − m)/12`.
* If `a = 0` then `k = m`, so `m•C.toE0 = m•P`, and multiplication by `m` is injective on `ℤ × ℤ/2` since
  `gcd(m,84) = 1` (`zsmul_injective_of_isCoprime_84`) ⇒ `C.toE0 = P`.
* If `a ≠ 0`: `reduceE0±(C.toE0) = reduceE0±(P) = (2,2)` (row 1), so `σ±(C.toE0 − P) ∈ kernel±`
  (`finiteReducePoint_sub_eq_none_of_eq`); and `m•(C.toE0 − P) = a•(12P)`, so
  `m•σ±(C.toE0 − P) = a•actualBase±`. The base pair is separated, `a•` preserves separation, and `m•` (with
  `37 ∤ m`) reflects it, so `(σ₊(C.toE0 − P), σ₋(C.toE0 − P))` is separated
  (`GaussianCoverZeroIndexPair.pairSeparated_sub_visible_of_row_one`) — contradicting
  `no_pairedKernelSeparated_sub_P`.
Row `−P`: `a := (k + m)/12`, `pairSeparated_sub_neg_visible_of_row_eleven`, `no_pairedKernelSeparated_sub_negP`.

### a.12 Final classification

* `GaussianSession1Completion.gaussianCoverZeroClassified : ∀ C : C₀(ℚ), C.toE0 = P ∨ C.toE0 = −P`.
* `GaussianActualTorsion.gaussianCoverOneEllipticClassified : ∀ C : C₁(ℚ), C.toE1 = 0 ∨ C.toE1 = T₁`,
  in fact `C₁(ℚ) = ∅` (`gaussianCoverOne_empty`): `C.toE1` is affine so `≠ 0`, and `C.toE1 = T₁` would force
  `u = 0`, `w² = −i·q(0) = −2 + i`, `N(w)² = 5`, impossible (`gaussianCoverOne_toE1_ne_torsion`,
  `five_not_rational_square`).
* Either of `±P` has `x = 2`, so `2u² = 2`, `u² = 1` (`gaussianCoverZero_u_sq_eq_one`); every octic point lifts to
  `C₀` or `C₁` by the parity of its reduced denominator (`octic_to_gaussian_cover`, primitive Pythagorean
  triples); so `u = ±1`, `r² = octicRhs(±1) = 1`, `r = ±1`: `octicRationalPointsClassified`
  (`OcticRationalPointsClassified`: the four points `(±1, ±1)`).

---------------------------------------------------------------------------------------------------

## (b) Logical flow to the three endpoints

```
gaussianCoverZeroClassified  (GaussianSession1Completion)
 ├─ GaussianActualTorsion.gaussianE0_equiv : E₀(ℚ(i)) ≃+ ℤ × ℤ/2
 │   ├─ gaussianE0_torsion_twelve / _fortyTwo  ← reduceE0Plus_add, reduceE0Plus_mem_finitePoints,
 │   │     plus_twelve_eq_none_of_mem (native), infinityKernel_isAddTorsionFree, mapE0PointPlusLocalHom_injective
 │   └─ GaussianTorsionNormalForm.gaussianE0_equiv_of_torsion_six  ← GaussianThreeTorsion (inert 11),
 │         GaussianTwoTorsion, GaussianMordellWeil.gaussianE0_freeRank (2-descent)
 ├─ GaussianIndexIndependent.exists_visible_and_point_normalForms : P = mG + δT, C.toE0 = kG + εT
 ├─ GaussianP29PolynomialRootBridge.seven_not_dvd_visiblePoint_coefficient   (7 ∤ m)
 │   └─ exists_weighted_seven_preimage, sevenPreimagePolynomial_monic, p29_sevenPreimagePolynomial_no_root (native)
 └─ GaussianCoverZeroRowCompletion.coverZero_toE0_eq_visible_or_neg
     ├─ visibleCoefficient_odd (Kummer: 2 ∤ m)
     ├─ GaussianP37SaturationActual.three_not_dvd_visiblePoint_coefficient (3 ∤ m)  ← p37_not_three_divisible (native)
     ├─ GaussianP37IndexSaturationActual.thirtySeven_not_dvd_visiblePoint_coefficient (37 ∤ m)
     │     ← plus_actual_formal_parameter_first_layer (t(12P)=37q, q≡17), norm_parameter_37_nsmul_eq
     ├─ GaussianIndexCoprime : gcd(m,84)=1, gcd(m,37)=1
     ├─ GaussianIndexIndependentReduction.coverZero_indexIndependent_survivingRows_actual
     │     ← actual_reductions_eq_reindexed_rows (84G killed), actual_reindexed_allowedRow
     │        (reduceE0_common_of_rational + commonX_row_classification_fin (native)),
     │        split37CoverReductionActual (nonsquares 2, 24 at 37)
     ├─ [a = 0]  zsmul_injective_of_isCoprime_84
     └─ [a ≠ 0]  GaussianCoverZeroIndexPair.pairSeparated_sub_visible_of_row_one / …_row_eleven
           ← actualBase_pairSeparated (17, 19), PairedKernelSeparated.zsmul, pairedKernelSeparated_of_natAbs_nsmul_of_not_dvd,
              finiteReducePoint_sub_eq_none_of_eq
           and GaussianCoverZeroTranslationActual.no_pairedKernelSeparated_sub_P / _sub_negP
           ← exists_integral_translation_at_P/_negP, mapE0PointLocal_xRep_eq_of_rational, plusFirstOrderTranslations_ne

gaussianCoverOneEllipticClassified  (GaussianActualTorsion)
 └─ gaussianE1_point_classified ← gaussianE1_torsion_two (reduceE1Plus_add, e1Plus/Minus exponent certificates,
       kernel torsion-free, injectivity) + GaussianTorsionNormalForm.gaussianE1_point_classified_of_torsion_two
       (rank 0: GaussianMordellWeil.gaussianE1_freeRank; 3-torsion excluded at 11; 2-torsion = {0,T₁})

octicRationalPointsClassified  (GaussianSession1Completion)
 └─ octic_classified_of_gaussian_covers gaussianCoverZeroClassified gaussianCoverOneEllipticClassified
       ← octic_to_gaussian_cover, gaussianCoverZero_u_sq_eq_one, gaussianCoverOne_empty
 └─ consumer: quadratic_cubic_impossible_sharipov (via GaussianCompletion)
```

Reduction-homomorphism dependency chain:
`GaussianGoodReduction → GaussianProjectiveReduction → GaussianProjectiveReductionHom → GaussianFormalLocal →
GaussianFormalKernelDisk → GaussianFormalKernelTorsion`; `GaussianSplit37ReductionActual` (uses
`FormalKernelDisk`, `ReductionSurjective`, `VisibleReduction`, `CoverReductionActual`) produces
`reduceE0Plus_add` etc.; `GaussianE1LocalReduction → GaussianE1Split37ReductionActual` for `E₁`.

---------------------------------------------------------------------------------------------------

## (c) The `native_decide` certificates (what finite computation each one is)

`GaussianFinite.lean` (definitions `finiteAdd` = explicit affine chord-tangent law on `y² = x³+Ax²+Bx` over
`ℤ/pℤ` with `residueInv` by exhaustive search, `finiteMul` = repeated addition, `finitePoints` = exhaustive
enumeration of `x, y ∈ [0,p)`, `finiteOrder` = first `n ≤ 4p+20` with `nP = ∞`, `finiteExponent` = lcm of orders):
* `e0TorsionRows13`, `e0TorsionRows29`, `e1TorsionRows13`, `e1TorsionRows29`: point counts at `p = 13` (`i ↦ 5, 8`):
  `E₀: 12, 18`; `E₁: 16, 10`; at `p = 29` (`i ↦ 12, 17`): `E₀: 28, 38`; `E₁: 32, 22`. (Consumed only by the
  arithmetic-boundary file `GaussianTorsionReduction`, not by the final chain.)
* `indexRow29`: `#E₀(𝔽₂₉) = 28`, `ord(2,2) = 14`, `7·(2,2) = (0,0)`; `indexRow157`: `#E₀(𝔽₁₅₇) = 148`
  (`i ↦ 28`), `ord(2,2) = 74`, `37·(2,2) = (92,0)`. (Not used by the final chain.)
* The homogeneous-space local obstructions mod 4, 8, 16, 32 (2-descent; outside this summary's scope).

`GaussianP37.lean`:
* `splitRoots`: `6² ≡ 31² ≡ 36 (mod 37)`.
* `plusGroupRow`: `e0Coefficients 37 6 = (12,11)`, 48 points, exponent 12, `ord(2,2) = 12`.
* `minusGroupRow`: `(25,22)`, 42 points, exponent 42, `ord(5,3) = 42`, `ord(2,2) = 6`.
* `plusPointRows`, `minusPointRows`: the 12-entry plain and `T`-twisted rows listed in a.5.
* `pairedXRows`: filter of `[0,12)` by `sameX` on the two rows gives `[0,1,11]` (plain), `[0]` (twisted).
* `infinityDisk_quartic_nonsquare`, `infinityDisk_no_square_root`: no `x ∈ [0,37)` with `x² ≡ 2`.
* `torsionDisk_quartic_nonsquare`, `torsionDisk_no_square_root`: `−(1+12) ≡ 24`, no `x` with `x² ≡ 24`.
* `splitRootLifts`: `117², 1252² ≡ 1368 (mod 1369)`, residues 6 and 31.
* `plusFormalParameterTrace`: over `ℤ/1369` with coefficients `(234, 899)` (from `i = 117`): the affine multiples
  `P..6P = (2,2),(10,411),(464,678),(329,1173),(931,347),(655,370)`; denominator-free doubling of `6P` gives
  `⟨N,D,X,Y,Z⟩ = ⟨998,740,741,1111,740⟩` on the weighted curve; `1111` invertible; `t = −XZ/Y ≡ 629 = 37·17`.
* `minusFormalParameterTrace`: coefficients `(1135, 466)` (from `i = 1252`), `P,2P,3P = (2,2),(677,1306),(0,444)`;
  doubling trace of `3P` = `⟨466,888,854,415,888⟩`, `t(6P) = 1036`; second weighted doubling `⟨266,1173,518⟩`,
  `t(12P) = 703 = 37·19 ≡ 2·1036`.

`GaussianFiniteExponent.lean`: `plus_all_twelve` (all 48 plus points killed by 12), `minus_all_fortyTwo`
(all 42 minus points killed by 42), `e1Plus_all_twentyEight` (`e1Coefficients 37 6 = (2,26)`, 28 points, killed by 28),
`e1Minus_all_thirtyFour` (`(2,15)`, 34 points, killed by 34).

`GaussianSaturationFinite.lean`: `finiteDivisible p A B n P` = "some listed `Q` has `nQ = P`".
`p37_not_three_divisible` (`(2,2)` and `(2,2)+(0,0) = (24,13)` are not `3·Q` over `𝔽₃₇`, `i ↦ 6`),
`p29_not_seven_divisible` (`i ↦ 12`, not used), `p157_not_thirtySeven_divisible` (`i ↦ 28`, not used).

`GaussianP37Bridge.lean`: `plusFiniteNeg_row`, `minusFiniteNeg_row` (`interval_cases r <;> native_decide`:
negating row entry `r` gives entry `(12 − r) mod 12`); `finiteMul … 12 = none` facts for the period;
`commonX_row_classification_fin` (`fin_cases r <;> cases twist`: `sameX` on the 24 row pairs implies `AllowedRow`);
`coefficient_decomposition` helpers.

`GaussianGoodReduction.lean`: `splitRootMinus_toZMod` (`−6 = 31` in `ℤ/37`), residue coefficient values
`(12,11)`, `(25,22)`, and `Δ ≠ 0` of both special fibres. `GaussianE1LocalReduction.lean`: `Δ ≠ 0` for the `E₁`
fibres, `2+4·6 = 26`, `2+4·31 = 15`, and equality with `e1PlusCoefficients`, `e1MinusCoefficients`.

`GaussianSplit37ReductionActual.lean` (`native_decide +revert`, statements universally quantified over
`ZMod 37`): `residueSub_val_37`, `residueAdd_val_37`, `residueMul_val_37`, `residuePowTwo_val_37`,
`residueInv_val_37`, `tangentSlope_val_37`, `secantSlope_val_37`, `addX_val_37`, `addY_val_37`,
`finiteCurveRhs_val_37` — the canonical natural representatives of field arithmetic in `𝔽₃₇` agree with the
executable formulas (each a check over all `37^k` inputs, `k ≤ 4`); plus `plusA_residue_val` etc.
(`12, 11, 25, 22`).

`GaussianVisibleReduction.lean`: residues of `P+T`: `−1 − 2·6 ≡ 24`, `1 + 12 = 13`; `−1 − 62 ≡ 11`, `63 ≡ 26`;
`finiteNeg (2,2) = (2,35)`.

`GaussianP37ActualTrace.lean`: `plus_root_lift_unique` / `minus_root_lift_unique` (the only `z ∈ ℤ/1369` with
`z² = −1` and `z ≡ 6` resp. `31` is `117` resp. `1252`); `plus_weighted_chain_mod37Sq`,
`minus_weighted_chain_mod37Sq` (evaluate the polynomial chain `weightedP12` in `ℤ/1369` after substituting
`r₊ ≡ 117`, `r₋ ≡ 1252`: values `128, 553, 296, 860, 935, 518` and `1217, 777, 1022, 490, 1231, 740`);
`plus_parameter_mod37Sq_unique` (`t·935 = −860·518 ⇒ t = 629`), `minus_parameter_mod37Sq_unique`
(`t·1231 = −490·740 ⇒ t = 703`), `plus_divided_parameter_residue_unique` (`37q = 629 ⇒ q ≡ 17`),
`minus_divided_parameter_residue_unique` (`37q = 703 ⇒ q ≡ 19`); nonvanishing of `128, 1217`, and of
`Y(12P) mod 37 = 10` (plus) / its minus analogue, `Z(12P) ≢ 0`.

`GaussianP29SaturationActual.lean`: `residueHom29` well-defined (`12² ≡ −1 (mod 29)`);
`p29_sevenPreimagePolynomial_no_root`: for all 29 values `x ∈ 𝔽₂₉`, the degree-49 recurrence
`sevenPreimageValue 24 8 x ≠ 0`. `GaussianP29PolynomialRootBridge.lean`: `residueHom29 (2i) = 24`,
`residueHom29 (−2−4i) = 8`.

`GaussianP37IndexSaturationActual.lean`: `17 ≠ 0` in `ℤ/37`. `GaussianPairedFormalNorm.lean`: `17 ≠ 0`, `19 ≠ 0`,
`17 − 19 ≠ 0` in `ℤ/37`. `GaussianCoverReductionActual.lean`: `2 ≠ 0`, `−1 − 12 = 24` in `ℤ/37`.
`GaussianIndexIndependentReduction.lean`, `GaussianCoverZeroIndexPair.lean`: row lookups `plusRowPoint 0 plain = none`,
`plusRowPoint 0 torsion = (0,0)`, `plusRowPoint 1 plain = (2,2)`, `plusRowPoint 11 plain = (2,35)` and minus analogues.
`GaussianReductionSurjective.lean`: `2 ≠ 0` in `ℤ/37`.

Everything else in these files is proved by ordinary tactics (`ring`, `field_simp`, `linear_combination`,
`nlinarith` on real norms, ultrametric inequalities, Mathlib's `hensels_lemma`, the Weierstrass group law).

---------------------------------------------------------------------------------------------------

## (d) Subtle points a paper author must not get wrong

1. **Both embeddings are needed, for two different reasons.** (i) The paired-`x` argument compares the reductions of
   the *same* global point under `σ₊` and `σ₋`; only a point with rational `x` has equal projective abscissae in
   both, and only the pair of rows cuts the twelve residue classes down to `{0, ±1}` (a single row would allow
   everything). (ii) The formal separation invariant is a statement about the *pair* `(t₊, t₋)`:
   `‖t₊ − t₋‖ = ‖t₊‖`, which comes from `17 ≢ 19 (mod 37)`. One embedding alone gives no contradiction:
   `x(S+P) = 2 + 4t + …` is consistent for any single `t`.
2. **No elliptic logarithm, no Chabauty-style power series.** The role of the logarithm is played by the formal
   parameter `t = −x/y` and the *inequalities* `‖t(nS) − n t(S)‖ ≤ ‖t(S)‖³`, `‖t(37S)‖ = ‖t(S)‖/37`,
   `‖t(nS)‖ = ‖t(S)‖` for `37 ∤ n`. The "all-level congruence" structures (`Split37FormalKernel`,
   `Split37FormalComparison`) in `GaussianP37Bridge` are never inhabited; the final proof goes through
   `PairedKernelSeparated`. Do not present the linear units `29` and `8` as load-bearing (they are only in the
   unused alternative formulation); what is load-bearing is `q₊ ≡ 17`, `q₋ ≡ 19`, and `17 ≠ 19`.
3. **`P` is not assumed to generate.** The argument is index-independent: `P = mG + δT` with unknown `m`, and only
   `gcd(m, 84) = gcd(m, 37) = 1` is used. Saturation at 2 uses the Kummer classes, at 3 the plus fibre at 37,
   at 7 the seventh division polynomial reduced at `i ↦ 12 (mod 29)`, at 37 the formal parameter of `12P`. The
   number `84 = 4·3·7 = lcm(12, 42)` is chosen so that `84G` reduces to `∞` at both primes above 37 for any
   `G`, which is what lets one replace `G` by `m⁻¹P (mod 84)`. Coprimality with `4` (not just `2`) is needed
   because `ℤ/84` contains `ℤ/4`; oddness suffices.
4. **Translation by `T`.** After reindexing, the row may be `T`-twisted; the twisted row's only paired index is `0`,
   excluded because reduction to `(0,0)` forces `ū = 0` and `q(0) = −1 − 2i ≡ 24`, a nonsquare mod 37. Note that
   this exclusion is done at the *plus* prime only (`24 = −1 − 2·6`); at the minus prime `q(0) ≡ −1 − 62 ≡ 11`
   would have to be checked separately, and is not needed.
5. **Why the reduction is a homomorphism needs proof.** Mathlib (at this version) has no reduction map on points
   nor a formal group; the files prove additivity from scratch by the secant/tangent valuation argument. The
   delicate case is two integral points with the same reduction on the residue two-torsion branch (`ȳ = 0`),
   where the secant numerator `y₁ + y₂` is *not* a unit and the cubic divided difference is used instead.
6. **Torsion-freeness of the kernel is genuinely used twice**: for the torsion bounds `12Q = 0`, `42Q = 0`
   (hence `E₀(ℚ(i))_tors = {0, T}`, `E₁(ℚ(i)) = {0, T₁}`), and for 37-saturation. The estimate `‖t(37S)‖ = ‖t(S)‖/37`
   requires `‖t(S)‖ ≤ 37⁻¹` (automatic from `‖t‖ < 1` in `ℚ₃₇`) so that `‖t‖³ < 37⁻¹‖t‖`.
7. **What `E₁` (rank 0) needs**: only the two split fibres at 37 (`28` and `34` points, `gcd = 2`), the inert-11
   three-torsion exclusion, the two-torsion classification and the 2-descent rank; no formal separation and no
   paired-`x` argument. And the twisted cover is *empty* (not merely classified): `C.toE1 = T₁` would give
   `N(w)² = 5`.
8. **Numerical identities to quote exactly**: `r₊ ≡ 6, 117`; `r₋ ≡ 31, 1252`; residue models `(12,11)`, `(25,22)`,
   `E₁`: `(2,26)`, `(2,15)`; counts `48, 42, 28, 34`; exponents `12, 42`; `ord P̄ = 12` (plus), `6` (minus);
   `t(12P) ≡ 629 = 37·17` (plus), `703 = 37·19` (minus) mod `37²`; nonsquares `2` and `24` mod 37; `A = 24`,
   `B = 8` mod 29 with `i ↦ 12`; `sevenPreimagePolynomial = Φ₇ − 2Ψ₇²` monic of degree `49`.
9. **The 13- and 29-torsion rows and the 157 row** in `GaussianFinite`/`GaussianSaturationFinite` are certificates
   of an earlier plan and are not on the dependency path of the final theorems; the torsion bound comes from 37,
   and 37-saturation from the formal parameter. Likewise `GaussianReductionSurjective` is not needed downstream.
10. **The translation formula's tails depend on the embedding** (`A₊ = 2r₊ ≠ A₋ = 2r₋`) but are integral in both;
    the argument only needs the *common* linear coefficient `±4` and the common rational value of the abscissa.
