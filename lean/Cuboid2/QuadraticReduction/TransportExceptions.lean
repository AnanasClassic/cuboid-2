import Cuboid2.QuadraticReduction.QuotientInverse
import Cuboid2.QuadraticReduction.TransportExceptionData
import Cuboid2.QuadraticReduction.CompactBoundary

/-!
# Exceptional fibres of the reciprocal quotient transport

This file closes the three denominators in the inverse `C8 → E1` map:
the subresultant coefficient `A`, the recovered-ordinate coefficient `a1`,
and the common forward denominator `f3`.  Large elimination steps are checked
as exact sparse integer Bézout identities; rational-root exclusions are
finite projective computations over small prime fields.
-/

namespace Cuboid2

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ## A small reusable rational-root checker -/

private def exceptionPolynomialEval {R : Type} [CommRing R] :
    List ℤ → R → R
  | [], _ => 0
  | coefficient :: rest, x =>
      (coefficient : R) * x ^ rest.length +
        exceptionPolynomialEval rest x

private def exceptionPolynomialHomogeneous {R : Type} [CommRing R] :
    List ℤ → R → R → R
  | [], _, _ => 0
  | coefficient :: rest, n, d =>
      (coefficient : R) * n ^ rest.length +
        d * exceptionPolynomialHomogeneous rest n d

private theorem exceptionPolynomialHomogeneous_eval
    (coefficients : List ℤ) (n d : ℚ) (hd : d ≠ 0)
    (hne : coefficients ≠ []) :
    exceptionPolynomialHomogeneous coefficients n d =
      d ^ (coefficients.length - 1) *
        exceptionPolynomialEval coefficients (n / d) := by
  induction coefficients with
  | nil => exact (hne rfl).elim
  | cons coefficient rest ih =>
      cases rest with
      | nil =>
          simp [exceptionPolynomialHomogeneous, exceptionPolynomialEval]
      | cons next tail =>
          rw [exceptionPolynomialHomogeneous, exceptionPolynomialEval]
          have hi := ih (by simp)
          rw [hi]
          simp only [List.length_cons, Nat.add_sub_cancel]
          rw [div_pow]
          field_simp [hd]
          ring

private theorem exceptionPolynomialHomogeneous_cast
    {R : Type} [CommRing R] (coefficients : List ℤ) (n d : ℤ) :
    ((exceptionPolynomialHomogeneous coefficients n d : ℤ) : R) =
      exceptionPolynomialHomogeneous coefficients (n : R) (d : R) := by
  induction coefficients with
  | nil => simp [exceptionPolynomialHomogeneous]
  | cons coefficient rest ih =>
      simp only [exceptionPolynomialHomogeneous]
      push_cast
      rw [ih]

private theorem exception_rat_num_den_not_both_zero_mod
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 1) (x : ℚ) :
    ¬ ((((x.num : ℤ) : ZMod p) = 0) ∧
      ((((x.den : ℕ) : ℤ) : ZMod p) = 0)) := by
  rintro ⟨hnum, hden⟩
  have hnumInt : (p : ℤ) ∣ x.num :=
    (CharP.intCast_eq_zero_iff (ZMod p) p x.num).mp hnum
  have hnumNat : p ∣ x.num.natAbs := by
    rw [← Int.natCast_dvd]
    exact hnumInt
  have hdenInt : (p : ℤ) ∣ (x.den : ℤ) :=
    (CharP.intCast_eq_zero_iff (ZMod p) p (x.den : ℤ)).mp hden
  have hdenNat : p ∣ x.den := by
    exact_mod_cast hdenInt
  have hgcd : p ∣ Nat.gcd x.num.natAbs x.den :=
    Nat.dvd_gcd hnumNat hdenNat
  rw [x.reduced.gcd_eq_one] at hgcd
  exact hp (Nat.dvd_one.mp hgcd)

private theorem exceptionPolynomial_ne_zero_of_mod
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 1)
    (coefficients : List ℤ) (hne : coefficients ≠ [])
    (hnonzero : ∀ n d : ZMod p, ¬ (n = 0 ∧ d = 0) →
      exceptionPolynomialHomogeneous coefficients n d ≠ 0)
    (x : ℚ) :
    exceptionPolynomialEval coefficients x ≠ 0 := by
  intro hx
  have hdenZ : (x.den : ℤ) ≠ 0 := by
    exact_mod_cast (Rat.den_nz x)
  have hhom := exceptionPolynomialHomogeneous_eval coefficients
    (x.num : ℚ) (x.den : ℚ) (by exact_mod_cast hdenZ) hne
  rw [Rat.num_div_den, hx, mul_zero] at hhom
  have hcastQ := exceptionPolynomialHomogeneous_cast (R := ℚ)
    coefficients x.num (x.den : ℤ)
  have hhomZ :
      exceptionPolynomialHomogeneous coefficients x.num (x.den : ℤ) = 0 := by
    exact_mod_cast (hcastQ.trans hhom)
  have hcastMod := exceptionPolynomialHomogeneous_cast (R := ZMod p)
    coefficients x.num (x.den : ℤ)
  have hmod :
      exceptionPolynomialHomogeneous coefficients
        ((x.num : ℤ) : ZMod p)
        (((x.den : ℕ) : ℤ) : ZMod p) = 0 := by
    rw [← hcastMod, hhomZ]
    norm_num
  exact hnonzero _ _
    (exception_rat_num_den_not_both_zero_mod p hp x) hmod

/-! ## Rational-root factors used by the three audits -/

/-- First irreducible factor in the `A=0` elimination. -/
def quotientInverseExceptionD1 (t : ℚ) : ℚ :=
  1331 * t ^ 2 - 12 * t - 1444

/-- Second irreducible factor in the `A=0` elimination. -/
def quotientInverseExceptionD2 (t : ℚ) : ℚ :=
  256 * t ^ 3 + 48 * t ^ 2 - 729 * t + 361

/-- Degree-eight irreducible factor in the `A=0` elimination. -/
def quotientInverseExceptionD8 (t : ℚ) : ℚ :=
  1000 * t ^ 8 - 4312 * t ^ 7 + 1720 * t ^ 6 +
    7260 * t ^ 5 - 677 * t ^ 4 - 3257 * t ^ 3 -
    983 * t ^ 2 - 107 * t - 4

private def exceptionD1Coefficients : List ℤ :=
  [1331, -12, -1444]

private def exceptionD2Coefficients : List ℤ :=
  [256, 48, -729, 361]

private def exceptionD8Coefficients : List ℤ :=
  [1000, -4312, 1720, 7260, -677, -3257, -983, -107, -4]

private def exceptionMinusOneCubicCoefficients : List ℤ :=
  [1, -69, -117, -79]

private def exceptionResultantCubicCoefficients : List ℤ :=
  [3, 1, -19, 16]

private theorem exceptionMod13_nonzero :
    (∀ n d : ZMod 13, ¬ (n = 0 ∧ d = 0) →
      exceptionPolynomialHomogeneous exceptionD1Coefficients n d ≠ 0) ∧
    (∀ n d : ZMod 13, ¬ (n = 0 ∧ d = 0) →
      exceptionPolynomialHomogeneous exceptionD2Coefficients n d ≠ 0) ∧
    (∀ n d : ZMod 13, ¬ (n = 0 ∧ d = 0) →
      exceptionPolynomialHomogeneous exceptionD8Coefficients n d ≠ 0) ∧
    (∀ n d : ZMod 13, ¬ (n = 0 ∧ d = 0) →
      exceptionPolynomialHomogeneous
        exceptionMinusOneCubicCoefficients n d ≠ 0) ∧
    (∀ n d : ZMod 13, ¬ (n = 0 ∧ d = 0) →
      exceptionPolynomialHomogeneous
        exceptionResultantCubicCoefficients n d ≠ 0) := by
  native_decide

theorem quotientInverseExceptionD1_ne_zero (t : ℚ) :
    quotientInverseExceptionD1 t ≠ 0 := by
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have h := exceptionPolynomial_ne_zero_of_mod 13 (by norm_num)
    exceptionD1Coefficients (by decide) exceptionMod13_nonzero.1 t
  intro ht
  apply h
  unfold quotientInverseExceptionD1 at ht
  dsimp [exceptionD1Coefficients, exceptionPolynomialEval]
  ring_nf at ht ⊢
  exact ht

theorem quotientInverseExceptionD2_ne_zero (t : ℚ) :
    quotientInverseExceptionD2 t ≠ 0 := by
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have h := exceptionPolynomial_ne_zero_of_mod 13 (by norm_num)
    exceptionD2Coefficients (by decide) exceptionMod13_nonzero.2.1 t
  intro ht
  apply h
  unfold quotientInverseExceptionD2 at ht
  dsimp [exceptionD2Coefficients, exceptionPolynomialEval]
  ring_nf at ht ⊢
  exact ht

theorem quotientInverseExceptionD8_ne_zero (t : ℚ) :
    quotientInverseExceptionD8 t ≠ 0 := by
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have h := exceptionPolynomial_ne_zero_of_mod 13 (by norm_num)
    exceptionD8Coefficients (by decide) exceptionMod13_nonzero.2.2.1 t
  intro ht
  apply h
  unfold quotientInverseExceptionD8 at ht
  dsimp [exceptionD8Coefficients, exceptionPolynomialEval]
  ring_nf at ht ⊢
  exact ht

private theorem exceptionMinusOneCubic_ne_zero (t : ℚ) :
    t ^ 3 - 69 * t ^ 2 - 117 * t - 79 ≠ 0 := by
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have h := exceptionPolynomial_ne_zero_of_mod 13 (by norm_num)
    exceptionMinusOneCubicCoefficients (by decide)
    exceptionMod13_nonzero.2.2.2.1 t
  intro ht
  apply h
  dsimp [exceptionMinusOneCubicCoefficients, exceptionPolynomialEval]
  ring_nf at ht ⊢
  exact ht

private theorem exceptionResultantCubic_ne_zero (t : ℚ) :
    3 * t ^ 3 + t ^ 2 - 19 * t + 16 ≠ 0 := by
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have h := exceptionPolynomial_ne_zero_of_mod 13 (by norm_num)
    exceptionResultantCubicCoefficients (by decide)
    exceptionMod13_nonzero.2.2.2.2 t
  intro ht
  apply h
  dsimp [exceptionResultantCubicCoefficients, exceptionPolynomialEval]
  ring_nf at ht ⊢
  exact ht

private def exceptionHalfQuinticCoefficients : List ℤ :=
  [1, 37, -23, -206, 241, -71]

private def exceptionPlusQuinticCoefficients : List ℤ := [
  145186336313572027609325799744136915584786826733926217310570871,
  6852200203548396432679759053847266778957535415384277621272571363,
  -5540006350779251837483708699993720975032876660385796405258349601,
  -40099037728084585350911840368601974827735720685487918845858676210,
  44982060090316411167687790749852565065709456687246572803611370791,
  -12464895883141888366851814707846733611017536021758095442591159089
]

private def exceptionLimitQuinticCoefficients : List ℤ := [
  158850809530653862669161159986115858392594057287485035676208263303438013659382934683322132102431340677255,
  4803050338192938943735072487223519636811056882395735180543841910066516254069709923681200009086331612377939,
  -2496366407617200132814723706977035587810048099797458836912272052121396790372493871230441330536254435758513,
  -25979921548039887254302779516128996545301955755902272831814563633102574087616425726594884794378551543193714,
  31358098769202167002506598998256397143506604150289530450271576098682054248709641491343379512549520922195703,
  -9668383435154321032799954310415393003253355775284047011287950528069045330205632347948454409970551432449729
]

private theorem exceptionMod2_nonzero :
    (∀ n d : ZMod 2, ¬ (n = 0 ∧ d = 0) →
      exceptionPolynomialHomogeneous
        exceptionHalfQuinticCoefficients n d ≠ 0) ∧
    (∀ n d : ZMod 2, ¬ (n = 0 ∧ d = 0) →
      exceptionPolynomialHomogeneous
        exceptionPlusQuinticCoefficients n d ≠ 0) ∧
    (∀ n d : ZMod 2, ¬ (n = 0 ∧ d = 0) →
      exceptionPolynomialHomogeneous
        exceptionLimitQuinticCoefficients n d ≠ 0) := by
  native_decide

private theorem exceptionHalfQuintic_ne_zero (t : ℚ) :
    t ^ 5 + 37 * t ^ 4 - 23 * t ^ 3 - 206 * t ^ 2 +
      241 * t - 71 ≠ 0 := by
  let _ : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h := exceptionPolynomial_ne_zero_of_mod 2 (by norm_num)
    exceptionHalfQuinticCoefficients (by decide)
    exceptionMod2_nonzero.1 t
  intro ht
  apply h
  dsimp [exceptionHalfQuinticCoefficients, exceptionPolynomialEval]
  ring_nf at ht ⊢
  exact ht

private theorem exceptionPlusQuintic_ne_zero (t : ℚ) :
    exceptionPolynomialEval exceptionPlusQuinticCoefficients t ≠ 0 := by
  let _ : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact exceptionPolynomial_ne_zero_of_mod 2 (by norm_num)
    exceptionPlusQuinticCoefficients (by decide)
    exceptionMod2_nonzero.2.1 t

private theorem exceptionLimitQuintic_ne_zero (t : ℚ) :
    exceptionPolynomialEval exceptionLimitQuinticCoefficients t ≠ 0 := by
  let _ : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact exceptionPolynomial_ne_zero_of_mod 2 (by norm_num)
    exceptionLimitQuinticCoefficients (by decide)
    exceptionMod2_nonzero.2.2 t

private def exceptionF3YCoefficientCoefficients : List ℤ :=
  [24, -293, 2857, -3491]

private theorem exceptionF3YCoefficientMod41_nonzero :
    ∀ n d : ZMod 41, ¬ (n = 0 ∧ d = 0) →
      exceptionPolynomialHomogeneous
        exceptionF3YCoefficientCoefficients n d ≠ 0 := by
  native_decide

private theorem exceptionF3YCoefficient_ne_zero (t : ℚ) :
    24 * t ^ 3 - 293 * t ^ 2 + 2857 * t - 3491 ≠ 0 := by
  let _ : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  have h := exceptionPolynomial_ne_zero_of_mod 41 (by norm_num)
    exceptionF3YCoefficientCoefficients (by decide)
    exceptionF3YCoefficientMod41_nonzero t
  intro ht
  apply h
  dsimp [exceptionF3YCoefficientCoefficients, exceptionPolynomialEval]
  ring_nf at ht ⊢
  exact ht

private def exceptionSimultaneous19Coefficients : List ℤ := [
  1003290624, -104776187904, -12751504911360,
  2631189869549568, -170810731888777728,
  5339424166353904896, -83279179393139415168,
  614346084096703888512, -2529245851196468776032,
  6028382951872188168912, -6600540413294354517724,
  -5465000895657705588936, 30383757679556937404072,
  -42357162867729161731660, 13973836128360833458095,
  35119310776956421480894, -55352507773645600866372,
  36898213103427801808800, -12337763653073475200000,
  1703243972271104000000
]

private theorem exceptionSimultaneous19Mod31_nonzero :
    ∀ n d : ZMod 31, ¬ (n = 0 ∧ d = 0) →
      exceptionPolynomialHomogeneous
        exceptionSimultaneous19Coefficients n d ≠ 0 := by
  native_decide

private theorem exceptionSimultaneous19_ne_zero (t : ℚ) :
    exceptionPolynomialEval exceptionSimultaneous19Coefficients t ≠ 0 := by
  let _ : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  exact exceptionPolynomial_ne_zero_of_mod 31 (by norm_num)
    exceptionSimultaneous19Coefficients (by decide)
    exceptionSimultaneous19Mod31_nonzero t

private theorem rational_sq_ne_five (t : ℚ) :
    t ^ 2 ≠ 5 := by
  intro ht
  have : IsSquare (5 : ℚ) := ⟨t, by simpa [pow_two] using ht.symm⟩
  norm_num at this

private theorem rational_golden_quadratic_ne_zero (t : ℚ) :
    t ^ 2 - t - 1 ≠ 0 := by
  intro ht
  have hsquare : (2 * t - 1) ^ 2 = 5 := by
    nlinarith
  exact rational_sq_ne_five (2 * t - 1) hsquare

/-! ## Sparse Bézout replay for `A=0` -/

private def exceptionUMinusOneTerms : List TransportUVTerm :=
  [(1, 0, 1), (0, 0, -1)]

private def exceptionUPlusOneTerms : List TransportUVTerm :=
  [(1, 0, 1), (0, 0, 1)]

private def exceptionTwoUMinusOneTerms : List TransportUVTerm :=
  [(1, 0, 2), (0, 0, -1)]

private def exceptionD1Terms : List TransportUVTerm :=
  [(2, 0, 1331), (1, 0, -12), (0, 0, -1444)]

private def exceptionD2Terms : List TransportUVTerm :=
  [(3, 0, 256), (2, 0, 48), (1, 0, -729), (0, 0, 361)]

private def exceptionD8Terms : List TransportUVTerm := [
  (8, 0, 1000), (7, 0, -4312), (6, 0, 1720), (5, 0, 7260),
  (4, 0, -677), (3, 0, -3257), (2, 0, -983), (1, 0, -107),
  (0, 0, -4)
]

private def exceptionAFactorProductTerms : List TransportUVTerm :=
  transportMulUVTerms [(0, 0, 4)]
    (transportMulUVTerms (transportPowUVTerms exceptionUMinusOneTerms 4)
      (transportMulUVTerms (transportPowUVTerms exceptionUPlusOneTerms 4)
        (transportMulUVTerms
          (transportPowUVTerms exceptionTwoUMinusOneTerms 18)
          (transportMulUVTerms exceptionD1Terms
            (transportMulUVTerms (transportPowUVTerms exceptionD2Terms 2)
              (transportPowUVTerms exceptionD8Terms 2))))))

/-- The univariate factor forced by a common affine zero of `C8` and `A`. -/
def quotientInverseAExceptionFactor (U : ℚ) : ℚ :=
  4 * (U - 1) ^ 4 * (U + 1) ^ 4 * (2 * U - 1) ^ 18 *
    quotientInverseExceptionD1 U * quotientInverseExceptionD2 U ^ 2 *
    quotientInverseExceptionD8 U ^ 2

private theorem exceptionC8Terms_explicit :
    transportExceptionC8Terms = [
      (6, 0, 16), (5, 1, -128),
      (4, 3, 44), (4, 2, 272), (4, 1, 32), (4, 0, 64),
      (3, 4, -76), (3, 3, -256), (3, 2, -180), (3, 1, -128),
      (3, 0, -32),
      (2, 6, -1), (2, 5, 32), (2, 4, 134), (2, 3, 228),
      (2, 2, 87), (2, 1, 148), (2, 0, -44),
      (1, 5, -34), (1, 4, -80), (1, 3, -60), (1, 2, -164),
      (1, 1, 94), (1, 0, -12),
      (0, 4, 31), (0, 3, 48), (0, 2, -46), (0, 1, 12),
      (0, 0, -1)
    ] := by
  native_decide

private theorem exceptionC8Terms_eval (U V : ℚ) :
    transportEvalUVTerms transportExceptionC8Terms U V =
      reciprocalQuotientC8 U V := by
  rw [exceptionC8Terms_explicit]
  simp [transportEvalUVTerms, transportEvalUVTerm, reciprocalQuotientC8]
  ring

private theorem exceptionAFactorTerms_product :
    transportExceptionAFactorTerms = exceptionAFactorProductTerms := by
  native_decide

private theorem exceptionAFactorTerms_eval (U V : ℚ) :
    transportEvalUVTerms transportExceptionAFactorTerms U V =
      quotientInverseAExceptionFactor U := by
  rw [exceptionAFactorTerms_product]
  unfold exceptionAFactorProductTerms
  repeat' rw [transportEvalMulUVTerms]
  repeat' rw [transportEvalPowUVTerms]
  norm_num [exceptionUMinusOneTerms, exceptionUPlusOneTerms,
    exceptionTwoUMinusOneTerms, exceptionD1Terms, exceptionD2Terms,
    exceptionD8Terms, transportEvalUVTerms, transportEvalUVTerm,
    quotientInverseAExceptionFactor, quotientInverseExceptionD1,
    quotientInverseExceptionD2, quotientInverseExceptionD8]
  ring

private theorem exceptionA_sparse_bezout :
    transportAddUVTerms
        (transportMulUVTerms transportExceptionABezoutLeftTerms
          transportExceptionC8Terms)
        (transportMulUVTerms transportExceptionABezoutRightTerms
          quotientInverseACertificateTerms) =
      transportExceptionAFactorTerms := by
  native_decide

/--
Exact affine Bézout consequence for the inverse `x` denominator.
The identity is checked coefficientwise by the sparse integer normalizer.
-/
theorem quotientInverseA_exception_bezout (U V : ℚ) :
    transportEvalUVTerms transportExceptionABezoutLeftTerms U V *
          reciprocalQuotientC8 U V +
        transportEvalUVTerms transportExceptionABezoutRightTerms U V *
          quotientInverseA U V =
      quotientInverseAExceptionFactor U := by
  have h := congrArg (fun terms => transportEvalUVTerms terms U V)
    exceptionA_sparse_bezout
  rw [transportEvalAddUVTerms, transportEvalMulUVTerms,
    transportEvalMulUVTerms, exceptionC8Terms_eval,
    exceptionAFactorTerms_eval] at h
  exact h

private theorem reciprocalQuotientC8_one (V : ℚ) :
    reciprocalQuotientC8 1 V = -(V - 1) ^ 4 * (V + 3) ^ 2 := by
  norm_num [reciprocalQuotientC8]
  ring

private theorem reciprocalQuotientC8_neg_one (V : ℚ) :
    reciprocalQuotientC8 (-1) V =
      -(V + 1) ^ 3 * (V ^ 3 - 69 * V ^ 2 - 117 * V - 79) := by
  norm_num [reciprocalQuotientC8]
  ring

private theorem reciprocalQuotientC8_half (V : ℚ) :
    reciprocalQuotientC8 (1 / 2) V =
      -(V - 1) *
        (V ^ 5 + 37 * V ^ 4 - 23 * V ^ 3 -
          206 * V ^ 2 + 241 * V - 71) / 4 := by
  norm_num [reciprocalQuotientC8]
  ring

private theorem quotientInverseA_exception_one_impossible
    {V : ℚ} (hC8 : reciprocalQuotientC8 1 V = 0)
    (hproduct : IsSquare (1 * V)) (hproductOne : 1 * V ≠ 1) :
    False := by
  rw [reciprocalQuotientC8_one] at hC8
  have hzero :
      (V - 1) ^ 4 = 0 ∨ (V + 3) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hC8 with h | h
    · exact Or.inl (neg_eq_zero.mp h)
    · exact Or.inr h
  rcases hzero with h | h
  · exact hproductOne (by
      have : V - 1 = 0 :=
        (pow_eq_zero_iff (by norm_num : 4 ≠ 0)).mp h
      linarith)
  · have hV : V = -3 := by
      have : V + 3 = 0 :=
        (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp h
      linarith
    rw [hV] at hproduct
    norm_num [Rat.isSquare_iff] at hproduct

private theorem quotientInverseA_exception_neg_one_impossible
    {V : ℚ} (hC8 : reciprocalQuotientC8 (-1) V = 0)
    (hproductOne : (-1) * V ≠ 1) :
    False := by
  rw [reciprocalQuotientC8_neg_one] at hC8
  have hzero :
      (V + 1) ^ 3 = 0 ∨
        V ^ 3 - 69 * V ^ 2 - 117 * V - 79 = 0 := by
    rcases mul_eq_zero.mp hC8 with h | h
    · exact Or.inl (neg_eq_zero.mp h)
    · exact Or.inr h
  rcases hzero with h | h
  · apply hproductOne
    have : V + 1 = 0 :=
      (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp h
    nlinarith
  · exact exceptionMinusOneCubic_ne_zero V h

private theorem quotientInverseA_exception_half_impossible
    {V : ℚ} (hC8 : reciprocalQuotientC8 (1 / 2) V = 0)
    (hproduct : IsSquare ((1 / 2) * V)) :
    False := by
  rw [reciprocalQuotientC8_half] at hC8
  have hproductZero :
      -(V - 1) *
        (V ^ 5 + 37 * V ^ 4 - 23 * V ^ 3 -
          206 * V ^ 2 + 241 * V - 71) = 0 := by
    linarith
  rcases mul_eq_zero.mp hproductZero with h | h
  · have hV : V = 1 := by linarith
    have hsquare : IsSquare (1 / 2 : ℚ) := by
      simpa [hV] using hproduct
    norm_num [Rat.isSquare_iff] at hsquare
  · exact exceptionHalfQuintic_ne_zero V h

/--
The inverse subresultant coefficient cannot vanish on the admissible
two-character locus of `C8`.
-/
theorem quotientInverseA_ne_zero_of_admissible
    {U V : ℚ} (hC8 : reciprocalQuotientC8 U V = 0)
    (hproduct : IsSquare (U * V)) (hproductOne : U * V ≠ 1) :
    quotientInverseA U V ≠ 0 := by
  intro hA
  have hbezout := quotientInverseA_exception_bezout U V
  rw [hC8, hA, mul_zero, mul_zero, zero_add] at hbezout
  symm at hbezout
  unfold quotientInverseAExceptionFactor at hbezout
  rcases mul_eq_zero.mp hbezout with h | hd8Power
  · rcases mul_eq_zero.mp h with h | hd2Power
    · rcases mul_eq_zero.mp h with h | hd1
      · rcases mul_eq_zero.mp h with h | hUhalfPower
        · rcases mul_eq_zero.mp h with h | hUm1Power
          · rcases mul_eq_zero.mp h with hfalse | hU1Power
            · norm_num at hfalse
            · have hU1 : U - 1 = 0 :=
                (pow_eq_zero_iff (by norm_num : 4 ≠ 0)).mp hU1Power
              have hU : U = 1 := sub_eq_zero.mp hU1
              subst U
              exact quotientInverseA_exception_one_impossible
                hC8 hproduct hproductOne
          · have hUm1 : U + 1 = 0 :=
              (pow_eq_zero_iff (by norm_num : 4 ≠ 0)).mp hUm1Power
            have hU : U = -1 := by linarith
            subst U
            exact quotientInverseA_exception_neg_one_impossible
              hC8 hproductOne
        · have hUhalf : 2 * U - 1 = 0 :=
            (pow_eq_zero_iff (by norm_num : 18 ≠ 0)).mp hUhalfPower
          have hU : U = 1 / 2 := by linarith
          subst U
          exact quotientInverseA_exception_half_impossible hC8 hproduct
      · exact quotientInverseExceptionD1_ne_zero U hd1
    · have hd2 : quotientInverseExceptionD2 U = 0 :=
        (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hd2Power
      exact quotientInverseExceptionD2_ne_zero U hd2
  · have hd8 : quotientInverseExceptionD8 U = 0 :=
      (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hd8Power
    exact quotientInverseExceptionD8_ne_zero U hd8

/-! ## The recovered-ordinate denominator `a1` -/

private def exceptionF1YCoefficient (x : ℚ) : ℚ :=
  24 * x ^ 3 - 2186 * x ^ 2 + 4524 * x - 2982

private def exceptionF2YCoefficient (x : ℚ) : ℚ :=
  24 * x ^ 3 - 1579 * x ^ 2 + 3636 * x - 2391

private def exceptionF3YCoefficient (x : ℚ) : ℚ :=
  24 * x ^ 3 - 293 * x ^ 2 + 2857 * x - 3491

private def exceptionF3Constant (x : ℚ) : ℚ :=
  583 * x ^ 4 - 715 * x ^ 3 - 3476 * x ^ 2 +
    9529 * x - 7107

private def exceptionSimultaneous19 (x : ℚ) : ℚ :=
  exceptionPolynomialEval exceptionSimultaneous19Coefficients x

private theorem exceptionSimultaneous19_def (x : ℚ) :
    exceptionSimultaneous19 x =
      1003290624 * x ^ 19 - 104776187904 * x ^ 18 -
      12751504911360 * x ^ 17 + 2631189869549568 * x ^ 16 -
      170810731888777728 * x ^ 15 +
      5339424166353904896 * x ^ 14 -
      83279179393139415168 * x ^ 13 +
      614346084096703888512 * x ^ 12 -
      2529245851196468776032 * x ^ 11 +
      6028382951872188168912 * x ^ 10 -
      6600540413294354517724 * x ^ 9 -
      5465000895657705588936 * x ^ 8 +
      30383757679556937404072 * x ^ 7 -
      42357162867729161731660 * x ^ 6 +
      13973836128360833458095 * x ^ 5 +
      35119310776956421480894 * x ^ 4 -
      55352507773645600866372 * x ^ 3 +
      36898213103427801808800 * x ^ 2 -
      12337763653073475200000 * x +
      1703243972271104000000 := by
  unfold exceptionSimultaneous19 exceptionSimultaneous19Coefficients
  simp [exceptionPolynomialEval]
  ring

private theorem exceptionSimultaneous19_ne_zero' (x : ℚ) :
    exceptionSimultaneous19 x ≠ 0 :=
  exceptionSimultaneous19_ne_zero x

private theorem quotientInverseA1_coefficient_form (x U : ℚ) :
    quotientInverseA1 x U =
      exceptionF1YCoefficient x - 2 * U * exceptionF3YCoefficient x := by
  rfl

private theorem quotientInverseA2_coefficient_form (x V : ℚ) :
    quotientInverseA2 x V =
      exceptionF2YCoefficient x - V * exceptionF3YCoefficient x := by
  rfl

/--
The simultaneous coefficient specialization of `C8` has only the two
displayed rational linear factors; the remaining degree-19 factor has no
rational root.
-/
private theorem exception_simultaneous_factor_identity (x : ℚ) :
    reciprocalQuotientC8Homogeneous
        (exceptionF1YCoefficient x)
        (exceptionF2YCoefficient x)
        (exceptionF3YCoefficient x) =
      -64 * (x - 2) ^ 3 * (576 * x - 352225) *
        exceptionSimultaneous19 x := by
  rw [exceptionSimultaneous19_def]
  unfold reciprocalQuotientC8Homogeneous
  unfold exceptionF1YCoefficient exceptionF2YCoefficient
  unfold exceptionF3YCoefficient
  ring

private theorem exception_plus_product_not_square :
    ¬ IsSquare
      (((2507654733463 : ℚ) / 5773889467838) *
        ((2739947416519 : ℚ) / 3008594206519)) := by
  norm_num [Rat.isSquare_iff]

private theorem exception_simultaneous_coefficients_impossible
    {x U V : ℚ} (hC8 : reciprocalQuotientC8 U V = 0)
    (ha1 : quotientInverseA1 x U = 0)
    (ha2 : quotientInverseA2 x V = 0)
    (hproduct : IsSquare (U * V)) (hproductOne : U * V ≠ 1) :
    False := by
  have hD : exceptionF3YCoefficient x ≠ 0 := by
    exact exceptionF3YCoefficient_ne_zero x
  have hU :
      exceptionF1YCoefficient x / (2 * exceptionF3YCoefficient x) = U := by
    rw [quotientInverseA1_coefficient_form] at ha1
    field_simp [hD]
    linarith
  have hV :
      exceptionF2YCoefficient x / exceptionF3YCoefficient x = V := by
    rw [quotientInverseA2_coefficient_form] at ha2
    field_simp [hD]
    linarith
  have hhomogeneous := reciprocalQuotientC8_homogeneous
    (A := exceptionF1YCoefficient x)
    (B := exceptionF2YCoefficient x)
    (D := exceptionF3YCoefficient x) hD
  rw [hU, hV, hC8, mul_zero] at hhomogeneous
  rw [exception_simultaneous_factor_identity] at hhomogeneous
  symm at hhomogeneous
  rcases mul_eq_zero.mp hhomogeneous with h | h19
  · rcases mul_eq_zero.mp h with h | hx4
    · rcases mul_eq_zero.mp h with hfalse | hx2Power
      · norm_num at hfalse
      · have hx2 : x = 2 := by
          have : x - 2 = 0 :=
            (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp hx2Power
          linarith
        subst x
        have hU' : U = -1 := by
          norm_num [quotientInverseA1] at ha1
          linarith
        have hV' : V = -1 := by
          norm_num [quotientInverseA2] at ha2
          linarith
        apply hproductOne
        rw [hU', hV']
        norm_num
    · have hx : x = 352225 / 576 := by linarith
      subst x
      have hU' :
          U = (2507654733463 : ℚ) / 5773889467838 := by
        norm_num [quotientInverseA1] at ha1 ⊢
        linarith
      have hV' :
          V = (2739947416519 : ℚ) / 3008594206519 := by
        norm_num [quotientInverseA2] at ha2 ⊢
        linarith
      apply exception_plus_product_not_square
      simpa [hU', hV'] using hproduct
  · exact exceptionSimultaneous19_ne_zero' x h19

private theorem exception_a1_b1_resultant_identity (x U : ℚ) :
    quotientInverseA1 x U * exceptionF3Constant x -
        exceptionF3YCoefficient x * quotientInverseB1 x U =
      (x - 2) * (576 * x - 352225) * (x ^ 2 - 5) *
        (3 * x ^ 3 + x ^ 2 - 19 * x + 16) := by
  unfold quotientInverseA1 quotientInverseB1
  unfold exceptionF3Constant exceptionF3YCoefficient
  ring

private theorem exceptionPlusFibreIdentity (V : ℚ) :
    (2315745408966185703295073348503455949833359378106568183647278421627214129924 : ℚ) *
        reciprocalQuotientC8
          ((2507654733463 : ℚ) / 5773889467838) V =
      -(3008594206519 * V - 2739947416519) *
        exceptionPolynomialEval exceptionPlusQuinticCoefficients V := by
  unfold reciprocalQuotientC8
  unfold exceptionPlusQuinticCoefficients
  simp [exceptionPolynomialEval]
  ring

private theorem exception_plus_fibre_impossible
    {V : ℚ}
    (hC8 : reciprocalQuotientC8
      ((2507654733463 : ℚ) / 5773889467838) V = 0)
    (hproduct :
      IsSquare (((2507654733463 : ℚ) / 5773889467838) * V)) :
    False := by
  have hfibre := exceptionPlusFibreIdentity V
  rw [hC8, mul_zero] at hfibre
  symm at hfibre
  rcases mul_eq_zero.mp hfibre with hlinear | hquintic
  · have hV :
        V = (2739947416519 : ℚ) / 3008594206519 := by
      linarith
    subst V
    exact exception_plus_product_not_square hproduct
  · exact exceptionPlusQuintic_ne_zero V hquintic

private theorem exception_a1_b1_impossible
    {x U V : ℚ} (hC8 : reciprocalQuotientC8 U V = 0)
    (ha1 : quotientInverseA1 x U = 0)
    (hb1 : quotientInverseB1 x U = 0)
    (hproduct : IsSquare (U * V)) (hproductOne : U * V ≠ 1) :
    False := by
  have hresultant := exception_a1_b1_resultant_identity x U
  rw [ha1, hb1, zero_mul, mul_zero, sub_zero] at hresultant
  symm at hresultant
  rcases mul_eq_zero.mp hresultant with h | hcubic
  · rcases mul_eq_zero.mp h with h | hfive
    · rcases mul_eq_zero.mp h with hx2 | hx4
      · have hx : x = 2 := by linarith
        subst x
        have hU : U = -1 := by
          norm_num [quotientInverseA1] at ha1
          linarith
        subst U
        exact quotientInverseA_exception_neg_one_impossible
          hC8 hproductOne
      · have hx : x = 352225 / 576 := by linarith
        subst x
        have hU :
            U = (2507654733463 : ℚ) / 5773889467838 := by
          norm_num [quotientInverseA1] at ha1 ⊢
          linarith
        subst U
        exact exception_plus_fibre_impossible hC8 hproduct
    · apply rational_sq_ne_five x
      linarith
  · exact exceptionResultantCubic_ne_zero x hcubic

/--
The coefficient used to recover the elliptic ordinate is nonzero on the
admissible two-character locus.
-/
theorem quotientInverseA1_ne_zero_of_admissible
    {U V : ℚ} (hC8 : reciprocalQuotientC8 U V = 0)
    (hproduct : IsSquare (U * V)) (hproductOne : U * V ≠ 1) :
    quotientInverseA1 (quotientInverseX U V) U ≠ 0 := by
  let x := quotientInverseX U V
  have hA := quotientInverseA_ne_zero_of_admissible
    hC8 hproduct hproductOne
  have hR5 := quotientInverseR5_zero hC8 hA
  have hdet := quotientInverse_projection_identity x U V
  change quotientInverseR5 x U V = 0 at hR5
  rw [hR5, mul_zero] at hdet
  intro ha1
  change quotientInverseA1 x U = 0 at ha1
  rw [ha1, zero_mul, zero_sub] at hdet
  have hsplit :
      quotientInverseA2 x V = 0 ∨ quotientInverseB1 x U = 0 := by
    exact mul_eq_zero.mp (neg_eq_zero.mp hdet)
  rcases hsplit with ha2 | hb1
  · exact exception_simultaneous_coefficients_impossible
      hC8 ha1 ha2 hproduct hproductOne
  · exact exception_a1_b1_impossible
      hC8 ha1 hb1 hproduct hproductOne

/-! ## The reconstructed common forward denominator `f3` -/

private theorem quotientForwardF3_coefficient_form (x y : ℚ) :
    quotientForwardF3 x y =
      exceptionF3YCoefficient x * y + exceptionF3Constant x := by
  unfold quotientForwardF3 exceptionF3YCoefficient exceptionF3Constant
  ring

private theorem exception_curve_f3_resultant_identity (x : ℚ) :
    exceptionF3Constant x ^ 2 -
        exceptionF3YCoefficient x ^ 2 * (x ^ 3 - 5 * x + 4) =
      -(576 * x - 352225) * (x ^ 2 - 5) *
        (x ^ 2 - x - 1) ^ 3 := by
  unfold exceptionF3Constant exceptionF3YCoefficient
  ring

private theorem exception_curve_f3_forces_removed_x
    {x y : ℚ} (hcurve : e1Residual x y = 0)
    (hF3 : quotientForwardF3 x y = 0) :
    x = 352225 / 576 := by
  rw [quotientForwardF3_coefficient_form] at hF3
  have hresultantZero :
      exceptionF3Constant x ^ 2 -
          exceptionF3YCoefficient x ^ 2 * (x ^ 3 - 5 * x + 4) = 0 := by
    calc
      exceptionF3Constant x ^ 2 -
          exceptionF3YCoefficient x ^ 2 * (x ^ 3 - 5 * x + 4) =
        (exceptionF3YCoefficient x * y + exceptionF3Constant x) *
            (exceptionF3Constant x - exceptionF3YCoefficient x * y) +
          exceptionF3YCoefficient x ^ 2 * e1Residual x y := by
            unfold e1Residual
            ring
      _ = 0 := by rw [hF3, hcurve]; ring
  rw [exception_curve_f3_resultant_identity] at hresultantZero
  rcases mul_eq_zero.mp hresultantZero with h | hgoldenPower
  · rcases mul_eq_zero.mp h with hx4 | hfive
    · linarith
    · exact ((rational_sq_ne_five x) (by linarith)).elim
  · have hgolden : x ^ 2 - x - 1 = 0 :=
      (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp hgoldenPower
    exact (rational_golden_quadratic_ne_zero x hgolden).elim

private def exceptionPlusULinearTerms : List TransportUVTerm :=
  [(1, 0, 5773889467838), (0, 0, -2507654733463)]

private def exceptionLimitULinearTerms : List TransportUVTerm :=
  [(1, 0, 1316366220366073678142),
    (0, 0, -731754020216156986855)]

private def exceptionRemovedFactorProductTerms : List TransportUVTerm :=
  transportMulUVTerms [(0, 0, 4)]
    (transportMulUVTerms (transportPowUVTerms exceptionUMinusOneTerms 4)
      (transportMulUVTerms (transportPowUVTerms exceptionUPlusOneTerms 4)
        (transportMulUVTerms
          (transportPowUVTerms exceptionTwoUMinusOneTerms 16)
          (transportMulUVTerms exceptionPlusULinearTerms
            (transportMulUVTerms exceptionLimitULinearTerms
              (transportMulUVTerms exceptionD1Terms
                (transportMulUVTerms
                  (transportPowUVTerms exceptionD2Terms 2)
                  (transportPowUVTerms exceptionD8Terms 2))))))))

/-- The univariate factor forced by the removed-base inverse equation. -/
def quotientInverseRemovedExceptionFactor (U : ℚ) : ℚ :=
  4 * (U - 1) ^ 4 * (U + 1) ^ 4 * (2 * U - 1) ^ 16 *
    (5773889467838 * U - 2507654733463) *
    (1316366220366073678142 * U - 731754020216156986855) *
    quotientInverseExceptionD1 U * quotientInverseExceptionD2 U ^ 2 *
    quotientInverseExceptionD8 U ^ 2

private theorem exceptionRemovedLinearTerms_construct :
    transportExceptionRemovedLinearTerms =
      transportAddUVTerms
        (transportMulUVTerms [(0, 0, 352225)]
          quotientInverseACertificateTerms)
        (transportMulUVTerms [(0, 0, 576)]
          quotientInverseBCertificateTerms) := by
  native_decide

private theorem exceptionRemovedLinearTerms_eval (U V : ℚ) :
    transportEvalUVTerms transportExceptionRemovedLinearTerms U V =
      352225 * quotientInverseA U V + 576 * quotientInverseB U V := by
  rw [exceptionRemovedLinearTerms_construct, transportEvalAddUVTerms,
    transportEvalMulUVTerms, transportEvalMulUVTerms]
  norm_num [transportEvalUVTerms, transportEvalUVTerm,
    quotientInverseA, quotientInverseB, quotientInverseACertificate,
    quotientInverseBCertificate]

private theorem exceptionRemovedFactorTerms_product :
    transportExceptionRemovedFactorTerms =
      exceptionRemovedFactorProductTerms := by
  native_decide

private theorem exceptionRemovedFactorTerms_eval (U V : ℚ) :
    transportEvalUVTerms transportExceptionRemovedFactorTerms U V =
      quotientInverseRemovedExceptionFactor U := by
  rw [exceptionRemovedFactorTerms_product]
  unfold exceptionRemovedFactorProductTerms
  repeat' rw [transportEvalMulUVTerms]
  repeat' rw [transportEvalPowUVTerms]
  norm_num [exceptionUMinusOneTerms, exceptionUPlusOneTerms,
    exceptionTwoUMinusOneTerms, exceptionPlusULinearTerms,
    exceptionLimitULinearTerms, exceptionD1Terms, exceptionD2Terms,
    exceptionD8Terms, transportEvalUVTerms, transportEvalUVTerm,
    quotientInverseRemovedExceptionFactor, quotientInverseExceptionD1,
    quotientInverseExceptionD2, quotientInverseExceptionD8]
  ring

private theorem exceptionRemoved_sparse_bezout :
    transportAddUVTerms
        (transportMulUVTerms transportExceptionRemovedBezoutLeftTerms
          transportExceptionC8Terms)
        (transportMulUVTerms transportExceptionRemovedBezoutRightTerms
          transportExceptionRemovedLinearTerms) =
      transportExceptionRemovedFactorTerms := by
  native_decide

/-- Exact Bézout consequence on the removed forward-base inverse fibre. -/
theorem quotientInverseRemoved_exception_bezout (U V : ℚ) :
    transportEvalUVTerms transportExceptionRemovedBezoutLeftTerms U V *
          reciprocalQuotientC8 U V +
        transportEvalUVTerms transportExceptionRemovedBezoutRightTerms U V *
          (352225 * quotientInverseA U V + 576 * quotientInverseB U V) =
      quotientInverseRemovedExceptionFactor U := by
  have h := congrArg (fun terms => transportEvalUVTerms terms U V)
    exceptionRemoved_sparse_bezout
  rw [transportEvalAddUVTerms, transportEvalMulUVTerms,
    transportEvalMulUVTerms, exceptionC8Terms_eval,
    exceptionRemovedLinearTerms_eval,
    exceptionRemovedFactorTerms_eval] at h
  exact h

private theorem exception_limit_product_not_square :
    ¬ IsSquare
      (((731754020216156986855 : ℚ) / 1316366220366073678142) *
        ((678770002969523258551 : ℚ) / 632597885616799462855)) := by
  norm_num [Rat.isSquare_iff]

private theorem exceptionLimitFibreIdentity (V : ℚ) :
    (325192404042398863544608309345894566549080301140047753894867017765504318438183863667390691694074276702750009855899897936871684 : ℚ) *
        reciprocalQuotientC8
          ((731754020216156986855 : ℚ) /
            1316366220366073678142) V =
      -(632597885616799462855 * V - 678770002969523258551) *
        exceptionPolynomialEval exceptionLimitQuinticCoefficients V := by
  unfold reciprocalQuotientC8
  unfold exceptionLimitQuinticCoefficients
  simp [exceptionPolynomialEval]
  ring

private theorem exception_limit_fibre_impossible
    {V : ℚ}
    (hC8 : reciprocalQuotientC8
      ((731754020216156986855 : ℚ) / 1316366220366073678142) V = 0)
    (hproduct : IsSquare
      (((731754020216156986855 : ℚ) / 1316366220366073678142) * V)) :
    False := by
  have hfibre := exceptionLimitFibreIdentity V
  rw [hC8, mul_zero] at hfibre
  symm at hfibre
  rcases mul_eq_zero.mp hfibre with hlinear | hquintic
  · have hV :
        V = (678770002969523258551 : ℚ) /
          632597885616799462855 := by
      linarith
    subst V
    exact exception_limit_product_not_square hproduct
  · exact exceptionLimitQuintic_ne_zero V hquintic

private theorem quotientInverse_removed_linear_zero
    {U V : ℚ} (hA : quotientInverseA U V ≠ 0)
    (hx : quotientInverseX U V = 352225 / 576) :
    352225 * quotientInverseA U V + 576 * quotientInverseB U V = 0 := by
  unfold quotientInverseX at hx
  field_simp [hA] at hx
  linarith

private theorem quotientInverse_removed_exception_impossible
    {U V : ℚ} (hC8 : reciprocalQuotientC8 U V = 0)
    (hremoved :
      352225 * quotientInverseA U V + 576 * quotientInverseB U V = 0)
    (hproduct : IsSquare (U * V)) (hproductOne : U * V ≠ 1) :
    False := by
  have hbezout := quotientInverseRemoved_exception_bezout U V
  rw [hC8, hremoved, mul_zero, mul_zero, zero_add] at hbezout
  symm at hbezout
  unfold quotientInverseRemovedExceptionFactor at hbezout
  rcases mul_eq_zero.mp hbezout with h | hd8Power
  · rcases mul_eq_zero.mp h with h | hd2Power
    · rcases mul_eq_zero.mp h with h | hd1
      · rcases mul_eq_zero.mp h with h | hlimit
        · rcases mul_eq_zero.mp h with h | hplus
          · rcases mul_eq_zero.mp h with h | hUhalfPower
            · rcases mul_eq_zero.mp h with h | hUm1Power
              · rcases mul_eq_zero.mp h with hfalse | hU1Power
                · norm_num at hfalse
                · have hU1 : U - 1 = 0 :=
                    (pow_eq_zero_iff (by norm_num : 4 ≠ 0)).mp hU1Power
                  have hU : U = 1 := sub_eq_zero.mp hU1
                  subst U
                  exact quotientInverseA_exception_one_impossible
                    hC8 hproduct hproductOne
              · have hUm1 : U + 1 = 0 :=
                  (pow_eq_zero_iff (by norm_num : 4 ≠ 0)).mp hUm1Power
                have hU : U = -1 := by linarith
                subst U
                exact quotientInverseA_exception_neg_one_impossible
                  hC8 hproductOne
            · have hUhalf : 2 * U - 1 = 0 :=
                (pow_eq_zero_iff (by norm_num : 16 ≠ 0)).mp hUhalfPower
              have hU : U = 1 / 2 := by linarith
              subst U
              exact quotientInverseA_exception_half_impossible hC8 hproduct
          · have hU :
                U = (2507654733463 : ℚ) / 5773889467838 := by
              linarith
            subst U
            exact exception_plus_fibre_impossible hC8 hproduct
        · have hU :
              U = (731754020216156986855 : ℚ) /
                1316366220366073678142 := by
            linarith
          subst U
          exact exception_limit_fibre_impossible hC8 hproduct
      · exact quotientInverseExceptionD1_ne_zero U hd1
    · have hd2 : quotientInverseExceptionD2 U = 0 :=
        (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hd2Power
      exact quotientInverseExceptionD2_ne_zero U hd2
  · have hd8 : quotientInverseExceptionD8 U = 0 :=
      (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hd8Power
    exact quotientInverseExceptionD8_ne_zero U hd8

/--
The reconstructed affine point does not meet the removable common zero of
the three forward numerators on the admissible two-character locus.
-/
theorem quotientInverseF3_ne_zero_of_admissible
    {U V : ℚ} (hC8 : reciprocalQuotientC8 U V = 0)
    (hproduct : IsSquare (U * V)) (hproductOne : U * V ≠ 1) :
    quotientForwardF3
      (quotientInverseX U V) (quotientInverseY U V) ≠ 0 := by
  have hA := quotientInverseA_ne_zero_of_admissible
    hC8 hproduct hproductOne
  have ha1 := quotientInverseA1_ne_zero_of_admissible
    hC8 hproduct hproductOne
  have hcurve := quotientInverse_on_E1 hC8 hA ha1
  intro hF3
  have hx := exception_curve_f3_forces_removed_x hcurve hF3
  have hremoved := quotientInverse_removed_linear_zero hA hx
  exact quotientInverse_removed_exception_impossible
    hC8 hremoved hproduct hproductOne

/-! ## Public admissible and compact wrappers -/

/--
All three rational-function denominators of the explicit inverse are nonzero
on the quotient locus with square product and product different from one.
-/
theorem reciprocalQuotientC8_admissible_denominators
    {U V : ℚ} (hC8 : reciprocalQuotientC8 U V = 0)
    (hproduct : IsSquare (U * V)) (hproductOne : U * V ≠ 1) :
    quotientInverseA U V ≠ 0 ∧
      quotientInverseA1 (quotientInverseX U V) U ≠ 0 ∧
      quotientForwardF3
        (quotientInverseX U V) (quotientInverseY U V) ≠ 0 := by
  have hA := quotientInverseA_ne_zero_of_admissible
    hC8 hproduct hproductOne
  have ha1 := quotientInverseA1_ne_zero_of_admissible
    hC8 hproduct hproductOne
  have hF3 := quotientInverseF3_ne_zero_of_admissible
    hC8 hproduct hproductOne
  exact ⟨hA, ha1, hF3⟩

/--
Unconditional inverse of `C8` on the admissible two-character locus.
The returned affine point has an exact forward roundtrip in both coordinates.
-/
theorem reciprocalQuotientC8_to_E1_admissible
    {U V : ℚ} (hC8 : reciprocalQuotientC8 U V = 0)
    (hproduct : IsSquare (U * V)) (hproductOne : U * V ≠ 1) :
    ∃ P : E1AffinePoint,
      quotientForwardU P.X P.Y = U ∧
        quotientForwardV P.X P.Y = V := by
  obtain ⟨hA, ha1, hF3⟩ :=
    reciprocalQuotientC8_admissible_denominators
      hC8 hproduct hproductOne
  exact reciprocalQuotientC8_to_E1_regular hC8 hA ha1 hF3

/--
Every nonzero compact-model solution off `z²=1` reaches an affine `E1`
point.  The sign-dependent reciprocal ordering is retained in the exact
forward roundtrip.
-/
theorem compact_to_E1AffinePoint
    {ε : PhysicalSign} {z k y : ℚ}
    (hz : z ≠ 0) (hk : k ≠ 0)
    (hSm : z ^ 2 - 1 ≠ 0)
    (h1 : compactF1 ε z k y = 0)
    (h0 : compactF0 ε z k y = 0) :
    ∃ P : E1AffinePoint,
      quotientForwardU P.X P.Y = compactReciprocalU ε z k ∧
        quotientForwardV P.X P.Y = compactReciprocalV ε z k := by
  have hC8 :
      reciprocalQuotientC8
        (compactReciprocalU ε z k) (compactReciprocalV ε z k) = 0 := by
    have h := compact_equations_to_reciprocalQuotientC8
      hz hk hSm h1 h0
    cases ε <;>
      simpa [compactReciprocalU, compactReciprocalV] using h
  obtain ⟨hproduct, hproductOne, _, _⟩ :=
    compact_common_character_facts hz hk hSm h1 h0
  exact reciprocalQuotientC8_to_E1_admissible
    hC8 hproduct hproductOne

end

end Cuboid2
