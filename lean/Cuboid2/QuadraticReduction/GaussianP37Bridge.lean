import Cuboid2.QuadraticReduction.GaussianCover
import Cuboid2.QuadraticReduction.GaussianP37

/-!
# The exact bridge boundary for the split-37 certificates

This file connects actual points of `gaussianE0` to the executable rows in
`GaussianP37`, conditional only on an explicitly packaged pair of
good-reduction maps.  It proves all downstream group-row bookkeeping and the
paired-`x` classification.

No inhabitant of `Split37GoodReduction` is asserted here.  Constructing one
requires projective good reduction at both primes above 37 and proofs that it
is a group homomorphism.  Likewise, the final all-level corollary takes the
finite-level formal congruences explicitly; their production from elliptic
formal-group multiplication is a separate, named boundary.
-/

namespace Cuboid2
namespace GaussianP37Bridge

open GaussianFinite GaussianP37

/-- The standard irreducibility fact needed for the field structure on
`ℚ(i)` in this module.
-/
private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

/-- Actual points on the characteristic-zero Gaussian curve `E₀`. -/
abbrev E0Point := gaussianE0.toAffine.Point

/-! ## Finite signed multiples -/

/-- Negation on the displayed short Weierstrass models. -/
def finiteNeg (p : ℕ) : FinitePoint → FinitePoint
  | none => none
  | some (x, y) => some (x, residueSub p 0 y)

/-- Signed scalar multiplication in the explicit finite model. -/
def finiteZMul (p A B : ℕ) (P : FinitePoint) : ℤ → FinitePoint
  | .ofNat n => finiteMul p A B P n
  | .negSucc n => finiteNeg p (finiteMul p A B P (n + 1))

/-- A period of the repeated-addition state machine propagates to every
subsequent state; no associativity assumption is needed for this lemma.
-/
theorem finiteMul_periodic_of_period
    (p A B period : ℕ) (P : FinitePoint)
    (hperiod : finiteMul p A B P period = none) :
    ∀ n : ℕ,
      finiteMul p A B P (n + period) = finiteMul p A B P n := by
  intro n
  induction n with
  | zero =>
      simpa only [Nat.zero_add, finiteMul] using hperiod
  | succ n ih =>
      rw [show n + 1 + period = n + period + 1 by omega]
      change
        finiteAdd p A B (finiteMul p A B P (n + period)) P =
          finiteAdd p A B (finiteMul p A B P n) P
      rw [ih]

/-- Iterating a period any natural number of times changes no state. -/
theorem finiteMul_add_period_mul
    (p A B period : ℕ) (P : FinitePoint)
    (hperiod : finiteMul p A B P period = none) :
    ∀ r k : ℕ,
      finiteMul p A B P (r + k * period) = finiteMul p A B P r := by
  intro r k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Nat.succ_mul]
      rw [← Nat.add_assoc]
      rw [finiteMul_periodic_of_period p A B period P hperiod]
      exact ih

/-- Reduction of a natural scalar to the chosen period. -/
theorem finiteMul_eq_mod
    (p A B period : ℕ) (P : FinitePoint)
    (hperiod : finiteMul p A B P period = none)
    (n : ℕ) :
    finiteMul p A B P n = finiteMul p A B P (n % period) := by
  have hdecomp : n % period + n / period * period = n :=
    Nat.mod_add_div' n period
  calc
    finiteMul p A B P n =
        finiteMul p A B P (n % period + n / period * period) := by
      rw [hdecomp]
    _ = finiteMul p A B P (n % period) :=
      finiteMul_add_period_mul p A B period P hperiod
        (n % period) (n / period)

/-- Negating any of the first twelve plus-row states reverses its index. -/
theorem plusFiniteNeg_row (r : ℕ) (hr : r < 12) :
    finiteNeg 37
        (finiteMul 37 plusCoefficients.1 plusCoefficients.2
          (some (2, 2)) r) =
      finiteMul 37 plusCoefficients.1 plusCoefficients.2
        (some (2, 2)) ((12 - r) % 12) := by
  interval_cases r <;> native_decide

/-- Negating any of the first twelve minus-row states reverses its index. -/
theorem minusFiniteNeg_row (r : ℕ) (hr : r < 12) :
    finiteNeg 37
        (finiteMul 37 minusCoefficients.1 minusCoefficients.2
          (some (2, 2)) r) =
      finiteMul 37 minusCoefficients.1 minusCoefficients.2
        (some (2, 2)) ((12 - r) % 12) := by
  interval_cases r <;> native_decide

/-- Every signed plus multiple is represented by its Euclidean residue
modulo 12.
-/
theorem plusFiniteZMul_eq_natMod (k : ℤ) :
    finiteZMul 37 plusCoefficients.1 plusCoefficients.2
        (some (2, 2)) k =
      finiteMul 37 plusCoefficients.1 plusCoefficients.2
        (some (2, 2)) (k.natMod 12) := by
  have hperiod :
      finiteMul 37 plusCoefficients.1 plusCoefficients.2
        (some (2, 2)) 12 = none := by
    native_decide
  cases k with
  | ofNat n =>
      change
        finiteMul 37 plusCoefficients.1 plusCoefficients.2 (some (2, 2)) n =
          finiteMul 37 plusCoefficients.1 plusCoefficients.2
            (some (2, 2)) (n % 12)
      exact finiteMul_eq_mod 37 plusCoefficients.1 plusCoefficients.2 12
        (some (2, 2)) hperiod n
  | negSucc n =>
      have hreduce :=
        finiteMul_eq_mod 37 plusCoefficients.1 plusCoefficients.2 12
          (some (2, 2)) hperiod (n + 1)
      rw [finiteZMul, hreduce,
        plusFiniteNeg_row ((n + 1) % 12) (Nat.mod_lt _ (by omega))]
      congr 1
      simp only [Int.natMod, Int.negSucc_eq]
      omega

/-- Every signed minus multiple is represented by its Euclidean residue
modulo 12.  Its actual order six is already visible in the twelve-state row.
-/
theorem minusFiniteZMul_eq_natMod (k : ℤ) :
    finiteZMul 37 minusCoefficients.1 minusCoefficients.2
        (some (2, 2)) k =
      finiteMul 37 minusCoefficients.1 minusCoefficients.2
        (some (2, 2)) (k.natMod 12) := by
  have hperiod :
      finiteMul 37 minusCoefficients.1 minusCoefficients.2
        (some (2, 2)) 12 = none := by
    native_decide
  cases k with
  | ofNat n =>
      change
        finiteMul 37 minusCoefficients.1 minusCoefficients.2 (some (2, 2)) n =
          finiteMul 37 minusCoefficients.1 minusCoefficients.2
            (some (2, 2)) (n % 12)
      exact finiteMul_eq_mod 37 minusCoefficients.1 minusCoefficients.2 12
        (some (2, 2)) hperiod n
  | negSucc n =>
      have hreduce :=
        finiteMul_eq_mod 37 minusCoefficients.1 minusCoefficients.2 12
          (some (2, 2)) hperiod (n + 1)
      rw [finiteZMul, hreduce,
        minusFiniteNeg_row ((n + 1) % 12) (Nat.mod_lt _ (by omega))]
      congr 1
      simp only [Int.natMod, Int.negSucc_eq]
      omega

/-! ## The explicit good-reduction interface -/

/-- A pair of actual good-reduction group maps at the two primes above 37.

Every field is a standard property of projective good reduction.  Keeping the
interface at this granularity makes the unproved construction visible: no row
classification or rational-`x` conclusion is included in the structure.
-/
structure Split37GoodReduction where
  plus : E0Point → FinitePoint
  minus : E0Point → FinitePoint
  plus_zero : plus 0 = none
  minus_zero : minus 0 = none
  plus_add : ∀ Q R : E0Point,
    plus (Q + R) =
      finiteAdd 37 plusCoefficients.1 plusCoefficients.2 (plus Q) (plus R)
  minus_add : ∀ Q R : E0Point,
    minus (Q + R) =
      finiteAdd 37 minusCoefficients.1 minusCoefficients.2 (minus Q) (minus R)
  plus_neg : ∀ Q : E0Point, plus (-Q) = finiteNeg 37 (plus Q)
  minus_neg : ∀ Q : E0Point, minus (-Q) = finiteNeg 37 (minus Q)
  plus_P : plus gaussianE0P = some (2, 2)
  minus_P : minus gaussianE0P = some (2, 2)
  plus_T : plus gaussianE0T = some (0, 0)
  minus_T : minus gaussianE0T = some (0, 0)

/-- The plus reduction of a natural multiple of `P`. -/
theorem Split37GoodReduction.plus_nsmul_P
    (red : Split37GoodReduction) (n : ℕ) :
    red.plus (n • gaussianE0P) =
      finiteMul 37 plusCoefficients.1 plusCoefficients.2 (some (2, 2)) n := by
  induction n with
  | zero =>
      simpa [finiteMul] using red.plus_zero
  | succ n ih =>
      rw [succ_nsmul, red.plus_add, ih, red.plus_P]
      rfl

/-- The minus reduction of a natural multiple of `P`. -/
theorem Split37GoodReduction.minus_nsmul_P
    (red : Split37GoodReduction) (n : ℕ) :
    red.minus (n • gaussianE0P) =
      finiteMul 37 minusCoefficients.1 minusCoefficients.2 (some (2, 2)) n := by
  induction n with
  | zero =>
      simpa [finiteMul] using red.minus_zero
  | succ n ih =>
      rw [succ_nsmul, red.minus_add, ih, red.minus_P]
      rfl

/-- The plus reduction of a signed multiple of `P`. -/
theorem Split37GoodReduction.plus_zsmul_P
    (red : Split37GoodReduction) (k : ℤ) :
    red.plus (k • gaussianE0P) =
      finiteZMul 37 plusCoefficients.1 plusCoefficients.2 (some (2, 2)) k := by
  cases k with
  | ofNat n =>
      simpa [finiteZMul] using red.plus_nsmul_P n
  | negSucc n =>
      simp only [negSucc_zsmul, red.plus_neg, red.plus_nsmul_P, finiteZMul]

/-- The minus reduction of a signed multiple of `P`. -/
theorem Split37GoodReduction.minus_zsmul_P
    (red : Split37GoodReduction) (k : ℤ) :
    red.minus (k • gaussianE0P) =
      finiteZMul 37 minusCoefficients.1 minusCoefficients.2 (some (2, 2)) k := by
  cases k with
  | ofNat n =>
      simpa [finiteZMul] using red.minus_nsmul_P n
  | negSucc n =>
      simp only [negSucc_zsmul, red.minus_neg, red.minus_nsmul_P, finiteZMul]

/-- Whether the global point is translated by the rational two-torsion point. -/
inductive Twist
  | plain
  | torsion
deriving DecidableEq, Repr

/-- The characteristic-zero torsion translate selected by a `Twist`. -/
def Twist.globalPoint : Twist → E0Point
  | .plain => 0
  | .torsion => gaussianE0T

/-- The finite torsion translate selected by a `Twist`. -/
def Twist.finitePoint : Twist → FinitePoint
  | .plain => none
  | .torsion => some (0, 0)

/-- The actual characteristic-zero point in a global cyclic row. -/
def globalRowPoint (k : ℤ) (twist : Twist) : E0Point :=
  k • gaussianE0P + twist.globalPoint

/-- The corresponding explicit plus finite row. -/
def plusRowPoint (r : ℕ) (twist : Twist) : FinitePoint :=
  finiteAdd 37 plusCoefficients.1 plusCoefficients.2
    (finiteMul 37 plusCoefficients.1 plusCoefficients.2 (some (2, 2)) r)
    twist.finitePoint

/-- The corresponding explicit minus finite row. -/
def minusRowPoint (r : ℕ) (twist : Twist) : FinitePoint :=
  finiteAdd 37 minusCoefficients.1 minusCoefficients.2
    (finiteMul 37 minusCoefficients.1 minusCoefficients.2 (some (2, 2)) r)
    twist.finitePoint

/-- Good reduction sends an actual global row point to the plus executable
row at the Euclidean residue of its coefficient.
-/
theorem Split37GoodReduction.plus_globalRowPoint
    (red : Split37GoodReduction) (k : ℤ) (twist : Twist) :
    red.plus (globalRowPoint k twist) =
      plusRowPoint (k.natMod 12) twist := by
  rw [globalRowPoint, red.plus_add, red.plus_zsmul_P,
    plusFiniteZMul_eq_natMod]
  cases twist <;> simp [Twist.globalPoint, Twist.finitePoint,
    plusRowPoint, red.plus_zero, red.plus_T]

/-- Good reduction sends an actual global row point to the minus executable
row at the same Euclidean residue.
-/
theorem Split37GoodReduction.minus_globalRowPoint
    (red : Split37GoodReduction) (k : ℤ) (twist : Twist) :
    red.minus (globalRowPoint k twist) =
      minusRowPoint (k.natMod 12) twist := by
  rw [globalRowPoint, red.minus_add, red.minus_zsmul_P,
    minusFiniteZMul_eq_natMod]
  cases twist <;> simp [Twist.globalPoint, Twist.finitePoint,
    minusRowPoint, red.minus_zero, red.minus_T]

/-! ## Rational `x` and the paired-row conclusion -/

/-- An actual affine `E₀` point whose `x`-coordinate lies in `ℚ`. -/
def HasRationalAffineX : E0Point → Prop
  | .zero => False
  | .some x _ _ => ∃ q : ℚ, x = gaussianOfRat q

/-- The quotient point of every `C₀` point has rational affine `x`. -/
theorem coverZero_toE0_hasRationalAffineX (C : GaussianCoverZeroPoint) :
    HasRationalAffineX C.toE0 := by
  refine ⟨2 * C.u ^ 2, ?_⟩
  simp [gaussianOfRat]

/-- Concrete coordinate compatibility for a rational-`x` point under the two
projective reductions.  The affine constructor covers integral `x`; the
infinity constructor covers negative 37-adic valuation.
-/
inductive CommonReducedX (red : Split37GoodReduction) (Q : E0Point) : Prop
  | infinity (hplus : red.plus Q = none) (hminus : red.minus Q = none)
  | affine (x yPlus yMinus : ℕ)
      (hplus : red.plus Q = some (x, yPlus))
      (hminus : red.minus Q = some (x, yMinus))

/-- A common projective reduced `x`-coordinate gives the Boolean comparison
consumed by the finite certificate.
-/
theorem CommonReducedX.sameX
    {red : Split37GoodReduction} {Q : E0Point}
    (h : CommonReducedX red Q) :
    sameX (red.plus Q) (red.minus Q) = true := by
  cases h with
  | infinity hp hm =>
      rw [hp, hm]
      rfl
  | affine x yp ym hp hm =>
      rw [hp, hm]
      change (x == x) = true
      simp

/-- Projective good reduction, including its coordinate compatibility on the
rational `x`-line.  This is the exact local-reduction object still missing
from Mathlib: `toGoodReduction` records the group homomorphism laws, while
`commonX_of_rational` records only the standard projective-coordinate
consequence of rationality.
-/
structure Split37ProjectiveReduction extends Split37GoodReduction where
  commonX_of_rational :
    ∀ Q : E0Point, HasRationalAffineX Q →
      CommonReducedX toSplit37GoodReduction Q

/-- Exact surviving-index predicate from the paired finite rows. -/
def AllowedRow (r : ℕ) : Twist → Prop
  | .plain => r = 0 ∨ r = 1 ∨ r = 11
  | .torsion => r = 0

/-- Closed classification of all twelve executable row pairs. -/
theorem commonX_row_classification_fin :
    ∀ (r : Fin 12) (twist : Twist),
      sameX (plusRowPoint r.val twist) (minusRowPoint r.val twist) = true →
        AllowedRow r.val twist := by
  intro r twist
  fin_cases r <;> cases twist <;> simp only [AllowedRow] <;> native_decide

/-- Natural-index wrapper around the closed twelve-row classification. -/
theorem commonX_row_classification
    (r : ℕ) (hr : r < 12) (twist : Twist)
    (hx : sameX (plusRowPoint r twist) (minusRowPoint r twist) = true) :
    AllowedRow r twist :=
  commonX_row_classification_fin ⟨r, hr⟩ twist hx

/-- Smallest actual-point bridge to the paired finite rows.

Given an actual global row identity, a genuine pair of good-reduction maps,
and coordinate compatibility for rational `x`, the coefficient is forced
into exactly the four rows found by the finite certificate.
-/
theorem actualPoint_allowedRow_of_commonReduction
    (red : Split37GoodReduction) (Q : E0Point) (k : ℤ) (twist : Twist)
    (hQ : Q = globalRowPoint k twist)
    (hxReduction : CommonReducedX red Q) :
    AllowedRow (k.natMod 12) twist := by
  have hr : k.natMod 12 < 12 :=
    Int.natMod_lt (m := k) (n := 12) (by norm_num)
  apply commonX_row_classification (k.natMod 12) hr twist
  rw [← red.plus_globalRowPoint k twist,
    ← red.minus_globalRowPoint k twist, ← hQ]
  exact hxReduction.sameX

/-- Actual-point form of the paired-row bridge.  Its only local input is the
explicit projective good-reduction structure above.
-/
theorem actualPoint_allowedRow
    (red : Split37ProjectiveReduction) (Q : E0Point)
    (k : ℤ) (twist : Twist)
    (hQ : Q = globalRowPoint k twist)
    (hxRat : HasRationalAffineX Q) :
    AllowedRow (k.natMod 12) twist :=
  actualPoint_allowedRow_of_commonReduction red.toSplit37GoodReduction
    Q k twist hQ (red.commonX_of_rational Q hxRat)

/-- Projective reduction data specialized further to the two quartic-cover
boundary disks.  Each field states the elementary valuation conclusion before
the finite nonsquare certificate is applied; it does not assume the desired
exclusion.
-/
structure Split37CoverReduction extends Split37ProjectiveReduction where
  infinity_forces_leading_square :
    ∀ C : GaussianCoverZeroPoint,
      toSplit37ProjectiveReduction.toSplit37GoodReduction.plus C.toE0 = none →
        ∃ a : Fin 37, a.val ^ 2 % 37 = 2
  torsion_forces_q0_square :
    ∀ C : GaussianCoverZeroPoint,
      toSplit37ProjectiveReduction.toSplit37GoodReduction.plus C.toE0 =
        some (0, 0) →
        ∃ a : Fin 37, a.val ^ 2 % 37 = 24

/-- An actual cover point cannot occupy the projective infinity row. -/
theorem coverZero_not_infinityRow
    (red : Split37CoverReduction) (C : GaussianCoverZeroPoint)
    (k : ℤ) (hC : C.toE0 = globalRowPoint k .plain)
    (hk : k.natMod 12 = 0) :
    False := by
  have hplus :
      red.toSplit37ProjectiveReduction.toSplit37GoodReduction.plus C.toE0 =
        none := by
    rw [hC,
      red.toSplit37ProjectiveReduction.toSplit37GoodReduction.plus_globalRowPoint,
      hk]
    native_decide
  exact infinityDisk_no_square_root
    (red.infinity_forces_leading_square C hplus)

/-- An actual cover point cannot occupy the `T=(0,0)` row. -/
theorem coverZero_not_torsionRow
    (red : Split37CoverReduction) (C : GaussianCoverZeroPoint)
    (k : ℤ) (hC : C.toE0 = globalRowPoint k .torsion)
    (hk : k.natMod 12 = 0) :
    False := by
  have hplus :
      red.toSplit37ProjectiveReduction.toSplit37GoodReduction.plus C.toE0 =
        some (0, 0) := by
    rw [hC,
      red.toSplit37ProjectiveReduction.toSplit37GoodReduction.plus_globalRowPoint,
      hk]
    native_decide
  exact torsionDisk_no_square_root
    (red.torsion_forces_q0_square C hplus)

/-- The actual-point finite bridge plus the two elementary lift interfaces
leave exactly the `P` and `-P` disks.
-/
theorem coverZero_survivingRows
    (red : Split37CoverReduction) (C : GaussianCoverZeroPoint)
    (k : ℤ) (twist : Twist)
    (hC : C.toE0 = globalRowPoint k twist) :
    twist = .plain ∧ (k.natMod 12 = 1 ∨ k.natMod 12 = 11) := by
  have hallowed : AllowedRow (k.natMod 12) twist :=
    actualPoint_allowedRow red.toSplit37ProjectiveReduction C.toE0
      k twist hC (coverZero_toE0_hasRationalAffineX C)
  cases twist with
  | plain =>
      simp only [AllowedRow] at hallowed
      refine ⟨rfl, ?_⟩
      rcases hallowed with hzero | hone | heleven
      · exact (coverZero_not_infinityRow red C k hC hzero).elim
      · exact Or.inl hone
      · exact Or.inr heleven
  | torsion =>
      simp only [AllowedRow] at hallowed
      exact (coverZero_not_torsionRow red C k hC hallowed).elim

/-! ## The formal-congruence handoff -/

/-- First derivative of translation by the disk center. -/
def diskTranslationSlope : Disk → ℤ
  | .plus => 4
  | .minus => -4

/-- The difference between the preferred residue representative and the exact
integer derivative coefficient.  At `P`, `-8 = 29 - 37`; at `-P`, the exact
coefficient is already `8`.
-/
def diskLinearCorrection : Disk → ℤ
  | .plus => -1
  | .minus => 0

/-- The exact coefficient identity combining `t₊/37=17`,
`t₋/37=19`, and the translation derivative.
-/
theorem diskSlopeParameterDifference (disk : Disk) :
    diskTranslationSlope disk * (17 - 19) =
      disk.linearUnit + 37 * diskLinearCorrection disk := by
  cases disk <;> norm_num [diskTranslationSlope,
    Disk.linearUnit, diskLinearCorrection]

/-- Cancel the visible factor 37 from an all-level congruence. -/
theorem cancel37_power
    (n : ℕ) (E : ℤ)
    (h : (37 : ℤ) ^ (n + 2) ∣ 37 * E) :
    (37 : ℤ) ^ (n + 1) ∣ E := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  apply mul_left_cancel₀ (a := (37 : ℤ)) (by norm_num)
  calc
    37 * E = 37 ^ (n + 2) * c := hc
    _ = 37 * (37 ^ (n + 1) * c) := by ring

/-- The formal-kernel half of the remaining local theorem: multiplication of
`R=12P` has the two certified linear coefficients, with a tail carrying the
visible factor `37²*z`, at every finite precision.
-/
structure Split37FormalKernel (z : ℤ) where
  plusParameter : ℕ → ℤ
  minusParameter : ℕ → ℤ
  plusKernelTail : ℕ → ℤ
  minusKernelTail : ℕ → ℤ
  plus_parameter :
    ∀ n : ℕ, (37 : ℤ) ^ (n + 2) ∣
      plusParameter n -
        (37 * 17 * z + 1369 * z * plusKernelTail n)
  minus_parameter :
    ∀ n : ℕ, (37 : ℤ) ^ (n + 2) ∣
      minusParameter n -
        (37 * 19 * z + 1369 * z * minusKernelTail n)

/-- The translation half of the remaining local theorem.  It says that the
actual two `x`-coordinates are obtained from the kernel parameters with
derivative `±4`, a nonlinear tail carrying `37²*z`, and equality at every
precision.
-/
structure Split37TranslationComparison
    (disk : Disk) (z : ℤ) (K : Split37FormalKernel z) where
  plusTranslatedX : ℕ → ℤ
  minusTranslatedX : ℕ → ℤ
  translationTail : ℕ → ℤ
  translation :
    ∀ n : ℕ, (37 : ℤ) ^ (n + 2) ∣
      (plusTranslatedX n - minusTranslatedX n) -
        (diskTranslationSlope disk *
          (K.plusParameter n - K.minusParameter n) +
            1369 * z * translationTail n)
  rational_x :
    ∀ n : ℕ, (37 : ℤ) ^ (n + 2) ∣
      plusTranslatedX n - minusTranslatedX n

/-- Minimal formal-kernel/translation interface for one actual disk
parameter.

For every precision `37^(n+2)`, the structure supplies compatible integer
representatives of the two formal parameters and translated
`x`-coordinates.  The first two fields are the formal multiplication theorem
for `[z](12P)` with linear coefficients 17 and 19.  The third is the
translation theorem at `±P`, whose nonlinear remainder visibly has the
factor `37²*z`.  The last field is exactly what equality of the original
rational `x`-coordinates says after clearing denominators.

No existence theorem for this structure is asserted: constructing it is the
specialized formal-group blocker.
-/
structure Split37FormalComparison (disk : Disk) (z : ℤ) where
  plusParameter : ℕ → ℤ
  minusParameter : ℕ → ℤ
  plusTranslatedX : ℕ → ℤ
  minusTranslatedX : ℕ → ℤ
  plusKernelTail : ℕ → ℤ
  minusKernelTail : ℕ → ℤ
  translationTail : ℕ → ℤ
  plus_parameter :
    ∀ n : ℕ, (37 : ℤ) ^ (n + 2) ∣
      plusParameter n -
        (37 * 17 * z + 1369 * z * plusKernelTail n)
  minus_parameter :
    ∀ n : ℕ, (37 : ℤ) ^ (n + 2) ∣
      minusParameter n -
        (37 * 19 * z + 1369 * z * minusKernelTail n)
  translation :
    ∀ n : ℕ, (37 : ℤ) ^ (n + 2) ∣
      (plusTranslatedX n - minusTranslatedX n) -
        (diskTranslationSlope disk *
          (plusParameter n - minusParameter n) +
            1369 * z * translationTail n)
  rational_x :
    ∀ n : ℕ, (37 : ℤ) ^ (n + 2) ∣
      plusTranslatedX n - minusTranslatedX n

/-- Assemble the separately constructible formal-kernel and translation
interfaces into the comparison consumed below.
-/
def Split37FormalComparison.ofKernelAndTranslation
    {disk : Disk} {z : ℤ}
    (K : Split37FormalKernel z)
    (X : Split37TranslationComparison disk z K) :
    Split37FormalComparison disk z where
  plusParameter := K.plusParameter
  minusParameter := K.minusParameter
  plusTranslatedX := X.plusTranslatedX
  minusTranslatedX := X.minusTranslatedX
  plusKernelTail := K.plusKernelTail
  minusKernelTail := K.minusKernelTail
  translationTail := X.translationTail
  plus_parameter := K.plus_parameter
  minus_parameter := K.minus_parameter
  translation := X.translation
  rational_x := X.rational_x

/-- The explicit tail obtained by combining formal multiplication and
translation.
-/
def Split37FormalComparison.combinedTail
    {disk : Disk} {z : ℤ}
    (F : Split37FormalComparison disk z) (n : ℕ) : ℤ :=
  diskLinearCorrection disk +
    diskTranslationSlope disk *
      (F.plusKernelTail n - F.minusKernelTail n) +
      F.translationTail n

/-- The decomposed formal-kernel interface implies the precise unit-linear
congruence consumed by the all-level uniqueness theorem.
-/
theorem Split37FormalComparison.unitLinearCongruence
    {disk : Disk} {z : ℤ}
    (F : Split37FormalComparison disk z) (n : ℕ) :
    (37 : ℤ) ^ (n + 1) ∣
      disk.linearUnit * z + 37 * z * F.combinedTail n := by
  let modulus : ℤ := 37 ^ (n + 2)
  let plusBase : ℤ :=
    37 * 17 * z + 1369 * z * F.plusKernelTail n
  let minusBase : ℤ :=
    37 * 19 * z + 1369 * z * F.minusKernelTail n
  have hcore :
      modulus ∣
        diskTranslationSlope disk *
            (F.plusParameter n - F.minusParameter n) +
          1369 * z * F.translationTail n := by
    have h := dvd_sub (F.rational_x n) (F.translation n)
    dsimp only [modulus]
    rw [show
      diskTranslationSlope disk *
            (F.plusParameter n - F.minusParameter n) +
          1369 * z * F.translationTail n =
        (F.plusTranslatedX n - F.minusTranslatedX n) -
          ((F.plusTranslatedX n - F.minusTranslatedX n) -
            (diskTranslationSlope disk *
              (F.plusParameter n - F.minusParameter n) +
                1369 * z * F.translationTail n)) by ring]
    exact h
  have hparameterDifference :
      modulus ∣ diskTranslationSlope disk *
        ((F.plusParameter n - F.minusParameter n) -
          (plusBase - minusBase)) := by
    have h := dvd_sub (F.plus_parameter n) (F.minus_parameter n)
    have hslope := dvd_mul_of_dvd_right h (diskTranslationSlope disk)
    dsimp only [modulus, plusBase, minusBase] at hslope ⊢
    rw [show
      diskTranslationSlope disk *
          (F.plusParameter n - F.minusParameter n -
            ((37 * 17 * z + 1369 * z * F.plusKernelTail n) -
              (37 * 19 * z + 1369 * z * F.minusKernelTail n))) =
        diskTranslationSlope disk *
          ((F.plusParameter n -
              (37 * 17 * z + 1369 * z * F.plusKernelTail n)) -
            (F.minusParameter n -
              (37 * 19 * z + 1369 * z * F.minusKernelTail n))) by ring]
    exact hslope
  have hbase :
      modulus ∣
        diskTranslationSlope disk * (plusBase - minusBase) +
          1369 * z * F.translationTail n := by
    have h := dvd_sub hcore hparameterDifference
    rw [show
      diskTranslationSlope disk * (plusBase - minusBase) +
          1369 * z * F.translationTail n =
        (diskTranslationSlope disk *
            (F.plusParameter n - F.minusParameter n) +
              1369 * z * F.translationTail n) -
          diskTranslationSlope disk *
            ((F.plusParameter n - F.minusParameter n) -
              (plusBase - minusBase)) by ring]
    exact h
  have hexact :
      diskTranslationSlope disk * (plusBase - minusBase) +
          1369 * z * F.translationTail n =
        37 * (disk.linearUnit * z +
          37 * z * F.combinedTail n) := by
    dsimp only [plusBase, minusBase,
      Split37FormalComparison.combinedTail]
    cases disk <;>
      norm_num [diskTranslationSlope, diskLinearCorrection,
        Disk.linearUnit] <;> ring
  apply cancel37_power n
  rw [← hexact]
  simpa only [modulus] using hbase

/-- View an integer disk coordinate as a rational 37-integral parameter. -/
def integerParameter (z : ℤ) : RationalParameter where
  numerator := z
  denominator := 1
  denominator_pos := by norm_num
  denominator_coprime := by norm_num

/-- The decomposed formal comparison produces the existing all-level
congruence predicate without adding any analytic or rank premise.
-/
theorem Split37FormalComparison.toAllLevels
    {disk : Disk} {z : ℤ}
    (F : Split37FormalComparison disk z) :
    RationalXCongruentAtAllLevels disk (integerParameter z) := by
  refine ⟨F.combinedTail, ?_⟩
  intro n
  simpa [integerParameter] using F.unitLinearCongruence n

/-- A coefficient in the `P` residue class has the exact form `1+12z`. -/
theorem coefficient_decomposition_at_P
    (k : ℤ) (hk : k.natMod 12 = 1) :
    k = 1 + 12 * (k / 12) := by
  have hmod : k % 12 = 1 := by
    simp only [Int.natMod] at hk
    have hnonneg : 0 ≤ k % 12 :=
      Int.emod_nonneg k (by norm_num)
    omega
  have hdiv := Int.ediv_mul_add_emod k 12
  omega

/-- A coefficient in the `-P` residue class has the exact form `-1+12z`. -/
theorem coefficient_decomposition_at_negP
    (k : ℤ) (hk : k.natMod 12 = 11) :
    k = -1 + 12 * ((k + 1) / 12) := by
  have hmod : k % 12 = 11 := by
    simp only [Int.natMod] at hk
    have hnonneg : 0 ≤ k % 12 :=
      Int.emod_nonneg k (by norm_num)
    omega
  have hdiv := Int.ediv_mul_add_emod (k + 1) 12
  omega

/-- The actual global point in the `P` row is `P+[z](12P)`, with an integer
parameter and no elliptic logarithm.
-/
theorem globalRowPoint_at_P
    (k : ℤ) (hk : k.natMod 12 = 1) :
    globalRowPoint k .plain =
      gaussianE0P + (k / 12) • (12 • gaussianE0P) := by
  rw [globalRowPoint, Twist.globalPoint, add_zero]
  calc
    k • gaussianE0P =
        (1 + 12 * (k / 12)) • gaussianE0P := by
      rw [← coefficient_decomposition_at_P k hk]
    _ = gaussianE0P + (k / 12) • (12 • gaussianE0P) := by
      simp only [add_zsmul, one_zsmul, mul_zsmul]
      rw [smul_comm]
      rfl

/-- The actual global point in the `-P` row is `-P+[z](12P)`, again with an
integer parameter.
-/
theorem globalRowPoint_at_negP
    (k : ℤ) (hk : k.natMod 12 = 11) :
    globalRowPoint k .plain =
      -gaussianE0P + ((k + 1) / 12) • (12 • gaussianE0P) := by
  rw [globalRowPoint, Twist.globalPoint, add_zero]
  calc
    k • gaussianE0P =
        (-1 + 12 * ((k + 1) / 12)) • gaussianE0P := by
      rw [← coefficient_decomposition_at_negP k hk]
    _ = -gaussianE0P + ((k + 1) / 12) • (12 • gaussianE0P) := by
      simp only [add_zsmul, neg_one_zsmul, mul_zsmul]
      rw [smul_comm]
      rfl

/-- Once the formal-group calculation supplies the explicit all-level
congruences, the actual rational parameter in either surviving disk is zero.
This theorem is merely the sound handoff to `GaussianP37`; it does not assert
that the formal-group congruences exist.
-/
theorem actualDiskParameter_unique
    (disk : Disk) (q : RationalParameter)
    (hformal : RationalXCongruentAtAllLevels disk q) :
    q.value = 0 :=
  rationalX_value_unique disk q hformal

/-- In the `P` disk, the all-level congruence forces the global coefficient
itself to be `1`.
-/
theorem coefficient_unique_at_P
    (k : ℤ) (hk : k.natMod 12 = 1)
    (hformal :
      RationalXCongruentAtAllLevels .plus (integerParameter (k / 12))) :
    k = 1 := by
  have hz : k / 12 = 0 :=
    rationalX_parameter_unique .plus (integerParameter (k / 12)) hformal
  rw [coefficient_decomposition_at_P k hk, hz]
  norm_num

/-- In the `-P` disk, the all-level congruence forces the global coefficient
itself to be `-1`.
-/
theorem coefficient_unique_at_negP
    (k : ℤ) (hk : k.natMod 12 = 11)
    (hformal :
      RationalXCongruentAtAllLevels .minus
        (integerParameter ((k + 1) / 12))) :
    k = -1 := by
  have hz : (k + 1) / 12 = 0 :=
    rationalX_parameter_unique .minus
      (integerParameter ((k + 1) / 12)) hformal
  rw [coefficient_decomposition_at_negP k hk, hz]
  norm_num

/-- Structured formal-kernel version of `coefficient_unique_at_P`. -/
theorem coefficient_unique_at_P_of_formalComparison
    (k : ℤ) (hk : k.natMod 12 = 1)
    (F : Split37FormalComparison .plus (k / 12)) :
    k = 1 :=
  coefficient_unique_at_P k hk F.toAllLevels

/-- Structured formal-kernel version of `coefficient_unique_at_negP`. -/
theorem coefficient_unique_at_negP_of_formalComparison
    (k : ℤ) (hk : k.natMod 12 = 11)
    (F : Split37FormalComparison .minus ((k + 1) / 12)) :
    k = -1 :=
  coefficient_unique_at_negP k hk F.toAllLevels

/-- Actual `E₀(ℚ(i))` point endpoint in the `P` disk. -/
theorem actualPoint_eq_P_of_formalComparison
    (Q : E0Point) (k : ℤ)
    (hQ : Q = globalRowPoint k .plain)
    (hk : k.natMod 12 = 1)
    (F : Split37FormalComparison .plus (k / 12)) :
    Q = gaussianE0P := by
  have hkOne : k = 1 :=
    coefficient_unique_at_P_of_formalComparison k hk F
  rw [hQ, hkOne]
  simp [globalRowPoint, Twist.globalPoint]

/-- Actual `E₀(ℚ(i))` point endpoint in the `-P` disk. -/
theorem actualPoint_eq_negP_of_formalComparison
    (Q : E0Point) (k : ℤ)
    (hQ : Q = globalRowPoint k .plain)
    (hk : k.natMod 12 = 11)
    (F : Split37FormalComparison .minus ((k + 1) / 12)) :
    Q = -gaussianE0P := by
  have hkNegOne : k = -1 :=
    coefficient_unique_at_negP_of_formalComparison k hk F
  rw [hQ, hkNegOne]
  simp [globalRowPoint, Twist.globalPoint]

/-- Complete actual-point endpoint after the two explicitly named local
interfaces have been constructed: an affine `C₀` point maps to `P` or `-P`.
-/
theorem coverZero_toE0_eq_P_or_negP
    (red : Split37CoverReduction) (C : GaussianCoverZeroPoint)
    (k : ℤ) (twist : Twist)
    (hC : C.toE0 = globalRowPoint k twist)
    (formalAtP :
      k.natMod 12 = 1 →
        Split37FormalComparison .plus (k / 12))
    (formalAtNegP :
      k.natMod 12 = 11 →
        Split37FormalComparison .minus ((k + 1) / 12)) :
    C.toE0 = gaussianE0P ∨ C.toE0 = -gaussianE0P := by
  obtain ⟨htwist, hk | hk⟩ :=
    coverZero_survivingRows red C k twist hC
  · exact Or.inl <| actualPoint_eq_P_of_formalComparison
      C.toE0 k (htwist ▸ hC) hk (formalAtP hk)
  · exact Or.inr <| actualPoint_eq_negP_of_formalComparison
      C.toE0 k (htwist ▸ hC) hk (formalAtNegP hk)

/-- The quotient coordinate `X=2u²` turns the `±P` conclusion into the exact
two rational values of the quartic-cover parameter.
-/
theorem coverZero_u_eq_one_or_neg_one_of_toE0
    (C : GaussianCoverZeroPoint)
    (h : C.toE0 = gaussianE0P ∨ C.toE0 = -gaussianE0P) :
    C.u = 1 ∨ C.u = -1 := by
  have hx : 2 * gaussianOfRat (C.u ^ 2) = (2 : GaussianRat) := by
    rcases h with hp | hm
    · exact (WeierstrassCurve.Affine.Point.some.inj hp).1
    · simp only [gaussianE0P] at hm
      exact (WeierstrassCurve.Affine.Point.some.inj hm).1
  have hxr := congrArg QuadraticAlgebra.re hx
  simp only [QuadraticAlgebra.re_mul, gaussianOfRat_re,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat,
    gaussianOfRat_im, mul_zero] at hxr
  rcases sq_eq_one_iff.mp (by linarith : C.u ^ 2 = 1) with hu | hu
  · exact Or.inl hu
  · exact Or.inr hu

/-- Value-level actual-cover endpoint. -/
theorem coverZero_u_eq_one_or_neg_one
    (red : Split37CoverReduction) (C : GaussianCoverZeroPoint)
    (k : ℤ) (twist : Twist)
    (hC : C.toE0 = globalRowPoint k twist)
    (formalAtP :
      k.natMod 12 = 1 →
        Split37FormalComparison .plus (k / 12))
    (formalAtNegP :
      k.natMod 12 = 11 →
        Split37FormalComparison .minus ((k + 1) / 12)) :
    C.u = 1 ∨ C.u = -1 :=
  coverZero_u_eq_one_or_neg_one_of_toE0 C
    (coverZero_toE0_eq_P_or_negP red C k twist hC formalAtP formalAtNegP)

end GaussianP37Bridge
end Cuboid2
