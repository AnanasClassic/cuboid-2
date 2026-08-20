import Cuboid2.QuadraticReduction.GaussianFinite

/-!
# The split-prime and all-level congruence certificates at 37

The first part of this module checks the complete two-embedding row over
`𝔽₃₇`, including the point counts, exponents, multiples of `P`, paired
`x`-coordinates, and the two excluded quartic residue disks.

The second part checks the exact `mod 37²` formal-parameter trace and isolates
the all-level arithmetic argument.  It does not assume an elliptic logarithm
or a Mordell--Weil rank statement: the final uniqueness theorem takes only the
explicit congruences obtained after a rational parameter has been substituted
in either of the two surviving disks.
-/

namespace Cuboid2
namespace GaussianP37

open GaussianFinite

/-! ## The complete row over `𝔽₃₇` -/

/-- Coefficients of the `i ↦ 6` reduction of `E₀`. -/
def plusCoefficients : ℕ × ℕ := e0Coefficients 37 6

/-- Coefficients of the `i ↦ 31` reduction of `E₀`. -/
def minusCoefficients : ℕ × ℕ := e0Coefficients 37 31

/-- Both displayed residues are square roots of `-1` modulo `37`. -/
theorem splitRoots :
    6 ^ 2 % 37 = 36 ∧ 31 ^ 2 % 37 = 36 := by
  native_decide

/-- The plus curve has coefficients `(12,11)`, 48 points, exponent 12, and
`P=(2,2)` has order 12.
-/
theorem plusGroupRow :
    plusCoefficients = (12, 11) ∧
      (finitePoints 37 plusCoefficients.1 plusCoefficients.2).length = 48 ∧
      finiteExponent 37 plusCoefficients.1 plusCoefficients.2 = 12 ∧
      finiteOrder 37 plusCoefficients.1 plusCoefficients.2 (some (2, 2)) = 12 := by
  native_decide

/-- The minus curve has coefficients `(25,22)`, 42 points and exponent 42.
The point `(5,3)` is an explicit cyclic generator, while `P` has order 6.
-/
theorem minusGroupRow :
    minusCoefficients = (25, 22) ∧
      (finitePoints 37 minusCoefficients.1 minusCoefficients.2).length = 42 ∧
      finiteExponent 37 minusCoefficients.1 minusCoefficients.2 = 42 ∧
      finiteOrder 37 minusCoefficients.1 minusCoefficients.2 (some (5, 3)) = 42 ∧
      finiteOrder 37 minusCoefficients.1 minusCoefficients.2 (some (2, 2)) = 6 := by
  native_decide

/-- The twelve multiples of `P` on the plus curve. -/
def plusPlainRow : List FinitePoint :=
  (List.range 12).map fun n =>
    finiteMul 37 plusCoefficients.1 plusCoefficients.2 (some (2, 2)) n

/-- The twelve multiples of `P`, translated by `T=(0,0)`, on the plus curve. -/
def plusTwistedRow : List FinitePoint :=
  plusPlainRow.map fun Q =>
    finiteAdd 37 plusCoefficients.1 plusCoefficients.2 Q (some (0, 0))

/-- The twelve multiples of `P` on the minus curve. -/
def minusPlainRow : List FinitePoint :=
  (List.range 12).map fun n =>
    finiteMul 37 minusCoefficients.1 minusCoefficients.2 (some (2, 2)) n

/-- The twelve multiples of `P`, translated by `T=(0,0)`, on the minus curve. -/
def minusTwistedRow : List FinitePoint :=
  minusPlainRow.map fun Q =>
    finiteAdd 37 minusCoefficients.1 minusCoefficients.2 Q (some (0, 0))

/-- Exact plus-embedding point rows. -/
theorem plusPointRows :
    plusPlainRow =
      [none, some (2, 2), some (10, 4), some (20, 12),
        some (33, 26), some (6, 14), some (26, 0), some (6, 23),
        some (33, 11), some (20, 25), some (10, 33), some (2, 35)] ∧
    plusTwistedRow =
      [some (0, 0), some (24, 13), some (27, 4), some (32, 3),
        some (25, 33), some (8, 6), some (36, 0), some (8, 31),
        some (25, 4), some (32, 34), some (27, 33), some (24, 24)] := by
  native_decide

/-- Exact minus-embedding point rows. -/
theorem minusPointRows :
    minusPlainRow =
      [none, some (2, 2), some (11, 11), some (0, 0),
        some (11, 26), some (2, 35), none, some (2, 2),
        some (11, 11), some (0, 0), some (11, 26), some (2, 35)] ∧
    minusTwistedRow =
      [some (0, 0), some (11, 26), some (2, 35), none,
        some (2, 2), some (11, 11), some (0, 0), some (11, 26),
        some (2, 35), none, some (2, 2), some (11, 11)] := by
  native_decide

/-- Indices at which the two untwisted rows have the same projective
`x`-coordinate.
-/
def equalXPlainIndices : List ℕ :=
  (List.range 12).filter fun n =>
    sameX (plusPlainRow.getD n none) (minusPlainRow.getD n none)

/-- Indices at which the two `T`-translated rows have the same projective
`x`-coordinate.
-/
def equalXTwistedIndices : List ℕ :=
  (List.range 12).filter fun n =>
    sameX (plusTwistedRow.getD n none) (minusTwistedRow.getD n none)

/-- The complete paired-`x` comparison leaves exactly the displayed rows. -/
theorem pairedXRows :
    equalXPlainIndices = [0, 1, 11] ∧
      equalXTwistedIndices = [0] := by
  native_decide

/-! ## The two quartic lift exclusions -/

/-- Exhaustive rational-square test modulo `p`. -/
def isSquareMod (p a : ℕ) : Bool :=
  (List.range p).any fun x => x ^ 2 % p == a % p

/-- The infinity disk would force the leading quartic coefficient `2` to be a
square modulo 37, but it is not.
-/
theorem infinityDisk_quartic_nonsquare :
    isSquareMod 37 2 = false := by
  native_decide

/-- Proposition-level form of the infinity-disk exclusion. -/
theorem infinityDisk_no_square_root :
    ¬ ∃ x : Fin 37, (x.val ^ 2) % 37 = 2 := by
  native_decide

/-- At `i ↦ 6`, the value `q(0)=-1-2i` is `24`, a nonsquare modulo 37. -/
theorem torsionDisk_quartic_nonsquare :
    residueSub 37 0 (1 + 2 * 6) = 24 ∧
      isSquareMod 37 24 = false := by
  native_decide

/-- Proposition-level form of the zero/torsion-disk exclusion. -/
theorem torsionDisk_no_square_root :
    ¬ ∃ x : Fin 37, (x.val ^ 2) % 37 = 24 := by
  native_decide

/-! ## The exact trace modulo `37²` -/

/-- The two Hensel lifts of the roots of `X²+1` modulo `37²`. -/
theorem splitRootLifts :
    117 ^ 2 % 1369 = 1368 ∧ 1252 ^ 2 % 1369 = 1368 ∧
      117 % 37 = 6 ∧ 1252 % 37 = 31 := by
  native_decide

/-- Projective data produced by doubling an affine point when `2y` need not
be invertible.  The represented doubled point has
`x=X/Z²`, `y=Y/Z³`.
-/
structure DoublingTrace where
  N : ℕ
  D : ℕ
  X : ℕ
  Y : ℕ
  Z : ℕ
deriving DecidableEq, Repr

/-- Weighted projective coordinates with affine chart
`x=X/Z²`, `y=Y/Z³`.
-/
structure WeightedPoint where
  X : ℕ
  Y : ℕ
  Z : ℕ
deriving DecidableEq, Repr

/-- The denominator-free doubling formulas used in the certificate. -/
def projectiveDoubleTrace (modulus A B x y : ℕ) : DoublingTrace :=
  let N := (3 * x ^ 2 + 2 * A * x + B) % modulus
  let D := 2 * y % modulus
  let X := residueSub modulus (N ^ 2) ((A + 2 * x) * D ^ 2)
  let Y := residueSub modulus
    (N * residueSub modulus (x * D ^ 2) X) (y * D ^ 3)
  ⟨N, D, X, Y, D⟩

/-- The formal parameter `t=-x/y=-XZ/Y` of a projective point. -/
def projectiveParameter (modulus : ℕ) (P : DoublingTrace) : ℕ :=
  residueSub modulus 0 (P.X * P.Z) * residueInv modulus P.Y % modulus

/-- Forget the tangent intermediates and retain the represented point. -/
def DoublingTrace.toWeightedPoint (P : DoublingTrace) : WeightedPoint :=
  ⟨P.X, P.Y, P.Z⟩

/-- Denominator-free doubling in weighted projective coordinates. -/
def projectiveDouble
    (modulus A B : ℕ) (P : WeightedPoint) : WeightedPoint :=
  let M :=
    (3 * P.X ^ 2 + 2 * A * P.X * P.Z ^ 2 + B * P.Z ^ 4) % modulus
  let X :=
    residueSub modulus (M ^ 2)
      ((A * P.Z ^ 2 + 2 * P.X) * (2 * P.Y) ^ 2)
  let Y :=
    residueSub modulus
      (M * residueSub modulus (4 * P.Y ^ 2 * P.X) X)
      (8 * P.Y ^ 4)
  let Z := 2 * P.Y * P.Z % modulus
  ⟨X, Y, Z⟩

/-- The formal parameter `-XZ/Y` in weighted projective coordinates. -/
def weightedProjectiveParameter (modulus : ℕ) (P : WeightedPoint) : ℕ :=
  residueSub modulus 0 (P.X * P.Z) * residueInv modulus P.Y % modulus

/-- Projective curve equation for `y²=x³+Ax²+Bx` in weights `(2,3,1)`. -/
def weightedOnCurve
    (modulus A B : ℕ) (P : WeightedPoint) : Bool :=
  P.Y ^ 2 % modulus ==
    (P.X ^ 3 + A * P.X ^ 2 * P.Z ^ 2 + B * P.X * P.Z ^ 4) % modulus

/-- Initial affine multiples at the plus lift `i=117`. -/
def plusLiftMultiples : List FinitePoint :=
  ((List.range 6).map Nat.succ).map fun n =>
    finiteMul 1369 234 899 (some (2, 2)) n

/-- Initial affine multiples at the minus lift `i=1252`. -/
def minusLiftMultiples : List FinitePoint :=
  ((List.range 3).map Nat.succ).map fun n =>
    finiteMul 1369 1135 466 (some (2, 2)) n

/-- The exact plus trace gives `t(12P)=629=37*17 (mod 37²)`. -/
theorem plusFormalParameterTrace :
    e0Coefficients 1369 117 = (234, 899) ∧
      plusLiftMultiples =
        [some (2, 2), some (10, 411), some (464, 678),
          some (329, 1173), some (931, 347), some (655, 370)] ∧
      projectiveDoubleTrace 1369 234 899 655 370 =
        ⟨998, 740, 741, 1111, 740⟩ ∧
      weightedOnCurve 1369 234 899
        (projectiveDoubleTrace 1369 234 899 655 370).toWeightedPoint = true ∧
      1111 * residueInv 1369 1111 % 1369 = 1 ∧
      projectiveParameter 1369
        (projectiveDoubleTrace 1369 234 899 655 370) = 629 ∧
      629 = 37 * 17 := by
  native_decide

/-- The exact minus trace first gives `t(6P)=1036`; a second
denominator-free projective doubling gives
`t(12P)=703=37*19 (mod 37²)`.
-/
theorem minusFormalParameterTrace :
    e0Coefficients 1369 1252 = (1135, 466) ∧
      minusLiftMultiples =
        [some (2, 2), some (677, 1306), some (0, 444)] ∧
      projectiveDoubleTrace 1369 1135 466 0 444 =
        ⟨466, 888, 854, 415, 888⟩ ∧
      projectiveParameter 1369
        (projectiveDoubleTrace 1369 1135 466 0 444) = 1036 ∧
      weightedOnCurve 1369 1135 466
        (projectiveDoubleTrace 1369 1135 466 0 444).toWeightedPoint = true ∧
      415 * residueInv 1369 415 % 1369 = 1 ∧
      projectiveDouble 1369 1135 466
        (projectiveDoubleTrace 1369 1135 466 0 444).toWeightedPoint =
          ⟨266, 1173, 518⟩ ∧
      weightedOnCurve 1369 1135 466
        (projectiveDouble 1369 1135 466
          (projectiveDoubleTrace 1369 1135 466 0 444).toWeightedPoint) = true ∧
      1173 * residueInv 1369 1173 % 1369 = 1 ∧
      weightedProjectiveParameter 1369
        (projectiveDouble 1369 1135 466
          (projectiveDoubleTrace 1369 1135 466 0 444).toWeightedPoint) = 703 ∧
      2 * 1036 % 1369 = 703 ∧
      703 = 37 * 19 := by
  native_decide

/-- If a formal parameter is divisible by 37, every quadratic correction to
doubling vanishes modulo `37²`.
-/
theorem formalDoubling_quadratic_tail
    (t h : ℤ) (ht : (37 : ℤ) ∣ t) :
    (1369 : ℤ) ∣ (2 * t + t ^ 2 * h) - 2 * t := by
  obtain ⟨c, rfl⟩ := ht
  refine ⟨c ^ 2 * h, ?_⟩
  ring

/-! ## Translation at `P` and `-P`

Put `r=1/x(S)` and `t=-x(S)/y(S)`.  Clearing the unit denominator
`(1-2r)²` from the addition law gives `translationNumerator` below.
The two factorization identities are exact.  Since the curve equation gives
`r=t²(1+Ar+Br²)`, their factor `r²` proves that everything after the
linear terms `±4t` is of order at least `t²`.
-/

/-- Numerator left after subtracting `2 + 4*sign*t` from the translated
`x`-coordinate and clearing `r(1-2r)²`.
-/
def translationNumerator (sign A B r t : ℤ) : ℤ :=
  (1 + A * r + B * r ^ 2) * (1 + sign * 2 * r * t) ^ 2 -
    r * (1 - 2 * r) ^ 2 * (A + 4 + sign * 4 * t) -
    (1 - 2 * r) ^ 2

/-- Exact factorization at `P=(2,2)`: the remaining translation numerator is
quadratic in `r`.
-/
theorem translationAtP_factor (A B r t : ℤ) :
    translationNumerator 1 A B r t =
      r ^ 2 * ((B + 4 * A + 12) - 4 * (A + 4) * r +
        4 * t * ((A + 4) + (B - 4) * r) +
        4 * t ^ 2 * (1 + A * r + B * r ^ 2)) := by
  simp only [translationNumerator]
  ring

/-- Exact factorization at `-P=(2,-2)`: the linear term changes from `4t`
to `-4t`, while the tail remains quadratic in `r`.
-/
theorem translationAtNegP_factor (A B r t : ℤ) :
    translationNumerator (-1) A B r t =
      r ^ 2 * ((B + 4 * A + 12) - 4 * (A + 4) * r -
        4 * t * ((A + 4) + (B - 4) * r) +
        4 * t ^ 2 * (1 + A * r + B * r ^ 2)) := by
  simp only [translationNumerator]
  ring

/-- Once the formal curve relation makes `r` a multiple of `t²`, the
cross-multiplied nonlinear translation remainder is a multiple of `r*t²`.
-/
theorem translation_tail_order_two
    (sign A B r t C H : ℤ)
    (hr : r = t ^ 2 * C)
    (hfactor : translationNumerator sign A B r t = r ^ 2 * H) :
    r * t ^ 2 ∣ translationNumerator sign A B r t := by
  rw [hfactor, hr]
  refine ⟨C * H, ?_⟩
  ring

/-! ## Unit coefficients and all-level uniqueness -/

/-- The plus-disk coefficient is `4*(17-19)=29 (mod 37)`. -/
theorem plusLinearCoefficient :
    (4 * (17 - 19) : ℤ) % 37 = 29 := by
  norm_num

/-- The minus-disk coefficient is `-4*(17-19)=8 (mod 37)`. -/
theorem minusLinearCoefficient :
    (-4 * (17 - 19) : ℤ) % 37 = 8 := by
  norm_num

/-- Every tail with a visible factor `37*z` gains one level of 37-adic
divisibility.  This includes both higher corrections to the linear coefficient
and all nonlinear terms.
-/
theorem tail_raises_valuation
    (n : ℕ) (z tail : ℤ) (hz : (37 : ℤ) ^ n ∣ z) :
    (37 : ℤ) ^ (n + 1) ∣ 37 * z * tail := by
  obtain ⟨c, rfl⟩ := hz
  refine ⟨c * tail, ?_⟩
  ring

/-- In particular, a quadratic formal tail has the required extra
divisibility at every level.
-/
theorem nonlinear_tail_raises_valuation
    (n : ℕ) (z tail : ℤ) (hz : (37 : ℤ) ^ n ∣ z) :
    (37 : ℤ) ^ (n + 1) ∣ 37 * z ^ 2 * tail := by
  simpa [pow_two, mul_assoc] using
    tail_raises_valuation n z (z * tail) hz

/-- A rational 37-integral parameter, represented without choosing any
p-adic completion.  Coprimality of the denominator is precisely what is
needed to clear it at every finite level.
-/
structure RationalParameter where
  numerator : ℤ
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_coprime : denominator.Coprime 37

/-- The rational value represented by a `RationalParameter`. -/
def RationalParameter.value (q : RationalParameter) : ℚ :=
  q.numerator / q.denominator

/-- The two surviving residue disks. -/
inductive Disk
  | plus
  | minus
deriving DecidableEq, Repr

/-- The exact unit coefficient in the two disks. -/
def Disk.linearUnit : Disk → ℤ
  | .plus => 29
  | .minus => 8

/-- Congruences supplied by equality of the two split `x`-coordinates at every
level, after clearing the rational parameter's denominator.

The tail is allowed to depend on the level; only its proved factor `37*z`
is used.  Thus this predicate neither hides convergence nor assumes a p-adic
logarithm.
-/
def RationalXCongruentAtAllLevels (disk : Disk) (q : RationalParameter) : Prop :=
  ∃ tail : ℕ → ℤ, ∀ n : ℕ,
    (37 : ℤ) ^ (n + 1) ∣
      (disk.linearUnit * q.denominator) * q.numerator +
        37 * q.numerator * tail n

/-- The explicit all-level induction: the unit-linear congruence at level
`n+1`, together with the visible `37*z` tail, forces one additional factor of
37 in `z`.
-/
theorem allLevel_unitLinear_divisible
    (linear z : ℤ)
    (hlinear : IsCoprime (37 : ℤ) linear)
    (tail : ℕ → ℤ)
    (hlevels : ∀ n : ℕ,
      (37 : ℤ) ^ (n + 1) ∣ linear * z + 37 * z * tail n) :
    ∀ n : ℕ, (37 : ℤ) ^ n ∣ z := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have htail :
          (37 : ℤ) ^ (n + 1) ∣ 37 * z * tail n :=
        tail_raises_valuation n z (tail n) ih
      have hlinearMul :
          (37 : ℤ) ^ (n + 1) ∣ linear * z := by
        have := dvd_sub (hlevels n) htail
        simpa only [add_sub_cancel_right] using this
      exact (hlinear.pow_left).dvd_of_dvd_mul_left hlinearMul

/-- A unit linear coefficient plus a `37*z` tail has no nonzero integral
numerator satisfying all congruence levels.
-/
theorem allLevel_unitLinear_unique
    (linear z : ℤ)
    (hlinear : IsCoprime (37 : ℤ) linear)
    (tail : ℕ → ℤ)
    (hlevels : ∀ n : ℕ,
      (37 : ℤ) ^ (n + 1) ∣ linear * z + 37 * z * tail n) :
    z = 0 := by
  have hpow : ∀ n : ℕ, (37 : ℤ) ^ n ∣ z :=
    allLevel_unitLinear_divisible linear z hlinear tail hlevels
  let bound := z.natAbs + 1
  have hzInt : (37 : ℤ) ^ bound ∣ z := hpow bound
  have hzNat : 37 ^ bound ∣ z.natAbs := by
    have h := (Int.natAbs_dvd_natAbs).mpr hzInt
    simpa using h
  have hlt : z.natAbs < 37 ^ bound := by
    have hself : bound < 37 ^ bound := Nat.lt_pow_self (by omega)
    omega
  exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt hzNat hlt)

/-- The displayed coefficient remains prime to 37 after clearing a permitted
rational denominator.
-/
theorem diskLinear_coprime
    (disk : Disk) (q : RationalParameter) :
    IsCoprime (37 : ℤ) (disk.linearUnit * q.denominator) := by
  have hunit : IsCoprime (37 : ℤ) disk.linearUnit := by
    cases disk <;> norm_num [Disk.linearUnit]
  have hden : IsCoprime (37 : ℤ) (q.denominator : ℤ) :=
    q.denominator_coprime.symm.isCoprime
  exact hunit.mul_right hden

/-- Specialized all-level split-37 uniqueness: rational equality of the two
split `x`-coordinates in either surviving disk forces the formal rational
parameter to be zero.
-/
theorem rationalX_parameter_unique
    (disk : Disk) (q : RationalParameter)
    (hx : RationalXCongruentAtAllLevels disk q) :
    q.numerator = 0 := by
  obtain ⟨tail, hlevels⟩ := hx
  exact allLevel_unitLinear_unique
    (disk.linearUnit * q.denominator) q.numerator
    (diskLinear_coprime disk q) tail hlevels

/-- Value-level form of `rationalX_parameter_unique`. -/
theorem rationalX_value_unique
    (disk : Disk) (q : RationalParameter)
    (hx : RationalXCongruentAtAllLevels disk q) :
    q.value = 0 := by
  rw [RationalParameter.value, rationalX_parameter_unique disk q hx]
  norm_num

end GaussianP37
end Cuboid2
