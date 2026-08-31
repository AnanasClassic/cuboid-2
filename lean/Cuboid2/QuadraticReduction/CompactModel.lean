import Cuboid2.QuadraticReduction.SignedSquare

/-!
# Signed-square compact model

The two physical signs are kept as a finite type, distinct from every later
valuation squareclass.  The 27- and 19-term equations below are the exact
expanded substitutions checked by
`research/compact_signed_square/compact_signed_square.py`.
-/

namespace Cuboid2

noncomputable section

/-- The physical sign of the quadratic constant. -/
inductive PhysicalSign
  | positive
  | negative
  deriving DecidableEq, Repr

namespace PhysicalSign

/-- The rational value `+1` or `-1`. -/
def value : PhysicalSign → ℚ
  | positive => 1
  | negative => -1

@[simp] theorem value_positive : value positive = 1 := rfl
@[simp] theorem value_negative : value negative = -1 := rfl

@[simp] theorem value_sq (ε : PhysicalSign) : ε.value ^ 2 = 1 := by
  cases ε <;> norm_num [value]

@[simp] theorem value_ne_zero (ε : PhysicalSign) : ε.value ≠ 0 := by
  cases ε <;> norm_num [value]

end PhysicalSign

/-- The exact scaled quartic equation `F1(z,k,y)`. -/
def compactF1 (ε : PhysicalSign) (z k y : ℚ) : ℚ :=
  let e := ε.value
  e ^ 2 * k ^ 4 * z ^ 4 -
    3 * e * k ^ 4 * y ^ 2 * z ^ 4 -
    4 * e * k ^ 3 * y * z ^ 6 -
    2 * e * k ^ 3 * y * z ^ 4 +
    12 * e * k ^ 3 * y * z ^ 2 -
    e * k ^ 2 * z ^ 8 +
    14 * e * k ^ 2 * z ^ 6 -
    4 * e * k ^ 2 * z ^ 4 -
    10 * e * k ^ 2 * z ^ 2 -
    e * k ^ 2 +
    k ^ 4 * y ^ 4 * z ^ 4 +
    2 * k ^ 3 * y ^ 3 * z ^ 6 +
    k ^ 3 * y ^ 3 * z ^ 4 -
    6 * k ^ 3 * y ^ 3 * z ^ 2 +
    k ^ 2 * y ^ 2 * z ^ 8 -
    14 * k ^ 2 * y ^ 2 * z ^ 6 +
    4 * k ^ 2 * y ^ 2 * z ^ 4 +
    10 * k ^ 2 * y ^ 2 * z ^ 2 +
    k ^ 2 * y ^ 2 +
    k * y * z ^ 8 +
    10 * k * y * z ^ 6 +
    4 * k * y * z ^ 4 -
    14 * k * y * z ^ 2 +
    k * y - 6 * z ^ 6 + z ^ 4 + 2 * z ^ 2

/-- The exact scaled cubic equation `F0(z,k,y)`. -/
def compactF0 (ε : PhysicalSign) (z k y : ℚ) : ℚ :=
  let e := ε.value;
  -2 * e ^ 2 * k ^ 5 * y * z ^ 4 -
    2 * e ^ 2 * k ^ 4 * z ^ 6 -
    e ^ 2 * k ^ 4 * z ^ 4 +
    6 * e ^ 2 * k ^ 4 * z ^ 2 +
    e * k ^ 5 * y ^ 3 * z ^ 4 +
    2 * e * k ^ 4 * y ^ 2 * z ^ 6 +
    e * k ^ 4 * y ^ 2 * z ^ 4 -
    6 * e * k ^ 4 * y ^ 2 * z ^ 2 +
    e * k ^ 3 * y * z ^ 8 -
    14 * e * k ^ 3 * y * z ^ 6 +
    4 * e * k ^ 3 * y * z ^ 4 +
    10 * e * k ^ 3 * y * z ^ 2 +
    e * k ^ 3 * y +
    e * k ^ 2 * z ^ 8 +
    10 * e * k ^ 2 * z ^ 6 +
    4 * e * k ^ 2 * z ^ 4 -
    14 * e * k ^ 2 * z ^ 2 +
    e * k ^ 2 - z ^ 4

/-- The signed-square substitution into the linear remainder. -/
theorem compactF1_scaling (ε : PhysicalSign) (z k y : ℚ) :
    quadraticR1 (z ^ 2) (z ^ 2 * k * y) (ε.value * z ^ 4 * k ^ 2) =
      z ^ 4 * compactF1 ε z k y := by
  cases ε <;>
    simp [PhysicalSign.value, compactF1, quadraticR1, quinticC4, quinticC3,
      quinticC2, quinticC1] <;>
    ring

/-- The signed-square substitution into the constant remainder. -/
theorem compactF0_scaling (ε : PhysicalSign) (z k y : ℚ) :
    quadraticR0 (z ^ 2) (z ^ 2 * k * y) (ε.value * z ^ 4 * k ^ 2) =
      z ^ 6 * compactF0 ε z k y := by
  cases ε <;>
    simp [PhysicalSign.value, compactF0, quadraticR0, quinticC4, quinticC3,
      quinticC2, quinticC0] <;>
    ring

/-- Away from the excluded boundary `z=0`, the compact equations lose no solution. -/
theorem compact_equations_of_remainders
    {ε : PhysicalSign} {z k y : ℚ} (hz : z ≠ 0)
    (h : SatisfiesQuadraticRemainders
      (z ^ 2) (z ^ 2 * k * y) (ε.value * z ^ 4 * k ^ 2)) :
    compactF1 ε z k y = 0 ∧ compactF0 ε z k y = 0 := by
  constructor
  · have hm : z ^ 4 * compactF1 ε z k y = 0 := by
      rw [← compactF1_scaling, h.1]
    exact (mul_eq_zero.mp hm).resolve_left (pow_ne_zero 4 hz)
  · have hm : z ^ 6 * compactF0 ε z k y = 0 := by
      rw [← compactF0_scaling, h.2]
    exact (mul_eq_zero.mp hm).resolve_left (pow_ne_zero 6 hz)

/-- The coefficient called `ell` in the linear subresultant certificate. -/
def compactLiftDenominator (ε : PhysicalSign) (z k : ℚ) : ℚ :=
  k ^ 10 * z ^ 2 + 6 * k ^ 6 * z ^ 4 - k ^ 6 * z ^ 2 - 2 * k ^ 6 +
    ε.value * (2 * k ^ 4 * z ^ 4 + k ^ 4 * z ^ 2 - 6 * k ^ 4 - z ^ 2)

/-- The middle block in the exact recovered numerator. -/
def compactLiftMiddle (z k : ℚ) : ℚ :=
  k ^ 6 * (z ^ 8 + 10 * z ^ 6 + 4 * z ^ 4 - 14 * z ^ 2 + 1) -
    k ^ 2 * (z ^ 8 - 14 * z ^ 6 + 4 * z ^ 4 + 10 * z ^ 2 + 1)

/-- The boundary block in the exact recovered numerator. -/
def compactLiftBoundary (z k : ℚ) : ℚ :=
  2 * k ^ 8 * z ^ 6 + k ^ 8 * z ^ 4 - 6 * k ^ 8 * z ^ 2 +
    6 * z ^ 6 - z ^ 4 - 2 * z ^ 2

/-- Coefficient of `y` in the certified linear subresultant. -/
def compactLiftL1 (ε : PhysicalSign) (z k : ℚ) : ℚ :=
  -z ^ 2 * compactLiftDenominator ε z k

/-- Constant coefficient in the certified linear subresultant. -/
def compactLiftL0 (ε : PhysicalSign) (z k : ℚ) : ℚ :=
  k * (ε.value * compactLiftMiddle z k - compactLiftBoundary z k)

/-- The multiplication-back candidate for the recovered lift coordinate. -/
def compactRecoveredY (ε : PhysicalSign) (z k : ℚ) : ℚ :=
  -compactLiftL0 ε z k / compactLiftL1 ε z k

/-- `z=0` is exactly the discarded parameter fibre `s=0`. -/
theorem square_parameter_eq_zero_iff (z : ℚ) : z ^ 2 = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hz : z * z = 0 := by simpa [pow_two] using h
    rcases mul_eq_zero.mp hz with hz | hz
    · exact hz
    · exact hz
  · intro hz
    simp [hz]

end

end Cuboid2
