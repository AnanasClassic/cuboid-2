import Cuboid2.QuadraticReduction.Reciprocal
import Cuboid2.DPlus.Basic

/-!
# Common-character descent on the elliptic quotient

This file checks the small-function identities from
`product_character_simplification.py` and the exact eliminations from
`product_squareclass_valuation.py`.  The factor `2` in the common character is
part of the theorem.
-/

namespace Cuboid2

noncomputable section

/-- Residual of `E1 : Y^2 = X^3 - 5X + 4`. -/
def e1Residual (X Y : ℚ) : ℚ := Y ^ 2 - X ^ 3 + 5 * X - 4

/-- An affine rational point on the explicit elliptic quotient. -/
structure E1AffinePoint where
  X : ℚ
  Y : ℚ
  onCurve : e1Residual X Y = 0

/-- `L=2X+Y-2`. -/
def e1L (X Y : ℚ) : ℚ := 2 * X + Y - 2

/-- `M=X^2+2Y-1`. -/
def e1M (X Y : ℚ) : ℚ := X ^ 2 + 2 * Y - 1

/-- `F=(X+1)LM`. -/
def e1F (X Y : ℚ) : ℚ := (X + 1) * e1L X Y * e1M X Y

/-- Numerator of the transported quotient coordinate `U`. -/
def e1UNumerator (X Y : ℚ) : ℚ :=
  593 * X ^ 5 + 2454 * X ^ 4 + 310 * X ^ 3 * Y - 4845 * X ^ 3 -
    706 * X ^ 2 * Y - 8891 * X ^ 2 + 4710 * X * Y + 17492 * X -
    4218 * Y - 6803

/-- Numerator of the transported quotient coordinate `V`. -/
def e1VNumerator (X Y : ℚ) : ℚ :=
  593 * X ^ 5 + 1861 * X ^ 4 + 310 * X ^ 3 * Y - 3714 * X ^ 3 +
    170 * X ^ 2 * Y - 9954 * X ^ 2 + 4758 * X * Y + 16361 * X -
    5046 * Y - 5147

/-- Common denominator of the transported quotient coordinates. -/
def e1D0 (X Y : ℚ) : ℚ :=
  593 * X ^ 5 - 201 * X ^ 4 + 903 * X ^ 3 * Y - 880 * X ^ 3 +
    1977 * X ^ 2 * Y + 4384 * X ^ 2 - 5779 * X * Y - 12953 * X +
    3091 * Y + 9057

/-- Numerator polynomial `P` in the certified square multiplier. -/
def e1GPolynomialP (X : ℚ) : ℚ :=
  2062 * X ^ 3 - 1055 * X ^ 2 - 8634 * X + 7723

/-- Polynomial `Q` in the certified square multiplier. -/
def e1GPolynomialQ (X : ℚ) : ℚ :=
  593 * X ^ 2 + 1807 * X - 3758

/-- Transported quotient coordinate `U`. -/
def e1U (X Y : ℚ) : ℚ := e1UNumerator X Y / e1D0 X Y

/-- Transported quotient coordinate `V`. -/
def e1V (X Y : ℚ) : ℚ := e1VNumerator X Y / e1D0 X Y

/-- The exact rational square multiplier in the common-character identity. -/
def e1G (X Y : ℚ) : ℚ :=
  (e1GPolynomialP X - e1GPolynomialQ X * Y) / ((X - 3) * e1D0 X Y)

/-- The compact multiplier certifying the cleared common-character identity. -/
def e1CommonCharacterQuotient (X Y : ℚ) : ℚ :=
  (X + 1) *
    (2797181 * X ^ 7 - 703298 * X ^ 6 * Y - 2078205 * X ^ 6 +
      2682732 * X ^ 5 * Y - 13991627 * X ^ 5 -
      1406596 * X ^ 4 * Y ^ 2 + 13558504 * X ^ 4 * Y + 61460779 * X ^ 4 -
      8572408 * X ^ 3 * Y ^ 2 - 60074988 * X ^ 3 * Y - 165385561 * X ^ 3 +
      4766956 * X ^ 2 * Y ^ 2 + 12031106 * X ^ 2 * Y + 162793705 * X ^ 2 +
      54325648 * X * Y ^ 2 + 122421632 * X * Y + 540967 * X -
      56490256 * Y ^ 2 - 90958632 * Y - 46137239)

/-- The small identity `XM=(Y+2)L` in the function field of `E1`. -/
theorem e1_X_mul_M (P : E1AffinePoint) :
    P.X * e1M P.X P.Y = (P.Y + 2) * e1L P.X P.Y := by
  apply sub_eq_zero.mp
  calc
    P.X * e1M P.X P.Y - (P.Y + 2) * e1L P.X P.Y =
        -e1Residual P.X P.Y := by
          simp [e1M, e1L, e1Residual]
          ring
    _ = 0 := by rw [P.onCurve]; norm_num

/-- Cleared form of `M=L*(Y+2)/X`. -/
theorem e1_M_eq_L_mul_k (P : E1AffinePoint) (hX : P.X ≠ 0) :
    e1M P.X P.Y = e1L P.X P.Y * ((P.Y + 2) / P.X) := by
  apply (eq_div_iff hX).2
  rw [mul_comm]
  exact e1_X_mul_M P

/-- Exact polynomial certificate behind `1-UV=2F g^2`. -/
theorem e1_common_character_cleared (P : E1AffinePoint) :
    (e1D0 P.X P.Y ^ 2 - e1UNumerator P.X P.Y * e1VNumerator P.X P.Y) *
        (P.X - 3) ^ 2 =
      2 * e1F P.X P.Y *
        (e1GPolynomialP P.X - e1GPolynomialQ P.X * P.Y) ^ 2 := by
  apply sub_eq_zero.mp
  calc
    (e1D0 P.X P.Y ^ 2 - e1UNumerator P.X P.Y * e1VNumerator P.X P.Y) *
          (P.X - 3) ^ 2 -
        2 * e1F P.X P.Y *
          (e1GPolynomialP P.X - e1GPolynomialQ P.X * P.Y) ^ 2 =
      e1Residual P.X P.Y * e1CommonCharacterQuotient P.X P.Y := by
        simp [e1D0, e1UNumerator, e1VNumerator, e1F, e1L, e1M,
          e1GPolynomialP, e1GPolynomialQ, e1Residual, e1CommonCharacterQuotient]
        ring
    _ = 0 := by rw [P.onCurve]; simp

/-- Rational-function form, with every denominator made explicit. -/
theorem e1_common_character
    (P : E1AffinePoint) (hD0 : e1D0 P.X P.Y ≠ 0) (hX3 : P.X ≠ 3) :
    1 - e1U P.X P.Y * e1V P.X P.Y =
      2 * e1F P.X P.Y * e1G P.X P.Y ^ 2 := by
  have hclear := e1_common_character_cleared P
  field_simp [e1U, e1V, e1G, hD0, sub_ne_zero.mpr hX3] at ⊢ hclear
  ring_nf at ⊢ hclear
  exact hclear

/-- The line through `(0,-2)` used to introduce `k`. -/
theorem e1_line_substitution (X k : ℚ) :
    e1Residual X (k * X - 2) = -X * (X ^ 2 - k ^ 2 * X + 4 * k - 5) := by
  simp [e1Residual]
  ring

/-- The quadratic relation between `h=X+1` and the line slope `k`. -/
def e1HKRelation (k h : ℚ) : ℚ :=
  h ^ 2 - (k ^ 2 + 2) * h + (k ^ 2 + 4 * k - 4)

/-- Every nonvertical affine point satisfies the displayed `h,k` relation. -/
theorem e1_hk_relation (P : E1AffinePoint) (hX : P.X ≠ 0) :
    e1HKRelation ((P.Y + 2) / P.X) (P.X + 1) = 0 := by
  field_simp [e1HKRelation, hX]
  have h := P.onCurve
  simp [e1Residual] at h
  nlinarith

/-- Discriminant of the `h`-quadratic. -/
theorem e1_hk_discriminant (k : ℚ) :
    (k ^ 2 + 2) ^ 2 - 4 * (k ^ 2 + 4 * k - 4) = k ^ 4 - 16 * k + 20 := by
  ring

/-- Exact negative-squareclass substitution. -/
theorem e1_negative_squareclass_relation (U v : ℚ) :
    e1HKRelation (-2 * U) (-v ^ 2) =
      4 * U ^ 2 * v ^ 2 + 4 * U ^ 2 - 8 * U + v ^ 4 + 2 * v ^ 2 - 4 := by
  simp [e1HKRelation]
  ring

/-- Discriminant in `U` of the negative-squareclass relation. -/
theorem e1_negative_U_discriminant (v : ℚ) :
    (-8) ^ 2 -
        4 * (4 * (v ^ 2 + 1)) * (v ^ 4 + 2 * v ^ 2 - 4) =
      -16 * (v ^ 2 + 2) * (v ^ 4 + v ^ 2 - 4) := by
  ring

/-- Exact positive-squareclass substitution. -/
theorem e1_positive_squareclass_relation (U v : ℚ) :
    e1HKRelation (2 * U) (v ^ 2) =
      -4 * U ^ 2 * v ^ 2 + 4 * U ^ 2 + 8 * U + v ^ 4 - 2 * v ^ 2 - 4 := by
  simp [e1HKRelation]
  ring

/-- The positive discriminant after writing `k=2u^2`. -/
theorem e1_positive_discriminant (u : ℚ) :
    ((2 * u ^ 2) ^ 4 - 16 * (2 * u ^ 2) + 20) / 4 =
      4 * u ^ 8 - 8 * u ^ 2 + 5 := by
  ring

/-- The positive octic maps to `D+` with square abscissa. -/
theorem e1_positive_octic_to_dplus (u r : ℚ)
    (hr : r ^ 2 = 4 * u ^ 8 - 8 * u ^ 2 + 5) :
    ∃ P : DPlusAffinePoint, P.HasSquareAbscissa := by
  let Q : OcticPoint := {
    u := u
    r := r
    onCurve := by simpa [octicRhs] using hr
  }
  exact ⟨Q.toDPlus, Q.toDPlus_hasSquareAbscissa⟩

end

end Cuboid2
