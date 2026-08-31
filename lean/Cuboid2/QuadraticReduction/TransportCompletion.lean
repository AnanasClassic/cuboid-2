import Cuboid2.QuadraticReduction.CompactBoundary
import Cuboid2.QuadraticReduction.Completion

/-!
# Regular transport into the common-character contradiction

This module joins the affine `E1 → C8` chart to the already checked
common-character valuation descent.  It is deliberately independent of the
subresultant inverse: any `E1` point with the required two square characters
is excluded.  The inverse and its exceptional fibres are supplied by
`QuotientInverse` and `TransportExceptions`.
-/

namespace Cuboid2

noncomputable section

/-- Translation by the rational two-torsion point, bundled on affine points. -/
def E1AffinePoint.transportTranslate
    (Q : E1AffinePoint) (hX : Q.X ≠ 1) : E1AffinePoint where
  X := e1TransportTranslateX Q.X
  Y := e1TransportTranslateY Q.X Q.Y
  onCurve := by
    rw [e1TransportTranslate_residual hX, Q.onCurve]
    norm_num

@[simp] theorem E1AffinePoint.transportTranslate_X
    (Q : E1AffinePoint) (hX : Q.X ≠ 1) :
    (Q.transportTranslate hX).X = e1TransportTranslateX Q.X := rfl

@[simp] theorem E1AffinePoint.transportTranslate_Y
    (Q : E1AffinePoint) (hX : Q.X ≠ 1) :
    (Q.transportTranslate hX).Y = e1TransportTranslateY Q.X Q.Y := rfl

/-- The affine two-torsion translation never has abscissa `1`. -/
theorem E1AffinePoint.transportTranslate_X_ne_one
    (Q : E1AffinePoint) (hX : Q.X ≠ 1) :
    (Q.transportTranslate hX).X ≠ 1 := by
  intro h
  simp only [E1AffinePoint.transportTranslate_X,
    e1TransportTranslateX] at h
  field_simp [sub_ne_zero.mpr hX] at h
  linarith

/-- Translation by the two-torsion point is involutive on the affine chart. -/
theorem E1AffinePoint.transportTranslate_involutive_X
    (Q : E1AffinePoint) (hX : Q.X ≠ 1) :
    e1TransportTranslateX (Q.transportTranslate hX).X = Q.X := by
  simp only [E1AffinePoint.transportTranslate_X,
    e1TransportTranslateX]
  field_simp [sub_ne_zero.mpr hX]
  ring

/-- The ordinate also returns after applying the translation twice. -/
theorem E1AffinePoint.transportTranslate_involutive_Y
    (Q : E1AffinePoint) (hX : Q.X ≠ 1) :
    e1TransportTranslateY
        (Q.transportTranslate hX).X (Q.transportTranslate hX).Y = Q.Y := by
  simp only [E1AffinePoint.transportTranslate_X,
    E1AffinePoint.transportTranslate_Y, e1TransportTranslateX,
    e1TransportTranslateY]
  field_simp [sub_ne_zero.mpr hX]
  ring

private theorem quotient_product_not_square_at_three_neg_four :
    ¬ IsSquare
      (quotientForwardU 3 (-4) * quotientForwardV 3 (-4)) := by
  norm_num [quotientForwardU, quotientForwardV, quotientForwardF1,
    quotientForwardF2, quotientForwardF3, Rat.isSquare_iff]

private theorem quotient_product_not_square_at_zero_neg_two :
    ¬ IsSquare
      (quotientForwardU 0 (-2) * quotientForwardV 0 (-2)) := by
  norm_num [quotientForwardU, quotientForwardV, quotientForwardF1,
    quotientForwardF2, quotientForwardF3, Rat.isSquare_iff]

/--
The regular affine quotient chart is incompatible with the two nonzero
square characters supplied by a compact solution.

All low-degree exceptional elliptic points needed by the valuation descent
are discharged here directly.  Values with product `1` are boundary points;
the other two values have a nonsquare product.
-/
theorem regular_quotient_common_character_impossible
    (hclass : DPlusSquareAbscissaClassified)
    (Q : E1AffinePoint)
    (hQX1 : Q.X ≠ 1)
    (hF3 : quotientForwardF3 Q.X Q.Y ≠ 0)
    (hproduct :
      IsSquare
        (quotientForwardU Q.X Q.Y * quotientForwardV Q.X Q.Y))
    (hproductOne :
      quotientForwardU Q.X Q.Y * quotientForwardV Q.X Q.Y ≠ 1)
    (hcharacter :
      IsSquare
        (1 - quotientForwardU Q.X Q.Y * quotientForwardV Q.X Q.Y))
    (hcharacterZero :
      1 - quotientForwardU Q.X Q.Y * quotientForwardV Q.X Q.Y ≠ 0) :
    False := by
  let P := Q.transportTranslate hQX1
  have hPX1 : P.X ≠ 1 :=
    Q.transportTranslate_X_ne_one hQX1
  have hbackX : e1TransportTranslateX P.X = Q.X :=
    Q.transportTranslate_involutive_X hQX1
  have hbackY : e1TransportTranslateY P.X P.Y = Q.Y :=
    Q.transportTranslate_involutive_Y hQX1
  have hD0 : e1D0 P.X P.Y ≠ 0 := by
    intro hzero
    have htranslate :=
      quotientForwardF3_translate (X := P.X) (Y := P.Y) hPX1
    rw [hbackX, hbackY, hzero] at htranslate
    have :
        (P.X - 1) ^ 5 * quotientForwardF3 Q.X Q.Y = 0 := by
      linarith
    exact hF3
      ((mul_eq_zero.mp this).resolve_left
        (pow_ne_zero 5 (sub_ne_zero.mpr hPX1)))
  have hforwardU :
      quotientForwardU Q.X Q.Y = e1U P.X P.Y := by
    rw [← hbackX, ← hbackY]
    exact quotientForwardU_translate hPX1 hD0
  have hforwardV :
      quotientForwardV Q.X Q.Y = e1V P.X P.Y := by
    rw [← hbackX, ← hbackY]
    exact quotientForwardV_translate hPX1 hD0
  have hPX : P.X ≠ 0 := by
    intro hPX0
    have hQX3 : Q.X = 3 := by
      dsimp [P] at hPX0
      simp only [e1TransportTranslateX] at hPX0
      field_simp [sub_ne_zero.mpr hQX1] at hPX0
      linarith
    have hQY : Q.Y = 4 ∨ Q.Y = -4 := by
      have hcurve := Q.onCurve
      rw [hQX3] at hcurve
      unfold e1Residual at hcurve
      have hfactor : (Q.Y - 4) * (Q.Y + 4) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hfactor with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rcases hQY with hQY | hQY
    · apply hproductOne
      rw [hQX3, hQY]
      norm_num [quotientForwardU, quotientForwardV, quotientForwardF1,
        quotientForwardF2, quotientForwardF3]
    · apply quotient_product_not_square_at_three_neg_four
      simpa [hQX3, hQY] using hproduct
  have hPX3 : P.X ≠ 3 := by
    intro hPX3
    have hQX0 : Q.X = 0 := by
      dsimp [P] at hPX3
      simp only [e1TransportTranslateX] at hPX3
      field_simp [sub_ne_zero.mpr hQX1] at hPX3
      linarith
    have hQY : Q.Y = 2 ∨ Q.Y = -2 := by
      have hcurve := Q.onCurve
      rw [hQX0] at hcurve
      unfold e1Residual at hcurve
      have hfactor : (Q.Y - 2) * (Q.Y + 2) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hfactor with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rcases hQY with hQY | hQY
    · apply hproductOne
      rw [hQX0, hQY]
      norm_num [quotientForwardU, quotientForwardV, quotientForwardF1,
        quotientForwardF2, quotientForwardF3]
    · apply quotient_product_not_square_at_zero_neg_two
      simpa [hQX0, hQY] using hproduct
  have hcharacterP :
      IsSquare (1 - e1U P.X P.Y * e1V P.X P.Y) := by
    simpa [hforwardU, hforwardV] using hcharacter
  have hcharacterZeroP :
      1 - e1U P.X P.Y * e1V P.X P.Y ≠ 0 := by
    simpa [hforwardU, hforwardV] using hcharacterZero
  have hL : e1L P.X P.Y ≠ 0 := by
    intro hzero
    apply hcharacterZeroP
    rw [e1_common_character P hD0 hPX3]
    simp [e1F, hzero]
  have hg : e1G P.X P.Y ≠ 0 := by
    intro hzero
    apply hcharacterZeroP
    rw [e1_common_character P hD0 hPX3, hzero]
    ring
  exact regular_e1_common_character_impossible hclass P hPX hD0 hPX3
    hL hg hcharacterP hcharacterZeroP

end

end Cuboid2
