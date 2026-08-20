import Cuboid2.QuadraticReduction.C012
import Cuboid2.QuadraticReduction.TransportExceptions
import Cuboid2.QuadraticReduction.TransportCompletion
import Cuboid2.QuadraticReduction.GaussianSplit

/-!
# Final quadratic--cubic assembly around the Gaussian octic classification

All transport and exceptional-fibre arguments in this file are
unconditional.  The sole global input of the main theorem is the exact
rational-point classification on the octic curve; the Gaussian descent and
split-37 argument will discharge that input in the subsequent module.
-/

namespace Cuboid2

noncomputable section

/-- The inverse point produced from an admissible compact solution stays in
the regular forward chart.  This strengthens the roundtrip theorem with the
nonvanishing denominator needed by the common-character argument. -/
theorem compact_to_E1AffinePoint_regular
    {ε : PhysicalSign} {z k y : ℚ}
    (hz : z ≠ 0) (hk : k ≠ 0)
    (hSm : z ^ 2 - 1 ≠ 0)
    (h1 : compactF1 ε z k y = 0)
    (h0 : compactF0 ε z k y = 0) :
    ∃ P : E1AffinePoint,
      quotientForwardU P.X P.Y = compactReciprocalU ε z k ∧
      quotientForwardV P.X P.Y = compactReciprocalV ε z k ∧
      quotientForwardF3 P.X P.Y ≠ 0 := by
  let U := compactReciprocalU ε z k
  let V := compactReciprocalV ε z k
  have hC8 : reciprocalQuotientC8 U V = 0 := by
    have h := compact_equations_to_reciprocalQuotientC8
      hz hk hSm h1 h0
    cases ε <;>
      simpa [U, V, compactReciprocalU, compactReciprocalV] using h
  obtain ⟨hproduct, hproductOne, -, -⟩ :=
    compact_common_character_facts hz hk hSm h1 h0
  change IsSquare (U * V) at hproduct
  change U * V ≠ 1 at hproductOne
  obtain ⟨hA, ha1, hF3⟩ :=
    reciprocalQuotientC8_admissible_denominators
      hC8 hproduct hproductOne
  let P : E1AffinePoint := {
    X := quotientInverseX U V
    Y := quotientInverseY U V
    onCurve := quotientInverse_on_E1 hC8 hA ha1
  }
  have hU : quotientForwardU P.X P.Y = U := by
    have hfirst :=
      quotientInverse_first_equation (U := U) (V := V) ha1
    change quotientForwardU
      (quotientInverseX U V) (quotientInverseY U V) = U
    unfold quotientForwardU
    field_simp [hF3]
    linarith
  have hV : quotientForwardV P.X P.Y = V := by
    have hsecond := quotientInverse_second_equation hC8 hA ha1
    change quotientForwardV
      (quotientInverseX U V) (quotientInverseY U V) = V
    unfold quotientForwardV
    field_simp [hF3]
    linarith
  exact ⟨P, hU, hV, hF3⟩

/-- A regular inverse point with admissible product cannot have abscissa
`1`: that elliptic fibre consists of `(1,0)`, whose forward product is the
removed value `1`. -/
theorem quotient_inverse_point_X_ne_one
    (P : E1AffinePoint)
    (hF3 : quotientForwardF3 P.X P.Y ≠ 0)
    (hproductOne :
      quotientForwardU P.X P.Y * quotientForwardV P.X P.Y ≠ 1) :
    P.X ≠ 1 := by
  intro hX
  have hY : P.Y = 0 := by
    have hcurve := P.onCurve
    rw [hX] at hcurve
    norm_num [e1Residual] at hcurve
    nlinarith
  apply hproductOne
  rw [hX, hY]
  norm_num [quotientForwardU, quotientForwardV, quotientForwardF1,
    quotientForwardF2, quotientForwardF3] at hF3 ⊢

/-- The complete specialized `2+3` contradiction, conditional only on the
exact octic rational-point theorem.  Every compact and inverse-transport
exception is discharged inside the proof. -/
theorem quadratic_cubic_impossible_sharipov_of_octic_classified
    (hclass : OcticRationalPointsClassified)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hcop : Nat.Coprime p q) (hne : p ≠ q) :
    ¬ QuadraticCubicCase (sharipovParameter p q) := by
  intro hcase
  obtain ⟨ε, z, k, y, hz, hk, hs, h1, h0⟩ :=
    quadraticCubicCase_to_compact_sharipov hp hq hcop hcase
  have hSm : z ^ 2 - 1 ≠ 0 := by
    intro hzero
    apply sharipovParameter_ne_one hp hq hne
    rw [hs]
    linarith
  obtain ⟨P, hU, hV, hF3⟩ :=
    compact_to_E1AffinePoint_regular hz hk hSm h1 h0
  obtain ⟨hproduct, hproductOne, hcharacter, hcharacterZero⟩ :=
    compact_common_character_facts hz hk hSm h1 h0
  have hproductP :
      IsSquare
        (quotientForwardU P.X P.Y * quotientForwardV P.X P.Y) := by
    simpa [hU, hV] using hproduct
  have hproductOneP :
      quotientForwardU P.X P.Y * quotientForwardV P.X P.Y ≠ 1 := by
    simpa [hU, hV] using hproductOne
  have hcharacterP :
      IsSquare
        (1 - quotientForwardU P.X P.Y * quotientForwardV P.X P.Y) := by
    simpa [hU, hV] using hcharacter
  have hcharacterZeroP :
      1 - quotientForwardU P.X P.Y * quotientForwardV P.X P.Y ≠ 0 := by
    simpa [hU, hV] using hcharacterZero
  have hPX1 := quotient_inverse_point_X_ne_one P hF3 hproductOneP
  exact regular_quotient_common_character_impossible
    (dplus_classified_of_octic_classified hclass)
    P hPX1 hF3 hproductP hproductOneP hcharacterP hcharacterZeroP

end

end Cuboid2
