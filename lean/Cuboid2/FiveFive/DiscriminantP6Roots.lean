import Cuboid2.FiveFive.DiscriminantIntervals
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

/-!
# Exact real-root isolation for the degree-six `5+5` discriminant factor

The degree-six factor is isolated without trusting a CAS root counter.  Exact
Bernstein-basis identities prove its sign outside two rational brackets and
the sign of its derivative inside the brackets.  Continuity and strict
monotonicity then give exactly one real root in each bracket.
-/

namespace Cuboid2

open Polynomial Set

noncomputable section

/-- The degree-six discriminant factor as a polynomial over `ℝ`. -/
def fiveFiveDiscriminantP6PolyReal : ℝ[X] :=
  X ^ 6 + C 15 * X ^ 5 - C 1585 * X ^ 4 + C 3052 * X ^ 3 -
    C 1585 * X ^ 2 + C 15 * X + 1

@[simp] theorem eval_fiveFiveDiscriminantP6PolyReal (x : ℝ) :
    fiveFiveDiscriminantP6PolyReal.eval x =
      x ^ 6 + 15 * x ^ 5 - 1585 * x ^ 4 + 3052 * x ^ 3 -
        1585 * x ^ 2 + 15 * x + 1 := by
  simp [fiveFiveDiscriminantP6PolyReal]

@[simp] theorem eval_derivative_fiveFiveDiscriminantP6PolyReal (x : ℝ) :
    fiveFiveDiscriminantP6PolyReal.derivative.eval x =
      6 * x ^ 5 + 75 * x ^ 4 - 6340 * x ^ 3 + 9156 * x ^ 2 -
        3170 * x + 15 := by
  simp [fiveFiveDiscriminantP6PolyReal]
  ring

private theorem unit_interval_coordinate
    {a b t : ℝ} (hab : a < b) (hat : a ≤ t) (htb : t ≤ b) :
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ t = a + (b - a) * x := by
  let x : ℝ := (t - a) / (b - a)
  have hba : 0 < b - a := sub_pos.mpr hab
  refine ⟨x, ?_, ?_, ?_⟩
  · exact div_nonneg (sub_nonneg.mpr hat) hba.le
  · exact (div_le_one hba).2 (by linarith)
  · dsimp [x]
    field_simp [ne_of_gt hba]
    ring

private def p6LeftBernstein (x : ℝ) : ℝ :=
  (1 - x) ^ 6 +
      (1293 / 200 : ℝ) * x * (1 - x) ^ 5 +
      (3160363 / 200000 : ℝ) * x ^ 2 * (1 - x) ^ 4 +
      (4662045533 / 250000000 : ℝ) * x ^ 3 * (1 - x) ^ 3 +
      (2156438523043 / 200000000000 : ℝ) * x ^ 4 * (1 - x) ^ 2 +
      (500419852773453 / 200000000000000 : ℝ) * x ^ 5 * (1 - x) +
      (31273781539768681 / 1000000000000000000 : ℝ) * x ^ 6

private theorem p6LeftBernstein_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 < p6LeftBernstein x := by
  unfold p6LeftBernstein
  by_cases hx : x = 1
  · subst x
    norm_num
  · have hxlt : x < 1 := lt_of_le_of_ne hx1 hx
    have h1x : 0 < 1 - x := sub_pos.mpr hxlt
    positivity

private theorem p6Left_identity (x : ℝ) :
    fiveFiveDiscriminantP6PolyReal.eval ((31 / 1000 : ℝ) * x) = p6LeftBernstein x := by
  simp [fiveFiveDiscriminantP6PolyReal, p6LeftBernstein]
  ring

private def p6LowDerivativeBernstein (x : ℝ) : ℝ :=
  (37329944752075047 / 500000000000000 : ℝ) * (1 - x) ^ 5 +
      (9398001119393621 / 25000000000000 : ℝ) * x * (1 - x) ^ 4 +
      (591463060349407 / 781250000000 : ℝ) * x ^ 2 * (1 - x) ^ 3 +
      (74443045357363 / 97656250000 : ℝ) * x ^ 3 * (1 - x) ^ 2 +
      (9369046600567 / 24414062500 : ℝ) * x ^ 4 * (1 - x) +
      (2358152046981 / 30517578125 : ℝ) * x ^ 5

private theorem p6LowDerivativeBernstein_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 < p6LowDerivativeBernstein x := by
  unfold p6LowDerivativeBernstein
  by_cases hx : x = 1
  · subst x
    norm_num
  · have hxlt : x < 1 := lt_of_le_of_ne hx1 hx
    have h1x : 0 < 1 - x := sub_pos.mpr hxlt
    positivity

private theorem p6LowDerivative_identity (x : ℝ) :
    -(fiveFiveDiscriminantP6PolyReal.derivative.eval ((31 / 1000 : ℝ) + (1 / 1000 : ℝ) * x)) = p6LowDerivativeBernstein x := by
  simp [fiveFiveDiscriminantP6PolyReal, p6LowDerivativeBernstein]
  ring

private def p6MidLowBernstein (x : ℝ) : ℝ :=
  (170492372779 / 3814697265625 : ℝ) * (1 - x) ^ 6 +
      (2290874815371 / 30517578125 : ℝ) * x * (1 - x) ^ 5 +
      (77852996819 / 48828125 : ℝ) * x ^ 2 * (1 - x) ^ 4 +
      (5944402302 / 1953125 : ℝ) * x ^ 3 * (1 - x) ^ 3 +
      (26618134 / 15625 : ℝ) * x ^ 4 * (1 - x) ^ 2 +
      (33282 / 125 : ℝ) * x ^ 5 * (1 - x) +
      86 * x ^ 6

private theorem p6MidLowBernstein_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 < p6MidLowBernstein x := by
  unfold p6MidLowBernstein
  by_cases hx : x = 1
  · subst x
    norm_num
  · have hxlt : x < 1 := lt_of_le_of_ne hx1 hx
    have h1x : 0 < 1 - x := sub_pos.mpr hxlt
    positivity

private theorem p6MidLow_identity (x : ℝ) :
    -(fiveFiveDiscriminantP6PolyReal.eval ((4 / 125 : ℝ) + (121 / 125 : ℝ) * x)) = p6MidLowBernstein x := by
  simp [fiveFiveDiscriminantP6PolyReal, p6MidLowBernstein]
  ring

private def p6MidOneBernstein (x : ℝ) : ℝ :=
  86 * (1 - x) ^ 6 +
      2838 * x * (1 - x) ^ 5 +
      156594 * x ^ 2 * (1 - x) ^ 4 +
      2872738 * x ^ 3 * (1 - x) ^ 3 +
      17514435 * x ^ 4 * (1 - x) ^ 2 +
      25783329 * x ^ 5 * (1 - x) +
      10456349 * x ^ 6

private theorem p6MidOneBernstein_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 < p6MidOneBernstein x := by
  unfold p6MidOneBernstein
  by_cases hx : x = 1
  · subst x
    norm_num
  · have hxlt : x < 1 := lt_of_le_of_ne hx1 hx
    have h1x : 0 < 1 - x := sub_pos.mpr hxlt
    positivity

private theorem p6MidOne_identity (x : ℝ) :
    -(fiveFiveDiscriminantP6PolyReal.eval ((1 : ℝ) + (9 : ℝ) * x)) = p6MidOneBernstein x := by
  simp [fiveFiveDiscriminantP6PolyReal, p6MidOneBernstein]
  ring

private def p6MidHighBernstein (x : ℝ) : ℝ :=
  10456349 * (1 - x) ^ 6 +
      152250747 * x * (1 - x) ^ 5 +
      871030021 * x ^ 2 * (1 - x) ^ 4 +
      (304168844342 / 125 : ℝ) * x ^ 3 * (1 - x) ^ 3 +
      (411167761238 / 125 : ℝ) * x ^ 4 * (1 - x) ^ 2 +
      (211870826178 / 125 : ℝ) * x ^ 5 * (1 - x) +
      (37581940034 / 15625 : ℝ) * x ^ 6

private theorem p6MidHighBernstein_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 < p6MidHighBernstein x := by
  unfold p6MidHighBernstein
  by_cases hx : x = 1
  · subst x
    norm_num
  · have hxlt : x < 1 := lt_of_le_of_ne hx1 hx
    have h1x : 0 < 1 - x := sub_pos.mpr hxlt
    positivity

private theorem p6MidHigh_identity (x : ℝ) :
    -(fiveFiveDiscriminantP6PolyReal.eval ((10 : ℝ) + (109 / 5 : ℝ) * x)) = p6MidHighBernstein x := by
  simp [fiveFiveDiscriminantP6PolyReal, p6MidHighBernstein]
  ring

private def p6HighDerivativeBernstein (x : ℝ) : ℝ :=
  (240902400294 / 3125 : ℝ) * (1 - x) ^ 5 +
      (242256824452 / 625 : ℝ) * x * (1 - x) ^ 4 +
      (974467354739 / 1250 : ℝ) * x ^ 2 * (1 - x) ^ 3 +
      (489964925906 / 625 : ℝ) * x ^ 3 * (1 - x) ^ 2 +
      (3941659476509 / 10000 : ℝ) * x ^ 4 * (1 - x) +
      (990922487043 / 12500 : ℝ) * x ^ 5

private theorem p6HighDerivativeBernstein_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 < p6HighDerivativeBernstein x := by
  unfold p6HighDerivativeBernstein
  by_cases hx : x = 1
  · subst x
    norm_num
  · have hxlt : x < 1 := lt_of_le_of_ne hx1 hx
    have h1x : 0 < 1 - x := sub_pos.mpr hxlt
    positivity

private theorem p6HighDerivative_identity (x : ℝ) :
    fiveFiveDiscriminantP6PolyReal.derivative.eval ((159 / 5 : ℝ) + (1 / 10 : ℝ) * x) = p6HighDerivativeBernstein x := by
  simp [fiveFiveDiscriminantP6PolyReal, p6HighDerivativeBernstein]
  ring

private def p6RightPolynomial (x : ℝ) : ℝ :=
  (5412584453431 / 1000000 : ℝ) +
      (990922487043 / 12500 : ℝ) * x +
      (22030471663 / 2000 : ℝ) * x ^ 2 +
      (15067067 / 25 : ℝ) * x ^ 3 +
      (321433 / 20 : ℝ) * x ^ 4 +
      (1032 / 5 : ℝ) * x ^ 5 +
      x ^ 6

private theorem p6RightPolynomial_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < p6RightPolynomial x := by
  unfold p6RightPolynomial
  positivity

private theorem p6Right_identity (x : ℝ) :
    fiveFiveDiscriminantP6PolyReal.eval ((319 / 10 : ℝ) + x) =
      p6RightPolynomial x := by
  simp [fiveFiveDiscriminantP6PolyReal, p6RightPolynomial]
  ring

theorem fiveFiveDiscriminantP6_pos_left
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 31 / 1000) :
    0 < fiveFiveDiscriminantP6PolyReal.eval t := by
  rcases unit_interval_coordinate (a := 0) (b := 31 / 1000)
      (by norm_num) ht0 ht1 with ⟨x, hx0, hx1, ht⟩
  have ht' : t = (31 / 1000 : ℝ) * x := by
    rw [ht]
    ring
  rw [ht', p6Left_identity]
  exact p6LeftBernstein_pos hx0 hx1

theorem fiveFiveDiscriminantP6_derivative_neg_low
    {t : ℝ} (ht0 : 31 / 1000 ≤ t) (ht1 : t ≤ 32 / 1000) :
    fiveFiveDiscriminantP6PolyReal.derivative.eval t < 0 := by
  rcases unit_interval_coordinate (a := 31 / 1000) (b := 32 / 1000)
      (by norm_num) ht0 ht1 with ⟨x, hx0, hx1, ht⟩
  have ht' : t = (31 / 1000 : ℝ) + (1 / 1000 : ℝ) * x := by
    rw [ht]
    ring
  have hpos : 0 < -(fiveFiveDiscriminantP6PolyReal.derivative.eval t) := by
    rw [ht', p6LowDerivative_identity]
    exact p6LowDerivativeBernstein_pos hx0 hx1
  linarith

theorem fiveFiveDiscriminantP6_neg_mid_low
    {t : ℝ} (ht0 : 32 / 1000 ≤ t) (ht1 : t ≤ 1) :
    fiveFiveDiscriminantP6PolyReal.eval t < 0 := by
  rcases unit_interval_coordinate (a := 32 / 1000) (b := 1)
      (by norm_num) ht0 ht1 with ⟨x, hx0, hx1, ht⟩
  have ht' : t = (4 / 125 : ℝ) + (121 / 125 : ℝ) * x := by
    rw [ht]
    ring
  have hpos : 0 < -(fiveFiveDiscriminantP6PolyReal.eval t) := by
    rw [ht', p6MidLow_identity]
    exact p6MidLowBernstein_pos hx0 hx1
  linarith

theorem fiveFiveDiscriminantP6_neg_mid_one
    {t : ℝ} (ht0 : 1 ≤ t) (ht1 : t ≤ 10) :
    fiveFiveDiscriminantP6PolyReal.eval t < 0 := by
  rcases unit_interval_coordinate (a := 1) (b := 10)
      (by norm_num) ht0 ht1 with ⟨x, hx0, hx1, ht⟩
  have ht' : t = (1 : ℝ) + 9 * x := by
    rw [ht]
    ring
  have hpos : 0 < -(fiveFiveDiscriminantP6PolyReal.eval t) := by
    rw [ht', p6MidOne_identity]
    exact p6MidOneBernstein_pos hx0 hx1
  linarith

theorem fiveFiveDiscriminantP6_neg_mid_high
    {t : ℝ} (ht0 : 10 ≤ t) (ht1 : t ≤ 159 / 5) :
    fiveFiveDiscriminantP6PolyReal.eval t < 0 := by
  rcases unit_interval_coordinate (a := 10) (b := 159 / 5)
      (by norm_num) ht0 ht1 with ⟨x, hx0, hx1, ht⟩
  have ht' : t = (10 : ℝ) + (109 / 5 : ℝ) * x := by
    rw [ht]
    ring
  have hpos : 0 < -(fiveFiveDiscriminantP6PolyReal.eval t) := by
    rw [ht', p6MidHigh_identity]
    exact p6MidHighBernstein_pos hx0 hx1
  linarith

theorem fiveFiveDiscriminantP6_derivative_pos_high
    {t : ℝ} (ht0 : 159 / 5 ≤ t) (ht1 : t ≤ 319 / 10) :
    0 < fiveFiveDiscriminantP6PolyReal.derivative.eval t := by
  rcases unit_interval_coordinate (a := 159 / 5) (b := 319 / 10)
      (by norm_num) ht0 ht1 with ⟨x, hx0, hx1, ht⟩
  have ht' : t = (159 / 5 : ℝ) + (1 / 10 : ℝ) * x := by
    rw [ht]
    ring
  rw [ht', p6HighDerivative_identity]
  exact p6HighDerivativeBernstein_pos hx0 hx1

theorem fiveFiveDiscriminantP6_pos_right
    {t : ℝ} (ht : 319 / 10 ≤ t) :
    0 < fiveFiveDiscriminantP6PolyReal.eval t := by
  let x : ℝ := t - 319 / 10
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have ht' : t = 319 / 10 + x := by dsimp [x]; ring
  rw [ht', p6Right_identity]
  exact p6RightPolynomial_pos hx

theorem fiveFiveDiscriminantP6_strictAnti_low :
    StrictAntiOn (fun t : ℝ => fiveFiveDiscriminantP6PolyReal.eval t)
      (Icc (31 / 1000) (32 / 1000)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact fiveFiveDiscriminantP6PolyReal.continuous.continuousOn
  · intro t ht
    have ht' : t ∈ Icc (31 / 1000 : ℝ) (32 / 1000) :=
      interior_subset ht
    change deriv (fun y : ℝ => fiveFiveDiscriminantP6PolyReal.eval y) t < 0
    rw [Polynomial.deriv]
    exact fiveFiveDiscriminantP6_derivative_neg_low ht'.1 ht'.2

theorem fiveFiveDiscriminantP6_strictMono_high :
    StrictMonoOn (fun t : ℝ => fiveFiveDiscriminantP6PolyReal.eval t)
      (Icc (159 / 5) (319 / 10)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact fiveFiveDiscriminantP6PolyReal.continuous.continuousOn
  · intro t ht
    have ht' : t ∈ Icc (159 / 5 : ℝ) (319 / 10) :=
      interior_subset ht
    change 0 < deriv (fun y : ℝ => fiveFiveDiscriminantP6PolyReal.eval y) t
    rw [Polynomial.deriv]
    exact fiveFiveDiscriminantP6_derivative_pos_high ht'.1 ht'.2

theorem fiveFiveDiscriminantP6_existsUnique_low_root :
    ∃! r : ℝ,
      r ∈ Icc (31 / 1000) (32 / 1000) ∧
        fiveFiveDiscriminantP6PolyReal.eval r = 0 := by
  have hleft : 0 < fiveFiveDiscriminantP6PolyReal.eval (31 / 1000 : ℝ) :=
    fiveFiveDiscriminantP6_pos_left (by norm_num) le_rfl
  have hright : fiveFiveDiscriminantP6PolyReal.eval (32 / 1000 : ℝ) < 0 :=
    fiveFiveDiscriminantP6_neg_mid_low le_rfl (by norm_num)
  obtain ⟨r, hr, hr0⟩ :=
    (isPreconnected_Icc.intermediate_value₂
      (show (32 / 1000 : ℝ) ∈ Icc (31 / 1000) (32 / 1000) by constructor <;> norm_num)
      (show (31 / 1000 : ℝ) ∈ Icc (31 / 1000) (32 / 1000) by constructor <;> norm_num)
      fiveFiveDiscriminantP6PolyReal.continuous.continuousOn
      continuousOn_const hright.le hleft.le)
  refine ⟨r, ⟨hr, hr0⟩, ?_⟩
  intro z hz
  apply fiveFiveDiscriminantP6_strictAnti_low.injOn hz.1 hr
  change fiveFiveDiscriminantP6PolyReal.eval z =
    fiveFiveDiscriminantP6PolyReal.eval r
  rw [hz.2, hr0]

theorem fiveFiveDiscriminantP6_existsUnique_high_root :
    ∃! r : ℝ,
      r ∈ Icc (159 / 5) (319 / 10) ∧
        fiveFiveDiscriminantP6PolyReal.eval r = 0 := by
  have hleft : fiveFiveDiscriminantP6PolyReal.eval (159 / 5 : ℝ) < 0 :=
    fiveFiveDiscriminantP6_neg_mid_high (by norm_num) le_rfl
  have hright : 0 < fiveFiveDiscriminantP6PolyReal.eval (319 / 10 : ℝ) :=
    fiveFiveDiscriminantP6_pos_right le_rfl
  obtain ⟨r, hr, hr0⟩ :=
    (isPreconnected_Icc.intermediate_value₂
      (show (159 / 5 : ℝ) ∈ Icc (159 / 5) (319 / 10) by constructor <;> norm_num)
      (show (319 / 10 : ℝ) ∈ Icc (159 / 5) (319 / 10) by constructor <;> norm_num)
      fiveFiveDiscriminantP6PolyReal.continuous.continuousOn
      continuousOn_const hleft.le hright.le)
  refine ⟨r, ⟨hr, hr0⟩, ?_⟩
  intro z hz
  apply fiveFiveDiscriminantP6_strictMono_high.injOn hz.1 hr
  change fiveFiveDiscriminantP6PolyReal.eval z =
    fiveFiveDiscriminantP6PolyReal.eval r
  rw [hz.2, hr0]

/-- Every positive real root lies in one of the two certified brackets. -/
theorem fiveFiveDiscriminantP6_positive_root_mem_brackets
    {r : ℝ} (hr : 0 < r)
    (hroot : fiveFiveDiscriminantP6PolyReal.eval r = 0) :
    r ∈ Icc (31 / 1000) (32 / 1000) ∨
      r ∈ Icc (159 / 5) (319 / 10) := by
  by_cases hlow : r ≤ 31 / 1000
  · exact False.elim ((ne_of_gt
      (fiveFiveDiscriminantP6_pos_left hr.le hlow)) hroot)
  by_cases hlow' : r ≤ 32 / 1000
  · left
    exact ⟨(lt_of_not_ge hlow).le, hlow'⟩
  by_cases hone : r ≤ 1
  · exact False.elim ((ne_of_lt
      (fiveFiveDiscriminantP6_neg_mid_low ((lt_of_not_ge hlow').le) hone)) hroot)
  by_cases hten : r ≤ 10
  · exact False.elim ((ne_of_lt
      (fiveFiveDiscriminantP6_neg_mid_one ((lt_of_not_ge hone).le) hten)) hroot)
  by_cases hmid : r ≤ 159 / 5
  · exact False.elim ((ne_of_lt
      (fiveFiveDiscriminantP6_neg_mid_high ((lt_of_not_ge hten).le) hmid)) hroot)
  by_cases hhigh : r ≤ 319 / 10
  · right
    exact ⟨(lt_of_not_ge hmid).le, hhigh⟩
  · exact False.elim ((ne_of_gt
      (fiveFiveDiscriminantP6_pos_right ((lt_of_not_ge hhigh).le))) hroot)

end

end Cuboid2
