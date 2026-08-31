import Cuboid2.DPlus.Mumford
import Cuboid2.Genus2.FiniteMumford

/-!
# The exact rational Mumford output used by the direct `p = 3` certificate

The external generator computes `11D`, where
`D = [(1,1)-∞]`.  External Cantor arithmetic is not taken as a premise here:
this file stores the resulting rational pair and checks its reduced Mumford
curve equation by an explicit polynomial identity.

The separate global group-law bridge still has to identify this checked pair
with `11D`; the theorem below verifies every coefficient of the pinned output.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- Linear coefficient of the pinned `u` polynomial for `11D`. -/
def dplusElevenDU1 : ℚ :=
  1512953551049931090011965235491827543186300655 /
    1125269740599723731463996110864350380899451136

/-- Constant coefficient of the pinned `u` polynomial for `11D`. -/
def dplusElevenDU0 : ℚ :=
  4962362169051877276884579419235108537444446281 /
    1125269740599723731463996110864350380899451136

/-- Linear coefficient of the pinned `R` polynomial for `11D`. -/
def dplusElevenDV1 : ℚ :=
  1007505149562890744940358950045020958155759206235199053063950244685377 /
    169862485481534422148926696857238158902856641371442101767166209865728

/-- Constant coefficient of the pinned `R` polynomial for `11D`. -/
def dplusElevenDV0 : ℚ :=
  834152317751873069949501294852486932979913973640787027090529717536519 /
    169862485481534422148926696857238158902856641371442101767166209865728

/-- The coefficient-level reduced Mumford representation produced for `11D`. -/
def dplusElevenDRaw : FiniteMumford ℚ :=
  .degreeTwo dplusElevenDU1 dplusElevenDU0
    dplusElevenDV1 dplusElevenDV0

/-- Cubic quotient in the exact identity `f-v²=u*q`. -/
def dplusElevenDQuotient : ℚ[X] :=
  C
      (102564791117858932344097110011969918818469522649018411899367699224574242838801132190186930176 /
        25641197779464733086024277502992479704617380662254602974841924806143560709700283047546732544 :
        ℚ) *
      X ^ 3 +
    C
        (-137900948844280333541286962652141504355731264063628071638072801139803967984658992785960820480 /
          25641197779464733086024277502992479704617380662254602974841924806143560709700283047546732544 :
          ℚ) *
        X ^ 2 +
      C
          (-266892370990799644377177482306736490982699423070373428545550497612044556309833314082922691471 /
            25641197779464733086024277502992479704617380662254602974841924806143560709700283047546732544 :
            ℚ) *
          X +
        C
          (-140217514463230971306398357529072677284222115601998441761114547457618395961694493410117120681 /
            25641197779464733086024277502992479704617380662254602974841924806143560709700283047546732544 :
            ℚ)

set_option maxHeartbeats 2000000 in
/--
Kernel-checked original-model identity for the pinned `11D` output.
-/
theorem dplusElevenD_curve_identity :
    dplusPolynomial - dplusElevenDRaw.v ^ 2 =
      dplusElevenDRaw.u * dplusElevenDQuotient := by
  ext n
  by_cases hn : n ≤ 5
  · interval_cases n <;>
      simp [dplusPolynomial, dplusElevenDRaw, FiniteMumford.u,
        FiniteMumford.v, dplusElevenDQuotient, dplusElevenDU1,
        dplusElevenDU0, dplusElevenDV1, dplusElevenDV0, pow_two,
        Polynomial.coeff_mul, Finset.HasAntidiagonal.antidiagonal,
        Polynomial.coeff_X] <;>
      norm_num <;> ring
  · have hn' : 5 < n := by omega
    have hf : dplusPolynomial.natDegree ≤ 5 := by
      simp only [dplusPolynomial]
      have h5 := natDegree_C_mul_X_pow_le (4 : ℚ) 5
      have h2 := natDegree_C_mul_X_pow_le (8 : ℚ) 2
      have h1 : (C (5 : ℚ) * X : ℚ[X]).natDegree ≤ 5 := by
        have h := natDegree_C_mul_X_pow_le (5 : ℚ) 1
        simpa only [pow_one] using h.trans (by omega)
      apply natDegree_add_le_of_degree_le
      · exact (natDegree_sub_le_of_le h5 h2).trans (by omega)
      · exact h1
    have hv : dplusElevenDRaw.v.natDegree ≤ 1 := by
      simp only [dplusElevenDRaw, FiniteMumford.v]
      have hlinear :
          (C dplusElevenDV1 * X : ℚ[X]).natDegree ≤ 1 := by
        simpa only [pow_one] using
          natDegree_C_mul_X_pow_le dplusElevenDV1 1
      exact natDegree_add_le_of_degree_le hlinear
        (by rw [natDegree_C]; omega)
    have hu : dplusElevenDRaw.u.natDegree ≤ 2 := by
      simp only [dplusElevenDRaw, FiniteMumford.u]
      have hlinear :
          (C dplusElevenDU1 * X : ℚ[X]).natDegree ≤ 2 := by
        simpa only [pow_one] using
          (natDegree_C_mul_X_pow_le dplusElevenDU1 1).trans (by omega)
      exact natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le (by simp) hlinear)
        (by rw [natDegree_C]; omega)
    have hq : dplusElevenDQuotient.natDegree ≤ 3 := by
      simp only [dplusElevenDQuotient]
      have hlinear :
          (C
              (-266892370990799644377177482306736490982699423070373428545550497612044556309833314082922691471 /
                25641197779464733086024277502992479704617380662254602974841924806143560709700283047546732544 :
                ℚ) *
              X).natDegree ≤ 3 := by
        simpa only [pow_one] using
          (natDegree_C_mul_X_pow_le
            (-266892370990799644377177482306736490982699423070373428545550497612044556309833314082922691471 /
              25641197779464733086024277502992479704617380662254602974841924806143560709700283047546732544 :
              ℚ) 1).trans (by omega)
      exact natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le
          (natDegree_add_le_of_degree_le
            (natDegree_C_mul_X_pow_le _ 3)
            ((natDegree_C_mul_X_pow_le _ 2).trans (by omega)))
          hlinear)
        (by rw [natDegree_C]; omega)
    have hleft :
        (dplusPolynomial - dplusElevenDRaw.v ^ 2).natDegree ≤ 5 := by
      exact (natDegree_sub_le _ _).trans
        (max_le hf (natDegree_pow_le.trans (by omega)))
    have hright :
        (dplusElevenDRaw.u * dplusElevenDQuotient).natDegree ≤ 5 :=
      natDegree_mul_le.trans (by omega)
    rw [coeff_eq_zero_of_natDegree_lt (hleft.trans_lt hn'),
      coeff_eq_zero_of_natDegree_lt (hright.trans_lt hn')]

/-- The pinned pair satisfies the exact reduced Mumford condition on `D+`. -/
theorem dplusElevenDRaw_valid :
    dplusElevenDRaw.ValidOn dplusPolynomial := by
  refine ⟨dplusElevenDQuotient, ?_⟩
  exact dplusElevenD_curve_identity

/-- The same certificate in the generic rational Mumford representation. -/
def dplusElevenD : MumfordPair ℚ :=
  dplusElevenDRaw.toMumfordPair

/-- The stored output is a valid reduced rational divisor on `D+`. -/
theorem dplusElevenD_valid :
    dplusElevenD.ValidOn dplusPolynomial :=
  FiniteMumford.toMumfordPair_validOn dplusElevenDRaw_valid

/-- Shifted linear coefficient of `u(1+t)`. -/
def dplusElevenDShiftB : ℚ :=
  3763493032249378552939957457220528304985202927 /
    1125269740599723731463996110864350380899451136

/-- Shifted constant coefficient of `u(1+t)`. -/
def dplusElevenDShiftC : ℚ :=
  950073182587691512295067595698910807691274759 /
    140658717574965466432999513858043797612431392

/-- Exact coordinate shift of the checked `u` polynomial. -/
theorem dplusElevenD_u_shift :
    dplusElevenDRaw.u.comp (X + 1) =
      X ^ 2 + C dplusElevenDShiftB * X + C dplusElevenDShiftC := by
  simp [dplusElevenDRaw, FiniteMumford.u, dplusElevenDU1,
    dplusElevenDU0, dplusElevenDShiftB, dplusElevenDShiftC]
  ring_nf
  ext n
  simp [Polynomial.coeff_X, Polynomial.coeff_C,
    Polynomial.coeff_X_pow, Polynomial.coeff_one,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul_C]
  split_ifs <;> norm_num at *

/-- Value of the pinned `R` polynomial at the centre `a=1`. -/
def dplusElevenDVAtOne : ℚ :=
  76735727804781825620410843537396162130653049161499420006436665092579 /
    7077603561730600922871945702384923287619026723810087573631925411072

/-- Exact coordinate shift of the checked `R` polynomial. -/
theorem dplusElevenD_v_shift :
    dplusElevenDRaw.v.comp (X + 1) =
      C dplusElevenDV1 * X + C dplusElevenDVAtOne := by
  simp [dplusElevenDRaw, FiniteMumford.v, dplusElevenDV1,
    dplusElevenDV0, dplusElevenDVAtOne]
  ring_nf
  ext n
  simp [Polynomial.coeff_X, Polynomial.coeff_C,
    Polynomial.coeff_X_pow, Polynomial.coeff_one,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul_C]
  split_ifs <;> norm_num at *

/-- Discriminant of the shifted support polynomial. -/
def dplusElevenDDiscriminant : ℚ :=
  dplusElevenDShiftB ^ 2 - 4 * dplusElevenDShiftC

/-- The centre of the two roots of the shifted support. -/
def dplusElevenDRootCenter : ℚ :=
  -dplusElevenDShiftB / 2

/-- Value of the linear `R` polynomial at the root centre. -/
def dplusElevenDRAtRootCenter : ℚ :=
  dplusElevenDV1 * dplusElevenDRootCenter + dplusElevenDVAtOne

/-- The squared half-difference of the two `R` values. -/
def dplusElevenDHalfRDifferenceSq : ℚ :=
  dplusElevenDV1 ^ 2 * dplusElevenDDiscriminant / 4

end

end Cuboid2
