import Cuboid2.Genus2.Mumford
import Mathlib.Data.ZMod.Basic

/-!
# Finite reduced Mumford representatives

For an odd-degree genus-two model, every reduced divisor class has one of the
three shapes encoded below: degree zero, one, or two.  This representation is
finite over a finite field and is therefore suitable for kernel evaluation of
the small Jacobians used by the proof.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- Coefficient representation of a monic reduced Mumford pair of degree at most two. -/
inductive FiniteMumford (K : Type*) where
  | infinity
  | degreeOne (u0 v0 : K)
  | degreeTwo (u1 u0 v1 v0 : K)
deriving DecidableEq, Fintype

namespace FiniteMumford

variable {K : Type*} [Field K]

/-- The monic `u` polynomial encoded by a finite representative. -/
def u : FiniteMumford K → K[X]
  | infinity => 1
  | degreeOne u0 _ => X + C u0
  | degreeTwo u1 u0 _ _ => X ^ 2 + C u1 * X + C u0

/-- The reduced `v` polynomial encoded by a finite representative. -/
def v : FiniteMumford K → K[X]
  | infinity => 0
  | degreeOne _ v0 => C v0
  | degreeTwo _ _ v1 v0 => C v1 * X + C v0

/-- Forget the finite coefficient representation. -/
def toMumfordPair (D : FiniteMumford K) : MumfordPair K where
  u := D.u
  v := D.v

/-- The exact Mumford divisibility condition. -/
def ValidOn (f : K[X]) (D : FiniteMumford K) : Prop :=
  D.u ∣ f - D.v ^ 2

instance [DecidableEq K] (f : K[X]) (D : FiniteMumford K) :
    Decidable (D.ValidOn f) := inferInstance

@[simp] theorem infinity_validOn (f : K[X]) :
    (infinity : FiniteMumford K).ValidOn f := by
  simp [ValidOn, u, v]

/-- Every encoded `u` is monic. -/
theorem u_monic (D : FiniteMumford K) : D.u.Monic := by
  cases D <;> simp [u]

/-- Every encoded `u` has degree at most two. -/
theorem u_degree_le_two (D : FiniteMumford K) :
    D.u.degree ≤ (2 : WithBot ℕ) := by
  cases D <;> simp [u]

/-- Every encoded `v` has degree strictly smaller than its `u`. -/
theorem v_degree_lt_u_degree (D : FiniteMumford K) :
    D.v.degree < D.u.degree := by
  cases D with
  | infinity => simp [u, v]
  | degreeOne u0 v0 =>
      by_cases hv : v0 = 0
      · simp [u, v, hv]
      · simp [u, v, hv]
  | degreeTwo u1 u0 v1 v0 =>
      have hvle : (C v1 * X + C v0 : K[X]).degree ≤ (1 : WithBot ℕ) := by
        apply degree_add_le_of_degree_le
        · exact (degree_C_mul_X_pow_le 1 v1).trans (by norm_num)
        · exact degree_C_le.trans (by norm_num)
      have hu : (X ^ 2 + C u1 * X + C u0 : K[X]).degree = 2 := by
        rw [degree_add_eq_left_of_degree_lt]
        · simp
        · apply lt_of_le_of_lt
          · apply degree_add_le_of_degree_le
            · exact (degree_C_mul_X_pow_le 1 u1).trans (by norm_num)
            · exact degree_C_le.trans (by norm_num)
          · norm_num
      rw [v, u, hu]
      exact hvle.trans_lt (by norm_num)

/-- Valid finite representatives satisfy the generic genus-two predicate. -/
theorem toMumfordPair_validOn
    {f : K[X]} {D : FiniteMumford K} (h : D.ValidOn f) :
    D.toMumfordPair.ValidOn f := by
  exact ⟨⟨D.u_monic, D.u_degree_le_two, D.v_degree_lt_u_degree⟩, h⟩

end FiniteMumford

/-- The reduction of `D+` over `F₇`. -/
def dplusPolynomialF7 : (ZMod 7)[X] :=
  C 4 * X ^ 5 - C 8 * X ^ 2 + C 5 * X

/-- All reduced Mumford representatives satisfying the `D+` equation over `F₇`. -/
abbrev DPlusMumfordF7 :=
  {D : FiniteMumford (ZMod 7) // D.ValidOn dplusPolynomialF7}

/--
The exact finite enumeration used by the integral 3-saturation argument:
there are 42 reduced Mumford representatives on `D+` over `F₇`.
-/
theorem card_dplusMumfordF7 : Fintype.card DPlusMumfordF7 = 42 := by
  decide

end

end Cuboid2
