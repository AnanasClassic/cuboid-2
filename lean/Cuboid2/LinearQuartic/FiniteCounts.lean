import Cuboid2.Genus2.FiniteMumford
import Cuboid2.LinearQuartic.Basic

/-!
# Finite-field certificates for the linear--quartic curve

The small reductions used by the linear-factor argument are checked by
ordinary kernel reduction.  In particular, this file does not trust the
external point-counting scripts: both curve points and reduced Mumford
representatives are finite coefficient types whose defining equations are
evaluated by `decide`.
-/

namespace Cuboid2

open Polynomial

noncomputable section

local instance linearQuarticFiniteFactPrime3 : Fact (Nat.Prime 3) :=
  ⟨by norm_num⟩
local instance linearQuarticFiniteFactPrime5 : Fact (Nat.Prime 5) :=
  ⟨by norm_num⟩

/-- The odd-degree linear--quartic model as a polynomial over any ring. -/
def linearQuarticPolynomial {R : Type*} [CommRing R] : R[X] :=
  X ^ 5 + C 21 * X ^ 4 + C 26 * X ^ 3 +
    C 10 * X ^ 2 + C 5 * X + 1

/-- Polynomial evaluation agrees with the affine equation used over `ℚ`. -/
theorem eval_linearQuarticPolynomial
    {R : Type*} [CommRing R] (t : R) :
    eval t (linearQuarticPolynomial : R[X]) =
      linearQuarticCurveRhs t := by
  simp [linearQuarticPolynomial, linearQuarticCurveRhs]

/-- A point of an odd-degree model over a finite field: the unique point at
infinity or an affine pair of coordinates. -/
inductive LinearQuarticFinitePoint (K : Type*) where
  | infinity
  | affine (t w : K)
deriving DecidableEq, Fintype

namespace LinearQuarticFinitePoint

variable {K : Type*} [CommRing K]

/-- The exact curve equation for a finite-field point. -/
def Valid : LinearQuarticFinitePoint K → Prop
  | .infinity => True
  | .affine t w => w ^ 2 = linearQuarticCurveRhs t

instance [DecidableEq K] (P : LinearQuarticFinitePoint K) :
    Decidable P.Valid := by
  cases P <;> simp [Valid] <;> infer_instance

end LinearQuarticFinitePoint

/-- The finite set `C(F₃)`, including the point at infinity. -/
abbrev LinearQuarticPointsF3 :=
  {P : LinearQuarticFinitePoint (ZMod 3) // P.Valid}

/-- The finite set `C(F₅)`, including the point at infinity. -/
abbrev LinearQuarticPointsF5 :=
  {P : LinearQuarticFinitePoint (ZMod 5) // P.Valid}

/-- Exact kernel enumeration gives `#C(F₃)=6`. -/
theorem card_linearQuarticPointsF3 :
    Fintype.card LinearQuarticPointsF3 = 6 := by
  decide

/-- Exact kernel enumeration gives `#C(F₅)=6`. -/
theorem card_linearQuarticPointsF5 :
    Fintype.card LinearQuarticPointsF5 = 6 := by
  decide

/-- The six residue points over `F₅`, written in the same order as the six
known rational points. -/
def knownLinearQuarticPointsF5 :
    List (LinearQuarticFinitePoint (ZMod 5)) :=
  [ .infinity,
    .affine 4 0,
    .affine 0 1,
    .affine 0 4,
    .affine 1 3,
    .affine 1 2 ]

/-- The displayed six points are exactly all points of `C(F₅)`. -/
theorem linearQuarticPointF5_valid_iff_mem_known
    (P : LinearQuarticFinitePoint (ZMod 5)) :
    P.Valid ↔ P ∈ knownLinearQuarticPointsF5 := by
  decide +revert

/-- The coefficient of `X` in the remainder for a degree-two Mumford pair. -/
def linearQuarticMumfordRemainderX
    {K : Type*} [CommRing K] (u1 u0 v1 v0 : K) : K :=
  u0 ^ 2 - 3 * u0 * u1 ^ 2 + u1 ^ 4 +
    42 * u0 * u1 - 21 * u1 ^ 3 + 26 * u1 ^ 2 -
    26 * u0 - 10 * u1 + 5 +
    u1 * v1 ^ 2 - 2 * v0 * v1

/-- The constant coefficient in the remainder for a degree-two Mumford pair. -/
def linearQuarticMumfordRemainderC
    {K : Type*} [CommRing K] (u1 u0 v1 v0 : K) : K :=
  -2 * u0 ^ 2 * u1 + u0 * u1 ^ 3 +
    21 * u0 ^ 2 - 21 * u0 * u1 ^ 2 +
    26 * u0 * u1 - 10 * u0 + 1 +
    u0 * v1 ^ 2 - v0 ^ 2

/-- The quotient in the exact degree-two division identity. -/
def linearQuarticMumfordQuotient
    {K : Type*} [CommRing K] (u1 u0 v1 : K) : K[X] :=
  X ^ 3 + C (21 - u1) * X ^ 2 +
    C (u1 ^ 2 - 21 * u1 + 26 - u0) * X +
    C (10 - v1 ^ 2 - 21 * u0 + 2 * u0 * u1 -
      u1 ^ 3 + 21 * u1 ^ 2 - 26 * u1)

/--
The exact long-division identity behind the degree-two coefficient test.
This bridge is ring-theoretic and is not established by finite enumeration.
-/
theorem linearQuartic_degreeTwo_division_identity
    {K : Type*} [CommRing K] (u1 u0 v1 v0 : K) :
    (linearQuarticPolynomial : K[X]) -
          (C v1 * X + C v0) ^ 2 =
      (X ^ 2 + C u1 * X + C u0) *
          linearQuarticMumfordQuotient u1 u0 v1 +
        C (linearQuarticMumfordRemainderX u1 u0 v1 v0) * X +
        C (linearQuarticMumfordRemainderC u1 u0 v1 v0) := by
  simp [linearQuarticPolynomial, linearQuarticMumfordQuotient,
    linearQuarticMumfordRemainderX, linearQuarticMumfordRemainderC]
  simp only [Polynomial.C_ofNat]
  ring

/-- The coefficient remainder of `f-v²` modulo the monic `u` represented by
a finite Mumford pair.  It is written explicitly so finite enumeration does
not invoke a noncomputable polynomial division algorithm. -/
def linearQuarticMumfordValid
    {K : Type*} [CommRing K] : FiniteMumford K → Prop
  | .infinity => True
  | .degreeOne u0 v0 =>
      v0 ^ 2 = linearQuarticCurveRhs (-u0)
  | .degreeTwo u1 u0 v1 v0 =>
      linearQuarticMumfordRemainderX u1 u0 v1 v0 = 0 ∧
        linearQuarticMumfordRemainderC u1 u0 v1 v0 = 0

instance {K : Type*} [CommRing K] [DecidableEq K]
    (D : FiniteMumford K) : Decidable (linearQuarticMumfordValid D) := by
  cases D <;> simp [linearQuarticMumfordValid] <;> infer_instance

/--
The explicit coefficient test is exactly the generic Mumford divisibility
condition for the linear--quartic polynomial.
-/
theorem linearQuarticMumfordValid_iff_validOn
    {K : Type*} [Field K] (D : FiniteMumford K) :
    linearQuarticMumfordValid D ↔
      D.ValidOn (linearQuarticPolynomial : K[X]) := by
  cases D with
  | infinity =>
      constructor
      · intro _
        exact FiniteMumford.infinity_validOn _
      · intro _
        trivial
  | degreeOne u0 v0 =>
      change
        v0 ^ 2 = linearQuarticCurveRhs (-u0) ↔
          X + C u0 ∣
            (linearQuarticPolynomial : K[X]) - C v0 ^ 2
      rw [show (X + C u0 : K[X]) = X - C (-u0) by simp]
      rw [dvd_iff_isRoot]
      simp only [IsRoot, eval_sub, eval_pow, eval_C]
      rw [eval_linearQuarticPolynomial]
      constructor
      · intro h
        rw [h, sub_self]
      · intro h
        exact (sub_eq_zero.mp h).symm
  | degreeTwo u1 u0 v1 v0 =>
      let u : K[X] := X ^ 2 + C u1 * X + C u0
      let r : K[X] :=
        C (linearQuarticMumfordRemainderX u1 u0 v1 v0) * X +
          C (linearQuarticMumfordRemainderC u1 u0 v1 v0)
      have hu : u.Monic := by
        exact (isMonicOfDegree_add_add_two u1 u0).monic
      have hid :
          (linearQuarticPolynomial : K[X]) -
                (C v1 * X + C v0) ^ 2 =
            u * linearQuarticMumfordQuotient u1 u0 v1 + r := by
        rw [linearQuartic_degreeTwo_division_identity u1 u0 v1 v0]
        change
          (X ^ 2 + C u1 * X + C u0) *
                linearQuarticMumfordQuotient u1 u0 v1 +
              C (linearQuarticMumfordRemainderX u1 u0 v1 v0) * X +
            C (linearQuarticMumfordRemainderC u1 u0 v1 v0) =
            (X ^ 2 + C u1 * X + C u0) *
                linearQuarticMumfordQuotient u1 u0 v1 +
              (C (linearQuarticMumfordRemainderX u1 u0 v1 v0) * X +
                C (linearQuarticMumfordRemainderC u1 u0 v1 v0))
        ring
      have hdvdsub :
          u ∣
            ((linearQuarticPolynomial : K[X]) -
                (C v1 * X + C v0) ^ 2) - r := by
        refine ⟨linearQuarticMumfordQuotient u1 u0 v1, ?_⟩
        rw [hid]
        ring
      have hmod :
          ((linearQuarticPolynomial : K[X]) -
              (C v1 * X + C v0) ^ 2) %ₘ u = r %ₘ u :=
        modByMonic_eq_of_dvd_sub hu hdvdsub
      have hrdegree : r.degree < u.degree := by
        have hrle : r.degree ≤ (1 : WithBot ℕ) := by
          apply degree_add_le_of_degree_le (n := 1)
          · simpa only [pow_one] using
              (degree_C_mul_X_pow_le 1
                (linearQuarticMumfordRemainderX u1 u0 v1 v0))
          · exact degree_C_le.trans (by norm_num)
        have hudegree : u.degree = (2 : WithBot ℕ) := by
          exact degree_eq_natDegree hu.ne_zero ▸
            congrArg WithBot.some
              (isMonicOfDegree_add_add_two u1 u0).natDegree_eq
        rw [hudegree]
        exact hrle.trans_lt (by norm_num)
      have hrmod : r %ₘ u = r :=
        (modByMonic_eq_self_iff hu).2 hrdegree
      have hdvd_iff :
          u ∣
              (linearQuarticPolynomial : K[X]) -
                (C v1 * X + C v0) ^ 2 ↔
            r = 0 := by
        rw [← modByMonic_eq_zero_iff_dvd hu, hmod, hrmod]
      change
        linearQuarticMumfordRemainderX u1 u0 v1 v0 = 0 ∧
            linearQuarticMumfordRemainderC u1 u0 v1 v0 = 0 ↔
          u ∣
            (linearQuarticPolynomial : K[X]) -
              (C v1 * X + C v0) ^ 2
      rw [hdvd_iff]
      constructor
      · rintro ⟨hx, hc⟩
        simp [r, hx, hc]
      · intro hr
        have hx := congrArg (fun p : K[X] => p.coeff 1) hr
        have hc := congrArg (fun p : K[X] => p.coeff 0) hr
        simpa [r] using And.intro hx hc

/-- The explicit coefficient subtype is canonically equivalent to the
generic `FiniteMumford.ValidOn` subtype. -/
def linearQuarticMumfordEquivValidOn
    {K : Type*} [Field K] :
    {D : FiniteMumford K // linearQuarticMumfordValid D} ≃
      {D : FiniteMumford K //
        D.ValidOn (linearQuarticPolynomial : K[X])} where
  toFun D := ⟨D.1, (linearQuarticMumfordValid_iff_validOn D.1).mp D.2⟩
  invFun D := ⟨D.1, (linearQuarticMumfordValid_iff_validOn D.1).mpr D.2⟩
  left_inv D := by cases D; rfl
  right_inv D := by cases D; rfl

/-- The finite reduced Mumford representatives on the reduction at `3`. -/
abbrev LinearQuarticMumfordF3 :=
  {D : FiniteMumford (ZMod 3) // linearQuarticMumfordValid D}

/-- The finite reduced Mumford representatives on the reduction at `5`. -/
abbrev LinearQuarticMumfordF5 :=
  {D : FiniteMumford (ZMod 5) // linearQuarticMumfordValid D}

/-- The same reduced representatives at `3`, stated using generic polynomial
divisibility rather than the optimized coefficient predicate. -/
abbrev LinearQuarticMumfordValidOnF3 :=
  {D : FiniteMumford (ZMod 3) //
    D.ValidOn (linearQuarticPolynomial : (ZMod 3)[X])}

/-- The same reduced representatives at `5`, stated using generic polynomial
divisibility rather than the optimized coefficient predicate. -/
abbrev LinearQuarticMumfordValidOnF5 :=
  {D : FiniteMumford (ZMod 5) //
    D.ValidOn (linearQuarticPolynomial : (ZMod 5)[X])}

noncomputable instance : Fintype LinearQuarticMumfordValidOnF3 :=
  Fintype.ofEquiv LinearQuarticMumfordF3
    (linearQuarticMumfordEquivValidOn :
      LinearQuarticMumfordF3 ≃ LinearQuarticMumfordValidOnF3)

noncomputable instance : Fintype LinearQuarticMumfordValidOnF5 :=
  Fintype.ofEquiv LinearQuarticMumfordF5
    (linearQuarticMumfordEquivValidOn :
      LinearQuarticMumfordF5 ≃ LinearQuarticMumfordValidOnF5)

/-- Exact kernel enumeration of the reduced Mumford representatives at `3`. -/
theorem card_linearQuarticMumfordF3 :
    Fintype.card LinearQuarticMumfordF3 = 22 := by
  decide

/-- Exact kernel enumeration of the reduced Mumford representatives at `5`. -/
theorem card_linearQuarticMumfordF5 :
    Fintype.card LinearQuarticMumfordF5 = 28 := by
  decide

/-- The generic divisibility formulation also has exactly `22`
representatives over `F₃`. -/
theorem card_linearQuarticMumfordValidOnF3 :
    Fintype.card LinearQuarticMumfordValidOnF3 = 22 := by
  rw [← Fintype.card_congr
    (linearQuarticMumfordEquivValidOn :
      LinearQuarticMumfordF3 ≃ LinearQuarticMumfordValidOnF3)]
  exact card_linearQuarticMumfordF3

/-- The generic divisibility formulation also has exactly `28`
representatives over `F₅`. -/
theorem card_linearQuarticMumfordValidOnF5 :
    Fintype.card LinearQuarticMumfordValidOnF5 = 28 := by
  rw [← Fintype.card_congr
    (linearQuarticMumfordEquivValidOn :
      LinearQuarticMumfordF5 ≃ LinearQuarticMumfordValidOnF5)]
  exact card_linearQuarticMumfordF5

/-- Consequently the two small Jacobian counts have gcd `2`, the exact
torsion bound used by the rank-one argument. -/
theorem gcd_linearQuarticMumford_cards :
    Nat.gcd
        (Fintype.card LinearQuarticMumfordF3)
        (Fintype.card LinearQuarticMumfordF5) = 2 := by
  rw [card_linearQuarticMumfordF3, card_linearQuarticMumfordF5]
  decide

end

end Cuboid2
