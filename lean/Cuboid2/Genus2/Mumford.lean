import Mathlib

/-!
# Specialized genus-two Mumford pairs

This file deliberately avoids introducing Jacobian schemes.  It records the
exact polynomial conditions used by the explicit genus-two certificates in
this repository.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- A Mumford pair `(u,v)` for an odd-degree hyperelliptic model `Y²=f(X)`. -/
structure MumfordPair (K : Type*) [CommRing K] where
  u : K[X]
  v : K[X]

namespace MumfordPair

variable {K : Type*} [CommRing K] [Nontrivial K]

/-- Reducedness conditions specialized to genus two. -/
def IsReduced (D : MumfordPair K) : Prop :=
  D.u.Monic ∧ D.u.degree ≤ (2 : WithBot ℕ) ∧ D.v.degree < D.u.degree

/-- Exact validity of a Mumford pair on `Y²=f(X)`. -/
def ValidOn (f : K[X]) (D : MumfordPair K) : Prop :=
  D.IsReduced ∧ D.u ∣ f - D.v ^ 2

/-- The neutral reduced pair. -/
def infinity : MumfordPair K where
  u := 1
  v := 0

@[simp] theorem infinity_u : (infinity : MumfordPair K).u = 1 := rfl
@[simp] theorem infinity_v : (infinity : MumfordPair K).v = 0 := rfl

/-- The neutral pair is valid on every odd-degree model. -/
theorem infinity_validOn (f : K[X]) : (infinity : MumfordPair K).ValidOn f := by
  constructor
  · refine ⟨monic_one, ?_, ?_⟩
    · change degree (1 : K[X]) ≤ 2
      rw [degree_one]
      norm_num
    · change degree (0 : K[X]) < degree (1 : K[X])
      rw [degree_zero, degree_one]
      norm_num
  · simp

/-- Mumford representation of the divisor class `(a,r)-∞`. -/
def ofPoint (a r : K) : MumfordPair K where
  u := X - C a
  v := C r

@[simp] theorem ofPoint_u (a r : K) : (ofPoint a r).u = X - C a := rfl
@[simp] theorem ofPoint_v (a r : K) : (ofPoint a r).v = C r := rfl

/-- A rational affine point produces a valid reduced Mumford pair. -/
theorem ofPoint_validOn
    {f : K[X]} {a r : K} (hpoint : eval a f = r ^ 2) :
    (ofPoint a r).ValidOn f := by
  constructor
  · refine ⟨monic_X_sub_C a, ?_, ?_⟩
    · change degree (X - C a) ≤ 2
      rw [degree_X_sub_C]
      norm_num
    · by_cases hr : r = 0
      · change degree (C r) < degree (X - C a)
        rw [hr, C_0, degree_zero, degree_X_sub_C]
        norm_num
      · change degree (C r) < degree (X - C a)
        rw [degree_C hr, degree_X_sub_C]
        norm_num
  · rw [show (ofPoint a r).u = X - C a by rfl, dvd_iff_isRoot]
    simp [ofPoint, IsRoot, hpoint]

/-- Hyperelliptic negation changes only `v`. -/
def neg (D : MumfordPair K) : MumfordPair K where
  u := D.u
  v := -D.v

@[simp] theorem neg_u (D : MumfordPair K) : D.neg.u = D.u := rfl
@[simp] theorem neg_v (D : MumfordPair K) : D.neg.v = -D.v := rfl
@[simp] theorem neg_neg (D : MumfordPair K) : D.neg.neg = D := by
  cases D
  simp [neg]

/-- Validity is invariant under hyperelliptic negation. -/
theorem validOn_neg_iff {f : K[X]} {D : MumfordPair K} :
    D.neg.ValidOn f ↔ D.ValidOn f := by
  constructor <;> intro h
  · rcases h with ⟨⟨hu, hdegree, hvdegree⟩, hdiv⟩
    refine ⟨⟨hu, hdegree, ?_⟩, ?_⟩
    · simpa [neg, degree_neg] using hvdegree
    · simpa [neg] using hdiv
  · rcases h with ⟨⟨hu, hdegree, hvdegree⟩, hdiv⟩
    refine ⟨⟨hu, hdegree, ?_⟩, ?_⟩
    · simpa [neg, degree_neg] using hvdegree
    · simpa [neg] using hdiv

/-- Equality of pairs is coefficientwise equality of the two polynomials. -/
@[ext] theorem ext {D E : MumfordPair K} (hu : D.u = E.u) (hv : D.v = E.v) : D = E := by
  cases D
  cases E
  simp_all

end MumfordPair

end

end Cuboid2
