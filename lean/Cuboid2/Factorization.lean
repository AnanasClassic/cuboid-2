import Cuboid2.Polynomial

/-!
# Factorization cases

This file fixes Lean-level meanings for the three cases in the streamlined
proof.  The definitions do not encode any external certificate as an axiom.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- A rational linear factor of the normalized quintic. -/
def LinearQuarticCase (s : ℚ) : Prop :=
  ∃ r : ℚ, IsRoot (normalizedQuintic s) r

/-- A monic rational quadratic times a monic rational cubic. -/
def QuadraticCubicCase (s : ℚ) : Prop :=
  ∃ A B : ℚ[X],
    A.Monic ∧ A.natDegree = 2 ∧
    B.Monic ∧ B.natDegree = 3 ∧
    normalizedQuintic s = A * B

/-- The Capell-type symmetric `5+5` factorization of `P_s(u^2)`. -/
def SymmetricFiveFiveCase (s : ℚ) : Prop :=
  ∃ R : ℚ[X],
    R.Monic ∧ R.natDegree = 5 ∧ Irreducible R ∧
    (normalizedQuintic s).comp (X ^ 2) = R * (-(R.comp (-X)))

/-- An explicit factorization in which neither factor is a unit. -/
def HasNontrivialFactorization {R : Type*} [Monoid R] (x : R) : Prop :=
  ∃ a b : R, x = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b

/-- The elementary implication from absence of proper factorizations to irreducibility. -/
theorem irreducible_of_no_nontrivial_factorization
    {R : Type*} [CommMonoidWithZero R] {x : R}
    (hx : ¬ IsUnit x) (hfac : ¬ HasNontrivialFactorization x) :
    Irreducible x := by
  refine ⟨hx, ?_⟩
  intro a b hab
  by_contra hunit
  push_neg at hunit
  exact hfac ⟨a, b, hab, hunit.1, hunit.2⟩

/-- Logical assembly of the three-case contradiction. -/
theorem irreducible_of_factorization_cases
    {P : ℚ[X]} {linear quadratic symmetric : Prop}
    (classify : ¬ Irreducible P → linear ∨ quadratic ∨ symmetric)
    (hlinear : ¬ linear)
    (hquadratic : ¬ quadratic)
    (hsymmetric : ¬ symmetric) :
    Irreducible P := by
  apply Classical.byContradiction
  intro hred
  rcases classify hred with h | h | h
  · exact hlinear h
  · exact hquadratic h
  · exact hsymmetric h

/-- Positivity of the normalized parameter in the admissible domain. -/
theorem sharipovParameter_pos {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    0 < sharipovParameter p q := by
  unfold sharipovParameter
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have hqq : (0 : ℚ) < q := by exact_mod_cast hq
  positivity

/-- The excluded fibre `s=1` is exactly `p=q` for positive parameters. -/
theorem sharipovParameter_ne_one
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hne : p ≠ q) :
    sharipovParameter p q ≠ 1 := by
  intro hs
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have hqq : (0 : ℚ) < q := by exact_mod_cast hq
  have hq0 : (q : ℚ) ≠ 0 := ne_of_gt hqq
  unfold sharipovParameter at hs
  have hsquares : (p : ℚ) ^ 2 = (q : ℚ) ^ 2 := by
    field_simp [hq0] at hs
    nlinarith
  have hcast : (p : ℚ) = (q : ℚ) := by nlinarith
  exact hne (Nat.cast_injective hcast)

end

end Cuboid2
