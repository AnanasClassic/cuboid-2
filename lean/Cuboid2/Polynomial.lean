import Mathlib

/-!
# Sharipov's polynomial

The definitions in this file are transcribed from `src/symbolic_reduction.py`
and `paper/clean3.tex` in this repository.  They are deliberately stated over
a generic commutative ring so that coefficient and scaling identities can be
checked by the Lean kernel rather than imported from an external CAS.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- The terms below degree five in the normalized quintic `P_s`. -/
def normalizedQuinticLower {R : Type*} [CommRing R] (s : R) : R[X] :=
  C ((2 + s) * (3 - 2 * s)) * X ^ 4 +
    (C (1 + 10 * s + 4 * s ^ 2 - 14 * s ^ 3 + s ^ 4) * X ^ 3 +
      (C (-s * (1 - 14 * s + 4 * s ^ 2 + 10 * s ^ 3 + s ^ 4)) * X ^ 2 +
        (C (-s ^ 3 * (1 + 2 * s) * (-2 + 3 * s)) * X + C (-s ^ 5))))

/-- The exact normalized quintic `P_s(x)` used by the streamlined proof. -/
def normalizedQuintic {R : Type*} [CommRing R] (s : R) : R[X] :=
  X ^ 5 + normalizedQuinticLower s

/-- The terms below degree ten in Sharipov's polynomial `Q_{p,q}(t)`. -/
def sharipovLower {R : Type*} [CommRing R] (p q : R) : R[X] :=
  C ((2 * q ^ 2 + p ^ 2) * (3 * q ^ 2 - 2 * p ^ 2)) * X ^ 8 +
    (C (q ^ 8 + 10 * p ^ 2 * q ^ 6 + 4 * p ^ 4 * q ^ 4 -
          14 * p ^ 6 * q ^ 2 + p ^ 8) * X ^ 6 +
      (C (-p ^ 2 * q ^ 2 *
          (q ^ 8 - 14 * p ^ 2 * q ^ 6 + 4 * p ^ 4 * q ^ 4 +
            10 * p ^ 6 * q ^ 2 + p ^ 8)) * X ^ 4 +
        (C (-p ^ 6 * q ^ 6 * (q ^ 2 + 2 * p ^ 2) * (-2 * q ^ 2 + 3 * p ^ 2)) *
            X ^ 2 + C (-p ^ 10 * q ^ 10))))

/-- Sharipov's exact polynomial, over an arbitrary commutative coefficient ring. -/
def sharipovPolynomialOver {R : Type*} [CommRing R] (p q : R) : R[X] :=
  X ^ 10 + sharipovLower p q

/-- The canonical public integer polynomial `Q_{p,q}(t)`. -/
def sharipovPolynomial (p q : ℕ) : ℤ[X] :=
  sharipovPolynomialOver (p : ℤ) (q : ℤ)

/-- The same polynomial after coefficient extension to `ℚ`. -/
def sharipovPolynomialQ (p q : ℕ) : ℚ[X] :=
  sharipovPolynomialOver (p : ℚ) (q : ℚ)

/-- The normalized parameter `s=(p/q)^2`. -/
def sharipovParameter (p q : ℕ) : ℚ :=
  ((p : ℚ) / (q : ℚ)) ^ 2

private theorem normalizedQuinticLower_degree_le
    {R : Type*} [CommRing R] (s : R) :
    (normalizedQuinticLower s).degree ≤ (4 : WithBot ℕ) := by
  unfold normalizedQuinticLower
  apply degree_add_le_of_degree_le
  · exact degree_C_mul_X_pow_le 4 _
  · apply degree_add_le_of_degree_le
    · exact (degree_C_mul_X_pow_le 3 _).trans (by norm_num)
    · apply degree_add_le_of_degree_le
      · exact (degree_C_mul_X_pow_le 2 _).trans (by norm_num)
      · apply degree_add_le_of_degree_le
        · simpa only [pow_one] using
            (degree_C_mul_X_pow_le 1
              (-s ^ 3 * (1 + 2 * s) * (-2 + 3 * s))).trans (by norm_num)
        · exact degree_C_le.trans (by norm_num)

private theorem sharipovLower_degree_le
    {R : Type*} [CommRing R] (p q : R) :
    (sharipovLower p q).degree ≤ (8 : WithBot ℕ) := by
  unfold sharipovLower
  apply degree_add_le_of_degree_le
  · exact degree_C_mul_X_pow_le 8 _
  · apply degree_add_le_of_degree_le
    · exact (degree_C_mul_X_pow_le 6 _).trans (by norm_num)
    · apply degree_add_le_of_degree_le
      · exact (degree_C_mul_X_pow_le 4 _).trans (by norm_num)
      · apply degree_add_le_of_degree_le
        · exact (degree_C_mul_X_pow_le 2 _).trans (by norm_num)
        · exact degree_C_le.trans (by norm_num)

/-- `P_s` is monic. -/
theorem normalizedQuintic_monic {R : Type*} [CommRing R] (s : R) :
    (normalizedQuintic s).Monic := by
  apply monic_X_pow_add
  exact (normalizedQuinticLower_degree_le s).trans_lt (by norm_num)

/-- `P_s` has degree five over every nontrivial coefficient ring. -/
theorem normalizedQuintic_degree {R : Type*} [CommRing R] [Nontrivial R] (s : R) :
    (normalizedQuintic s).degree = 5 := by
  unfold normalizedQuintic
  rw [degree_add_eq_left_of_degree_lt
    ((normalizedQuinticLower_degree_le s).trans_lt (by norm_num))]
  simp

/-- `Q_{p,q}` is monic. -/
theorem sharipovPolynomialOver_monic {R : Type*} [CommRing R] (p q : R) :
    (sharipovPolynomialOver p q).Monic := by
  apply monic_X_pow_add
  exact (sharipovLower_degree_le p q).trans_lt (by norm_num)

/-- `Q_{p,q}` has degree ten over every nontrivial coefficient ring. -/
theorem sharipovPolynomialOver_degree
    {R : Type*} [CommRing R] [Nontrivial R] (p q : R) :
    (sharipovPolynomialOver p q).degree = 10 := by
  unfold sharipovPolynomialOver
  rw [degree_add_eq_left_of_degree_lt
    ((sharipovLower_degree_le p q).trans_lt (by norm_num))]
  simp

@[simp] theorem normalizedQuintic_coeff_five (s : ℚ) :
    (normalizedQuintic s).coeff 5 = 1 := by
  rw [← (normalizedQuintic_monic s).leadingCoeff]
  rw [leadingCoeff, natDegree_eq_of_degree_eq_some (normalizedQuintic_degree s)]

@[simp] theorem sharipovPolynomial_coeff_ten (p q : ℕ) :
    (sharipovPolynomial p q).coeff 10 = 1 := by
  rw [← (sharipovPolynomialOver_monic (p : ℤ) (q : ℤ)).leadingCoeff]
  rw [leadingCoeff,
    natDegree_eq_of_degree_eq_some (sharipovPolynomialOver_degree (p : ℤ) (q : ℤ))]

@[simp] theorem sharipovPolynomial_coeff_zero (p q : ℕ) :
    (sharipovPolynomial p q).coeff 0 = -((p : ℤ) ^ 10 * (q : ℤ) ^ 10) := by
  simp [sharipovPolynomial, sharipovPolynomialOver, sharipovLower]

@[simp] theorem sharipovPolynomial_natDegree (p q : ℕ) :
    (sharipovPolynomial p q).natDegree = 10 :=
  natDegree_eq_of_degree_eq_some
    (sharipovPolynomialOver_degree (p : ℤ) (q : ℤ))

/-- The integer polynomial is primitive, by monicity. -/
theorem sharipovPolynomial_isPrimitive (p q : ℕ) :
    (sharipovPolynomial p q).IsPrimitive :=
  (sharipovPolynomialOver_monic (p : ℤ) (q : ℤ)).isPrimitive

/-- Mapping the integer definition to `ℚ` gives the independently stated rational definition. -/
theorem map_sharipovPolynomial (p q : ℕ) :
    (sharipovPolynomial p q).map (algebraMap ℤ ℚ) = sharipovPolynomialQ p q := by
  simp [sharipovPolynomial, sharipovPolynomialQ, sharipovPolynomialOver, sharipovLower]

/-- Exact Gauss-lemma transfer for the public polynomial. -/
theorem sharipovPolynomial_irreducible_iff_rational (p q : ℕ) :
    Irreducible (sharipovPolynomial p q) ↔ Irreducible (sharipovPolynomialQ p q) := by
  have h :=
    (sharipovPolynomialOver_monic (p : ℤ) (q : ℤ)).
      irreducible_iff_irreducible_map_fraction_map (K := ℚ)
  simpa only [map_sharipovPolynomial] using h

/--
The exact weighted scaling identity from the paper, stated pointwise over any
field.  Pointwise equality is the form used by all later root and
factorization transports.
-/
theorem eval_sharipov_scaling
    {K : Type*} [Field K] (p q t : K) (hq : q ≠ 0) :
    eval t (sharipovPolynomialOver p q) =
      q ^ 20 * eval (t ^ 2 / q ^ 4) (normalizedQuintic ((p / q) ^ 2)) := by
  simp [sharipovPolynomialOver, sharipovLower, normalizedQuintic,
    normalizedQuinticLower]
  field_simp [hq]
  ring

/-- Specialization of the scaling identity to the public natural parameters. -/
theorem eval_sharipovPolynomialQ_scaling
    {p q : ℕ} (hq : 0 < q) (t : ℚ) :
    eval t (sharipovPolynomialQ p q) =
      (q : ℚ) ^ 20 *
        eval (t ^ 2 / (q : ℚ) ^ 4) (normalizedQuintic (sharipovParameter p q)) := by
  apply eval_sharipov_scaling
  exact_mod_cast (Nat.ne_of_gt hq)

end

end Cuboid2
