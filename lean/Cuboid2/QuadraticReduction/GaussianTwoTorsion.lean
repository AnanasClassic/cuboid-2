import Cuboid2.QuadraticReduction.GaussianDescent

/-!
# Two-torsion on the two Gaussian elliptic quotients

The two fixed curves have exactly one nonzero rational point of order two.
The proof is elementary: a second two-torsion point would make the
discriminant of the remaining quadratic factor a square in `ℚ(i)`, while its
rational norm is `272`, which is not a square in `ℚ`.
-/

namespace Cuboid2

noncomputable section

open scoped QuadraticAlgebra

namespace GaussianTwoTorsion

open GaussianDescent

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

/-- An element of `ℚ(i)` whose square has norm `272` cannot exist. -/
theorem no_gaussian_square_of_norm_272
    (z w : GaussianRat) (hw : gaussianNorm w = 272)
    (hzw : z ^ 2 = w) : False := by
  have hnorm := congrArg gaussianNorm hzw
  have hsquare : IsSquare (272 : ℚ) := by
    refine ⟨gaussianNorm z, ?_⟩
    calc
      (272 : ℚ) = gaussianNorm w := hw.symm
      _ = gaussianNorm (z ^ 2) := hnorm.symm
      _ = gaussianNorm (z * z) := by rw [pow_two]
      _ = gaussianNorm z * gaussianNorm z := gaussianNorm_mul z z
  norm_num at hsquare

/-- The nonzero quadratic factor of `E₀` has no root in `ℚ(i)`. -/
theorem gaussianE0_quadratic_ne_zero (x : GaussianRat) :
    x ^ 2 + E0A * x + E0B ≠ 0 := by
  intro hx
  have hdisc :
      (2 * x + E0A) ^ 2 = E0A ^ 2 - 4 * E0B := by
    linear_combination 4 * hx
  have hnorm : gaussianNorm (E0A ^ 2 - 4 * E0B) = 272 := by
    norm_num [E0A, E0B, gaussianI, gaussianNorm,
      QuadraticAlgebra.norm_def, pow_two]
  exact no_gaussian_square_of_norm_272
    (2 * x + E0A) (E0A ^ 2 - 4 * E0B) hnorm hdisc

/-- The nonzero quadratic factor of `E₁` has no root in `ℚ(i)`. -/
theorem gaussianE1_quadratic_ne_zero (x : GaussianRat) :
    x ^ 2 + E1A * x + E1B ≠ 0 := by
  intro hx
  have hdisc :
      (2 * x + E1A) ^ 2 = E1A ^ 2 - 4 * E1B := by
    linear_combination 4 * hx
  have hnorm : gaussianNorm (E1A ^ 2 - 4 * E1B) = 272 := by
    norm_num [E1A, E1B, gaussianI, gaussianNorm,
      QuadraticAlgebra.norm_def, pow_two]
  exact no_gaussian_square_of_norm_272
    (2 * x + E1A) (E1A ^ 2 - 4 * E1B) hnorm hdisc

private theorem two_nsmul_eq_zero_iff_eq_neg
    {G : Type*} [AddCommGroup G] (P : G) :
    2 • P = 0 ↔ P = -P := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg]

/-- The only points killed by two on `E₀(ℚ(i))` are infinity and `(0,0)`. -/
theorem gaussianE0_two_torsion_classified
    (P : gaussianE0.toAffine.Point) (hP : 2 • P = 0) :
    P = 0 ∨ P = gaussianE0T := by
  rcases P with (_ | ⟨x, y, hxy⟩)
  · exact Or.inl rfl
  · right
    have hself :
        (WeierstrassCurve.Affine.Point.some x y hxy :
          gaussianE0.toAffine.Point) =
        -(WeierstrassCurve.Affine.Point.some x y hxy :
          gaussianE0.toAffine.Point) :=
      (two_nsmul_eq_zero_iff_eq_neg _).mp hP
    have hyNeg :
        y = gaussianE0.toAffine.negY x y :=
      (WeierstrassCurve.Affine.Point.some.inj hself).2
    have hy : y = 0 := by
      simp [gaussianE0, WeierstrassCurve.Affine.negY] at hyNeg
      have htwo : (2 : GaussianRat) * y = 0 := by
        linear_combination hyNeg
      exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
    have heq :
        y ^ 2 = x * (x ^ 2 + E0A * x + E0B) :=
      curve_equation_iff.mp hxy.left
    have hx : x = 0 := by
      rw [hy, zero_pow (by norm_num), zero_eq_mul] at heq
      rcases heq with hx | hx
      · exact hx
      · exact (gaussianE0_quadratic_ne_zero x hx).elim
    subst x
    subst y
    rfl

/-- The only points killed by two on `E₁(ℚ(i))` are infinity and `(0,0)`. -/
theorem gaussianE1_two_torsion_classified
    (P : gaussianE1.toAffine.Point) (hP : 2 • P = 0) :
    P = 0 ∨ P = gaussianE1T := by
  rcases P with (_ | ⟨x, y, hxy⟩)
  · exact Or.inl rfl
  · right
    have hself :
        (WeierstrassCurve.Affine.Point.some x y hxy :
          gaussianE1.toAffine.Point) =
        -(WeierstrassCurve.Affine.Point.some x y hxy :
          gaussianE1.toAffine.Point) :=
      (two_nsmul_eq_zero_iff_eq_neg _).mp hP
    have hyNeg :
        y = gaussianE1.toAffine.negY x y :=
      (WeierstrassCurve.Affine.Point.some.inj hself).2
    have hy : y = 0 := by
      simp [gaussianE1, WeierstrassCurve.Affine.negY] at hyNeg
      have htwo : (2 : GaussianRat) * y = 0 := by
        linear_combination hyNeg
      exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
    have heq :
        y ^ 2 = x * (x ^ 2 + E1A * x + E1B) :=
      curve_equation_iff.mp hxy.left
    have hx : x = 0 := by
      rw [hy, zero_pow (by norm_num), zero_eq_mul] at heq
      rcases heq with hx | hx
      · exact hx
      · exact (gaussianE1_quadratic_ne_zero x hx).elim
    subst x
    subst y
    rfl

end GaussianTwoTorsion

end

end Cuboid2
