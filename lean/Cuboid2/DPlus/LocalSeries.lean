import Cuboid2.DPlus.Basic

/-!
# Exact local algebra for the direct `p=3` argument on `D+`

These are the finite polynomial identities underlying the local certificate.
They deliberately avoid treating an external truncated series as a premise:
each claimed truncation is expressed by exact divisibility of its residual.
-/

namespace Cuboid2

noncomputable section

/-- The implicit equation at infinity in the exact chart
`w=1/a`, `t=2a²/R`. -/
def dplusInfinityRelation (t w : ℚ) : ℚ :=
  w - t ^ 2 * (1 - 2 * w ^ 3 + (5 / 4 : ℚ) * w ^ 4)

/-- The pinned approximation to the integral branch at infinity. -/
def dplusInfinityWApprox (t : ℚ) : ℚ :=
  t ^ 2 - 2 * t ^ 8 + (5 / 4 : ℚ) * t ^ 10

/--
Substitution of the pinned series satisfies the implicit curve equation
through degree 13.  The explicit quotient is part of the kernel-checked
certificate.
-/
theorem dplusInfinityWApprox_residual (t : ℚ) :
    dplusInfinityRelation t (dplusInfinityWApprox t) =
      t ^ 14 *
        (-12 + (35 / 2 : ℚ) * t ^ 2 - (25 / 4 : ℚ) * t ^ 4 +
          24 * t ^ 6 - 60 * t ^ 8 + (375 / 8 : ℚ) * t ^ 10 -
          (887 / 32 : ℚ) * t ^ 12 + 70 * t ^ 14 -
          (375 / 4 : ℚ) * t ^ 16 + (1625 / 32 : ℚ) * t ^ 18 -
          (1905 / 64 : ℚ) * t ^ 20 + 50 * t ^ 22 -
          (375 / 8 : ℚ) * t ^ 24 + (625 / 32 : ℚ) * t ^ 26 -
          (3125 / 1024 : ℚ) * t ^ 28) := by
  simp [dplusInfinityRelation, dplusInfinityWApprox]
  ring

/-- The infinity relation has unit formal derivative in `w` at the origin. -/
theorem dplusInfinityRelation_derivativeW_at_origin :
    Polynomial.eval 0
        (Polynomial.derivative
          (Polynomial.X : Polynomial ℚ)) = 1 := by
  norm_num

/-- The affine cofactor used in the zero disk. -/
def dplusCofactor (a : ℚ) : ℚ := 4 * a ^ 4 - 8 * a + 5

/-- Exact factorization of the curve right side. -/
theorem dplusRhs_eq_mul_cofactor (a : ℚ) :
    dplusRhs a = a * dplusCofactor a := by
  simp [dplusRhs, dplusCofactor]
  ring

/-- If the abscissa is a square, the zero-disk quotient has the displayed
square relation. -/
theorem dplus_zero_disk_square_quotient
    {a R u : ℚ} (ha : a = u ^ 2) (hcurve : R ^ 2 = dplusRhs a)
    (hu : u ≠ 0) :
    (R / u) ^ 2 = dplusCofactor a := by
  rw [dplusRhs_eq_mul_cofactor, ha] at hcurve
  subst a
  calc
    (R / u) ^ 2 = R ^ 2 / u ^ 2 := by ring
    _ = (u ^ 2 * dplusCofactor (u ^ 2)) / u ^ 2 := by
      rw [hcurve]
    _ = dplusCofactor (u ^ 2) := by field_simp [hu]

/-- Exact rational relation defining the infinity chart. -/
theorem dplus_infinity_chart_relation
    {a R t w : ℚ}
    (ha : a ≠ 0) (hR : R ≠ 0)
    (hcurve : R ^ 2 = dplusRhs a)
    (hw : w = 1 / a) (ht : t = 2 * a ^ 2 / R) :
    dplusInfinityRelation t w = 0 := by
  subst w
  subst t
  simp [dplusInfinityRelation]
  field_simp [ha, hR]
  rw [hcurve]
  simp [dplusRhs]
  ring

end

end Cuboid2
