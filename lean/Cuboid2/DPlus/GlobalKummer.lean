import Cuboid2.DPlus.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic.NormDet

/-!
# The fixed quartic Kummer algebra for `D+`

The two-descent artifact uses the étale algebra

`ℚ × ℚ[z]/(z⁴ - 16z + 20)`.

This file constructs its quartic factor directly and proves the first
global bridge that is available without a Jacobian or Selmer API: every
rational affine point maps to an explicit algebra element whose total norm
is a rational square.  The proof computes the actual `Algebra.norm`; the
norm condition is not stored as data in a certificate structure.

At the rational Weierstrass point the usual `x - θ` expression has zero
rational component.  The separate value `dplusTorsionKummerValue` is the
standard nonzero representative `(5, -z/2)` used by the pinned descent
artifact.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-! ## The quartic algebra and its exact norm -/

/-- The monic polynomial for the quartic factor in the `D+` étale algebra. -/
def dplusQuarticPolynomial : ℚ[X] :=
  X ^ 4 - C 16 * X + C 20

/-- The displayed quartic polynomial is monic. -/
theorem dplusQuarticPolynomial_monic :
    dplusQuarticPolynomial.Monic := by
  unfold dplusQuarticPolynomial
  monicity <;> norm_num

/-- The fixed quartic algebra `ℚ[z]/(z⁴-16z+20)`. -/
abbrev DPlusQuarticAlgebra :=
  AdjoinRoot dplusQuarticPolynomial

local instance dplusQuarticAlgebra_free :
    Module.Free ℚ DPlusQuarticAlgebra :=
  dplusQuarticPolynomial_monic.free_adjoinRoot

local instance dplusQuarticAlgebra_finite :
    Module.Finite ℚ DPlusQuarticAlgebra :=
  dplusQuarticPolynomial_monic.finite_adjoinRoot

/-- The image of `z` in the fixed quartic algebra. -/
def dplusQuarticRoot : DPlusQuarticAlgebra :=
  AdjoinRoot.root dplusQuarticPolynomial

/-- The defining equation is checked in the quotient algebra. -/
theorem dplusQuarticRoot_equation :
    dplusQuarticRoot ^ 4 - 16 * dplusQuarticRoot + 20 = 0 := by
  change
    AdjoinRoot.mk dplusQuarticPolynomial dplusQuarticPolynomial = 0
  exact AdjoinRoot.mk_self

/--
The genuine degree-four algebra norm of `a-z/2`.

Since `z/2` is a root of `4X⁴-8X+5`, the result is the expected quartic
cofactor divided by four.  The proof evaluates the multiplication matrix in
the power basis and asks the kernel to normalize its `4 × 4` determinant.
-/
theorem dplusQuarticNorm_sub_root_half (a : ℚ) :
    Algebra.norm ℚ
        (algebraMap ℚ DPlusQuarticAlgebra a -
          algebraMap ℚ DPlusQuarticAlgebra (1 / 2 : ℚ) *
            dplusQuarticRoot) =
      a ^ 4 - 2 * a + 5 / 4 := by
  let pb :=
    AdjoinRoot.powerBasis' dplusQuarticPolynomial_monic
  rw [Algebra.norm_eq_matrix_det pb.basis]
  change
    Matrix.det
      (Algebra.leftMulMatrix pb.basis
        (algebraMap ℚ DPlusQuarticAlgebra a -
          algebraMap ℚ DPlusQuarticAlgebra (1 / 2 : ℚ) * pb.gen)) =
      _
  simp only [map_sub, map_mul, AlgHomClass.commutes]
  rw [pb.leftMulMatrix]
  classical
  have hdim : pb.dim = 4 := by
    dsimp [pb]
    norm_num
      [dplusQuarticPolynomial,
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
  have hmin : pb.minpolyGen = dplusQuarticPolynomial := by
    rw [PowerBasis.minpolyGen_eq]
    dsimp [pb]
    exact
      AdjoinRoot.minpoly_powerBasis_gen_of_monic
        dplusQuarticPolynomial_monic
  rw [hdim, hmin]
  let M : Matrix (Fin 4) (Fin 4) ℚ :=
    !![a, 0, 0, 10;
       -(1 / 2), a, 0, -8;
       0, -(1 / 2), a, 0;
       0, 0, -(1 / 2), a]
  have hmatrix :
      (algebraMap ℚ (Matrix (Fin 4) (Fin 4) ℚ)) a -
          (algebraMap ℚ (Matrix (Fin 4) (Fin 4) ℚ)) (1 / 2) *
            Matrix.of (fun (i j : Fin 4) =>
              if (j : ℕ) + 1 = 4 then
                -dplusQuarticPolynomial.coeff i
              else if (i : ℕ) = j + 1 then 1 else 0) =
        M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp
        [dplusQuarticPolynomial, M,
          Algebra.algebraMap_eq_smul_one, Polynomial.coeff_X]
    all_goals ring
  rw [hmatrix]
  dsimp [M]
  eval_det
  ring

/-! ## The arbitrary-point Kummer candidate -/

/-- The product algebra used by the fixed `D+` two-descent. -/
abbrev DPlusEtaleAlgebra :=
  ℚ × DPlusQuarticAlgebra

/-- Product of the rational component with the quartic algebra norm. -/
def dplusEtaleNorm (x : DPlusEtaleAlgebra) : ℚ :=
  x.1 * Algebra.norm ℚ x.2

/-- The total norm is multiplicative. -/
theorem dplusEtaleNorm_mul
    (x y : DPlusEtaleAlgebra) :
    dplusEtaleNorm (x * y) =
      dplusEtaleNorm x * dplusEtaleNorm y := by
  simp [dplusEtaleNorm, map_mul]
  ring

/--
The degree-one `x-θ` value attached to an arbitrary rational affine point.

This is a raw element of the product algebra.  Passing from it to a
squareclass, then proving that all global classes occur in the four pinned
masks, requires the still-missing Selmer completeness theorem.
-/
def dplusPointKummerValue
    (P : DPlusAffinePoint) : DPlusEtaleAlgebra :=
  (P.a,
    algebraMap ℚ DPlusQuarticAlgebra P.a -
      algebraMap ℚ DPlusQuarticAlgebra (1 / 2 : ℚ) *
        dplusQuarticRoot)

/-- The total norm of the point value is exactly `(R/2)²`. -/
theorem dplusPointKummerValue_norm
    (P : DPlusAffinePoint) :
    dplusEtaleNorm (dplusPointKummerValue P) =
      (P.R / 2) ^ 2 := by
  rw [show
      dplusEtaleNorm (dplusPointKummerValue P) =
        P.a *
          Algebra.norm ℚ
            (algebraMap ℚ DPlusQuarticAlgebra P.a -
              algebraMap ℚ DPlusQuarticAlgebra (1 / 2 : ℚ) *
                dplusQuarticRoot) by
      rfl]
  rw [dplusQuarticNorm_sub_root_half]
  calc
    P.a * (P.a ^ 4 - 2 * P.a + 5 / 4) =
        dplusRhs P.a / 4 := by
          simp [dplusRhs]
          ring
    _ = P.R ^ 2 / 4 := by rw [P.onCurve]
    _ = (P.R / 2) ^ 2 := by ring

/-- Consequently every rational affine point lands in the square-norm
kernel of the raw product algebra. -/
theorem dplusPointKummerValue_norm_isSquare
    (P : DPlusAffinePoint) :
    IsSquare (dplusEtaleNorm (dplusPointKummerValue P)) := by
  refine ⟨P.R / 2, ?_⟩
  simpa [pow_two] using dplusPointKummerValue_norm P

/--
For a nonzero square-abscissa point, even the quartic component by itself
has square norm.  This is the exact norm-kernel condition used after the
rational component is removed modulo squares.
-/
theorem dplusSquareAbscissa_quarticNorm_isSquare
    (P : DPlusAffinePoint)
    (hsquare : P.HasSquareAbscissa)
    (ha : P.a ≠ 0) :
    IsSquare
      (Algebra.norm ℚ (dplusPointKummerValue P).2) := by
  rcases hsquare with ⟨u, hu⟩
  have hu0 : u ≠ 0 := by
    intro hzero
    apply ha
    simp [hu, hzero]
  rw [show
      Algebra.norm ℚ (dplusPointKummerValue P).2 =
        P.a ^ 4 - 2 * P.a + 5 / 4 by
      exact dplusQuarticNorm_sub_root_half P.a]
  refine ⟨P.R / (2 * u), ?_⟩
  have hcurve := P.onCurve
  rw [hu] at hcurve
  simp [dplusRhs] at hcurve
  rw [hu]
  field_simp [hu0]
  nlinarith [hcurve]

/-! ## Exact named values from the descent artifact -/

/-- The identity representative in the product algebra. -/
def dplusIdentityKummerValue : DPlusEtaleAlgebra :=
  (1, 1)

/-- The `D=[(1,1)-∞]` representative `(1,1-z/2)`. -/
def dplusGeneratorKummerValue : DPlusEtaleAlgebra :=
  (1,
    1 - algebraMap ℚ DPlusQuarticAlgebra (1 / 2 : ℚ) *
      dplusQuarticRoot)

/-- The nonzero Weierstrass representative `(5,-z/2)` for `T`. -/
def dplusTorsionKummerValue : DPlusEtaleAlgebra :=
  (5,
    -algebraMap ℚ DPlusQuarticAlgebra (1 / 2 : ℚ) *
      dplusQuarticRoot)

/-- The fourth named value is the product of the `D` and `T` values. -/
def dplusGeneratorPlusTorsionKummerValue : DPlusEtaleAlgebra :=
  dplusGeneratorKummerValue * dplusTorsionKummerValue

@[simp] theorem dplusPointKummerValue_onePlus :
    dplusPointKummerValue dplusOnePlus =
      dplusGeneratorKummerValue := by
  rfl

/-- The generator value has square total norm `1/4`. -/
theorem dplusGeneratorKummerValue_norm :
    dplusEtaleNorm dplusGeneratorKummerValue = (1 / 2 : ℚ) ^ 2 := by
  rw [← dplusPointKummerValue_onePlus]
  simpa [dplusOnePlus] using dplusPointKummerValue_norm dplusOnePlus

/-- The corrected Weierstrass value has square total norm `25/4`. -/
theorem dplusTorsionKummerValue_norm :
    dplusEtaleNorm dplusTorsionKummerValue = (5 / 2 : ℚ) ^ 2 := by
  have hquartic := dplusQuarticNorm_sub_root_half 0
  change
    5 *
        Algebra.norm ℚ
          (-algebraMap ℚ DPlusQuarticAlgebra (1 / 2 : ℚ) *
            dplusQuarticRoot) =
      (5 / 2 : ℚ) ^ 2
  norm_num at hquartic ⊢
  rw [hquartic]
  norm_num

/-- The `D+T` value also has square total norm. -/
theorem dplusGeneratorPlusTorsionKummerValue_norm_isSquare :
    IsSquare
      (dplusEtaleNorm dplusGeneratorPlusTorsionKummerValue) := by
  rw [dplusGeneratorPlusTorsionKummerValue, dplusEtaleNorm_mul,
    dplusGeneratorKummerValue_norm, dplusTorsionKummerValue_norm]
  refine ⟨(5 / 4 : ℚ), ?_⟩
  ring

end

end Cuboid2
