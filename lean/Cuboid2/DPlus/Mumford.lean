import Cuboid2.DPlus.Basic
import Cuboid2.Genus2.Mumford

/-!
# Explicit Mumford classes on `D+`

The rank and saturation certificates in `clean3` use

* `D = [(1,1)-∞]`, and
* `T = [(0,0)-∞]`.

This file fixes their exact Lean representatives and checks the curve
relations directly.
-/

namespace Cuboid2

open Polynomial

noncomputable section

/-- Polynomial model of `D+ : R² = 4a⁵ - 8a² + 5a`. -/
def dplusPolynomial : ℚ[X] :=
  C 4 * X ^ 5 - C 8 * X ^ 2 + C 5 * X

@[simp] theorem eval_dplusPolynomial (a : ℚ) :
    eval a dplusPolynomial = dplusRhs a := by
  simp [dplusPolynomial, dplusRhs]
  ring

/-- The rank-one class `D=[(1,1)-∞]`. -/
def dplusGeneratorD : MumfordPair ℚ :=
  MumfordPair.ofPoint 1 1

/-- The rational two-torsion candidate `T=[(0,0)-∞]`. -/
def dplusTorsionT : MumfordPair ℚ :=
  MumfordPair.ofPoint 0 0

@[simp] theorem dplusGeneratorD_u : dplusGeneratorD.u = X - 1 := by
  simp [dplusGeneratorD, MumfordPair.ofPoint]

@[simp] theorem dplusGeneratorD_v : dplusGeneratorD.v = 1 := by
  simp [dplusGeneratorD, MumfordPair.ofPoint]

@[simp] theorem dplusTorsionT_u : dplusTorsionT.u = X := by
  simp [dplusTorsionT, MumfordPair.ofPoint]

@[simp] theorem dplusTorsionT_v : dplusTorsionT.v = 0 := by
  simp [dplusTorsionT, MumfordPair.ofPoint]

/-- The class `D` satisfies the exact Mumford divisibility condition. -/
theorem dplusGeneratorD_valid :
    dplusGeneratorD.ValidOn dplusPolynomial := by
  apply MumfordPair.ofPoint_validOn
  norm_num [eval_dplusPolynomial, dplusRhs]

/-- The class `T` satisfies the exact Mumford divisibility condition. -/
theorem dplusTorsionT_valid :
    dplusTorsionT.ValidOn dplusPolynomial := by
  apply MumfordPair.ofPoint_validOn
  norm_num [eval_dplusPolynomial, dplusRhs]

/-- Hyperelliptic negation sends `D` to the class represented by `(1,-1)`. -/
theorem dplusGeneratorD_neg :
    dplusGeneratorD.neg = MumfordPair.ofPoint 1 (-1 : ℚ) := by
  ext <;> simp [dplusGeneratorD, MumfordPair.neg, MumfordPair.ofPoint]

/-- The Weierstrass class `T` is fixed by hyperelliptic negation. -/
theorem dplusTorsionT_neg : dplusTorsionT.neg = dplusTorsionT := by
  ext <;> simp [dplusTorsionT, MumfordPair.neg, MumfordPair.ofPoint]

end

end Cuboid2
