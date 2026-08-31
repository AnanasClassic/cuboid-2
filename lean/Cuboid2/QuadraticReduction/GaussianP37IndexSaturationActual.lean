import Cuboid2.QuadraticReduction.GaussianFormalKernelTorsion
import Cuboid2.QuadraticReduction.GaussianLocalMapInjective
import Cuboid2.QuadraticReduction.GaussianP37ActualTrace
import Cuboid2.QuadraticReduction.GaussianSaturationBridge
import Cuboid2.QuadraticReduction.GaussianSplit37ReductionActual

/-!
# Actual 37-saturation of the visible point

If the visible point were divisible by `37`, then its twelfth multiple would
be the `37`-multiple of a point in the actual infinity kernel.  Formal
multiplication would therefore make its parameter norm strictly smaller
than `37⁻¹`.  The closed actual trace instead gives
`t(12P) = 37 · q` with unit residue `q ≡ 17`, a contradiction.
-/

namespace Cuboid2
namespace GaussianP37IndexSaturationActual

noncomputable section

open GaussianFiniteExponent
open GaussianFinite
open GaussianFormalKernelDisk
open GaussianFormalKernelTorsion
open GaussianIndexIndependent
open GaussianLocalMapInjective
open GaussianP37
open GaussianP37ActualTrace
open GaussianProjectiveReduction
open GaussianProjectiveReductionHom
open GaussianSaturationBridge
open GaussianSplit37ReductionActual

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have hxnonneg : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : DecidableEq ℚ_[37] := Classical.decEq _

/-- The actual visible point has no `37`-division preimage. -/
theorem visiblePoint_not_thirtySeven_divisible :
    ¬ ∃ Q : E0Point, 37 • Q = visiblePoint := by
  rintro ⟨Q, hQ⟩
  let V :
      (localPadicCurve
        GaussianProjectiveReduction.plusA
        GaussianProjectiveReduction.plusB).toAffine.Point :=
    mapE0PointPlusLocal (12 • Q)
  have hred :
      reduceE0Plus (12 • Q) = none := by
    calc
      reduceE0Plus (12 • Q) =
          finiteMul 37 plusCoefficients.1 plusCoefficients.2
            (reduceE0Plus Q) 12 :=
        map_nsmul_finite
          37 plusCoefficients.1 plusCoefficients.2
          reduceE0Plus reduceE0Plus_zero reduceE0Plus_add Q 12
      _ = none :=
        plus_twelve_eq_none_of_mem
          (reduceE0Plus_mem_finitePoints Q)
  have hVmem :
      V ∈ infinityKernel
        GaussianProjectiveReduction.plusA
        GaussianProjectiveReduction.plusB := by
    change
      finiteReducePoint
        GaussianProjectiveReduction.plusA
        GaussianProjectiveReduction.plusB
        (mapE0PointPlusLocal (12 • Q)) = none
    exact hred
  have hrelation :
      37 • V =
        12 • mapE0PointPlusLocal visiblePoint := by
    calc
      37 • V =
          mapE0PointPlusLocalHom (37 • (12 • Q)) := by
            rw [map_nsmul]
            rfl
      _ = mapE0PointPlusLocalHom (12 • (37 • Q)) := by
            rw [nsmul_left_comm]
      _ = mapE0PointPlusLocalHom (12 • visiblePoint) := by
            rw [hQ]
      _ = 12 • mapE0PointPlusLocal visiblePoint := by
            rw [map_nsmul]
            rfl
  obtain ⟨h12, t, q, htrace, ht, _htCertificate, htq, hq⟩ :=
    plus_actual_formal_parameter_first_layer
  have hrelationTrace :
      37 • V =
        .some
          (weightedX
            (weightedP12
              GaussianProjectiveReduction.plusA
              GaussianProjectiveReduction.plusB))
          (weightedY
            (weightedP12
              GaussianProjectiveReduction.plusA
              GaussianProjectiveReduction.plusB))
          h12 := by
    exact hrelation.trans htrace
  have hparameter :
      parameter
          GaussianProjectiveReduction.plusA
          GaussianProjectiveReduction.plusB
          (37 • V) =
        (t : ℚ_[37]) := by
    rw [hrelationTrace, parameter_some]
    exact ht.symm
  have hqNorm : ‖(q : ℚ_[37])‖ = 1 := by
    apply norm_coe_eq_one_of_toZMod_ne_zero
    rw [hq]
    native_decide
  have htNorm : ‖(t : ℚ_[37])‖ = (37 : ℝ)⁻¹ := by
    have htCoe :
        (t : ℚ_[37]) = (37 : ℚ_[37]) * (q : ℚ_[37]) := by
      have h37 :
          (((37 : ℕ) : ℤ_[37]) : ℚ_[37]) = (37 : ℚ_[37]) :=
        PadicInt.coe_natCast 37
      calc
        (t : ℚ_[37]) = ((37 * q : ℤ_[37]) : ℚ_[37]) :=
          congrArg ((↑) : ℤ_[37] → ℚ_[37]) htq
        _ = ((37 : ℤ_[37]) : ℚ_[37]) * (q : ℚ_[37]) :=
          PadicInt.coe_mul _ _
        _ = (37 : ℚ_[37]) * (q : ℚ_[37]) := by
          exact congrArg (fun z : ℚ_[37] => z * (q : ℚ_[37])) h37
    rw [htCoe, norm_mul, hqNorm, mul_one]
    simpa using (Padic.norm_p (p := 37))
  have hscale :=
    norm_parameter_37_nsmul_eq
      GaussianProjectiveReduction.plusA
      GaussianProjectiveReduction.plusB V hVmem
  have hsmall :=
    norm_parameter_lt_one_of_mem_kernel_point
      GaussianProjectiveReduction.plusA
      GaussianProjectiveReduction.plusB V hVmem
  rw [hparameter, htNorm] at hscale
  have hinvPos : 0 < (37 : ℝ)⁻¹ := by positivity
  nlinarith

/-- In every exact rank-one normal form, the free coefficient of the
visible point is not divisible by `37`. -/
theorem thirtySeven_not_dvd_visiblePoint_coefficient
    (e : E0Point ≃+ ℤ × ZMod 2)
    {m : ℤ} {δ : ℕ}
    (hP :
      visiblePoint = m • freeGenerator e + δ • twoTorsionPoint) :
    ¬ (37 : ℤ) ∣ m := by
  intro hdiv
  apply visiblePoint_not_thirtySeven_divisible
  exact
    visiblePoint_divisible_of_odd_dvd_coefficient
      e hP (by norm_num) hdiv

end

end GaussianP37IndexSaturationActual
end Cuboid2
