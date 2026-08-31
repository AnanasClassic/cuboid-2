import Cuboid2.QuadraticReduction.GaussianPrimes
import Cuboid2.QuadraticReduction.GaussianFinite
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.NumDen

/-!
# From Gaussian descent classes to finite homogeneous-space obstructions

This file connects the genuine squareclass map on an actual affine point to
the homogeneous space used by the closed finite obstruction certificates.
The construction first produces a field-valued witness, then clears a reduced
Gaussian denominator and uses integral closedness of `GaussianInt` to recover
an integral square root.
-/

namespace Cuboid2

noncomputable section

open scoped QuadraticAlgebra

namespace GaussianObstructionBridge

open GaussianDescent GaussianPrimes

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

private theorem algebraMap_gaussianInt_ne_zero {z : GaussianInt}
    (hz : z ≠ 0) :
    algebraMap GaussianInt GaussianRat z ≠ 0 := by
  intro h
  apply hz
  apply FaithfulSMul.algebraMap_injective GaussianInt GaussianRat
  simpa only [map_zero] using h

private theorem gaussianLambdaInt_not_isUnit :
    ¬ IsUnit gaussianLambdaInt := by
  rw [Zsqrtd.isUnit_iff_norm_isUnit]
  rw [Int.isUnit_iff_natAbs_eq]
  norm_num [gaussianLambdaInt, Zsqrtd.norm]

/-- Divisibility by `1+i` is exactly parity of the sum of the two Gaussian
coordinates. -/
theorem gaussianLambdaInt_dvd_iff_even (z : GaussianInt) :
    gaussianLambdaInt ∣ z ↔ Even (z.re + z.im) := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨w.re, ?_⟩
    simp only [gaussianLambdaInt, Zsqrtd.re_mul, Zsqrtd.im_mul]
    ring
  · rintro ⟨k, hk⟩
    refine ⟨⟨k, z.im - k⟩, ?_⟩
    apply Zsqrtd.ext <;>
      simp only [gaussianLambdaInt, Zsqrtd.re_mul, Zsqrtd.im_mul]
    · omega
    · ring

/-- Coprime Gaussian numerator and denominator are `lambda`-primitive: the
ramified nonunit `1+i` cannot divide both. -/
theorem not_both_gaussianLambdaInt_dvd_of_isRelPrime
    {U V : GaussianInt} (hUV : IsRelPrime U V) :
    ¬ (gaussianLambdaInt ∣ U ∧ gaussianLambdaInt ∣ V) := by
  rintro ⟨hU, hV⟩
  exact gaussianLambdaInt_not_isUnit
    ((hUV.of_dvd_left hU).isUnit_of_dvd hV)

/-- Canonical real and imaginary representatives of a Gaussian integer
modulo a nonzero natural modulus. -/
def gaussianResidue (n : ℕ) [NeZero n] (z : GaussianInt) :
    GaussianFinite.GaussResidue :=
  ((z.re : ZMod n).val, (z.im : ZMod n).val)

/-- Every canonical reduction is one of the residues enumerated by the finite
checker. -/
theorem gaussianResidue_mem (n : ℕ) [NeZero n] (z : GaussianInt) :
    gaussianResidue n z ∈ GaussianFinite.gaussResidues n := by
  simp [gaussianResidue, GaussianFinite.gaussResidues, ZMod.val_lt]

/-- For an even modulus, reduction preserves the parity detected by
divisibility by `1+i`. -/
theorem even_gaussianResidue_coordSum_iff
    (n : ℕ) [NeZero n] (hn : Even n) (z : GaussianInt) :
    Even ((gaussianResidue n z).1 + (gaussianResidue n z).2) ↔
      Even (z.re + z.im) := by
  let f : ZMod n →+* ZMod 2 :=
    ZMod.castHom (even_iff_two_dvd.mp hn) (ZMod 2)
  have hre :
      ((gaussianResidue n z).1 : ZMod 2) = (z.re : ZMod 2) := by
    calc
      ((gaussianResidue n z).1 : ZMod 2) =
          f ((gaussianResidue n z).1 : ZMod n) := by
            simp [f]
      _ = f (z.re : ZMod n) := by
        rw [gaussianResidue, ZMod.natCast_zmod_val]
      _ = (z.re : ZMod 2) := by simp [f]
  have him :
      ((gaussianResidue n z).2 : ZMod 2) = (z.im : ZMod 2) := by
    calc
      ((gaussianResidue n z).2 : ZMod 2) =
          f ((gaussianResidue n z).2 : ZMod n) := by
            simp [f]
      _ = f (z.im : ZMod n) := by
        rw [gaussianResidue, ZMod.natCast_zmod_val]
      _ = (z.im : ZMod 2) := by simp [f]
  rw [← ZMod.natCast_eq_zero_iff_even,
    ← ZMod.intCast_eq_zero_iff_even]
  push_cast
  rw [hre, him]

/-- For an even modulus, coprimality of the original Gaussian numerator and
denominator makes their canonical residues pass the finite
`lambdaPrimitive` test. -/
theorem lambdaPrimitive_gaussianResidue
    (n : ℕ) [NeZero n] (hn : Even n) {U V : GaussianInt}
    (hUV : IsRelPrime U V) :
    GaussianFinite.lambdaPrimitive
        (gaussianResidue n U) (gaussianResidue n V) = true := by
  apply Bool.eq_true_of_not_eq_false
  intro hfalse
  rw [GaussianFinite.lambdaPrimitive,
    Bool.not_eq_false_eq_eq_true] at hfalse
  rcases Bool.and_eq_true_iff.mp hfalse with ⟨hU, hV⟩
  have hUeven :
      Even ((gaussianResidue n U).1 + (gaussianResidue n U).2) := by
    apply Nat.even_iff.mpr
    simpa only [beq_iff_eq] using hU
  have hVeven :
      Even ((gaussianResidue n V).1 + (gaussianResidue n V).2) := by
    apply Nat.even_iff.mpr
    simpa only [beq_iff_eq] using hV
  apply not_both_gaussianLambdaInt_dvd_of_isRelPrime hUV
  constructor
  · exact (gaussianLambdaInt_dvd_iff_even U).mpr
      ((even_gaussianResidue_coordSum_iff n hn U).mp hUeven)
  · exact (gaussianLambdaInt_dvd_iff_even V).mpr
      ((even_gaussianResidue_coordSum_iff n hn V).mp hVeven)

/-- Canonical Gaussian reduction respects addition. -/
theorem gaussianResidue_add (n : ℕ) [NeZero n] (z w : GaussianInt) :
    gaussianResidue n (z + w) =
      GaussianFinite.gaussAdd n (gaussianResidue n z) (gaussianResidue n w) := by
  apply Prod.ext <;>
    simp [gaussianResidue, GaussianFinite.gaussAdd, ZMod.val_add]

/-- Canonical Gaussian reduction respects multiplication. -/
theorem gaussianResidue_mul (n : ℕ) [NeZero n] (z w : GaussianInt) :
    gaussianResidue n (z * w) =
      GaussianFinite.gaussMul n (gaussianResidue n z) (gaussianResidue n w) := by
  apply Prod.ext
  · simp only [gaussianResidue, GaussianFinite.gaussMul,
      GaussianFinite.residueSub, Zsqrtd.re_mul]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_neg, neg_one_mul]
    rw [neg_mul]
    change
      ((z.re : ZMod n) * (w.re : ZMod n) +
          -((z.im : ZMod n) * (w.im : ZMod n))).val =
        ((z.re : ZMod n).val * (w.re : ZMod n).val % n +
            (n -
              (z.im : ZMod n).val * (w.im : ZMod n).val % n)) % n
    rw [ZMod.val_add, ZMod.neg_val',
      ZMod.val_mul, ZMod.val_mul]
    simp only [Nat.add_mod_mod]
  · simp [gaussianResidue, GaussianFinite.gaussMul, Zsqrtd.im_mul,
      ZMod.val_add, ZMod.val_mul, Nat.add_mod]

/-- Canonical Gaussian reduction takes a square to the finite squaring
operation. -/
theorem gaussianResidue_sq (n : ℕ) [NeZero n] (z : GaussianInt) :
    gaussianResidue n (z ^ 2) =
      GaussianFinite.gaussSq n (gaussianResidue n z) := by
  rw [pow_two, gaussianResidue_mul]
  rfl

/-- Canonical Gaussian reduction takes a fourth power to the finite fourth
power operation. -/
theorem gaussianResidue_fourth (n : ℕ) [NeZero n] (z : GaussianInt) :
    gaussianResidue n (z ^ 4) =
      GaussianFinite.gaussFourth n (gaussianResidue n z) := by
  calc
    gaussianResidue n (z ^ 4) =
        gaussianResidue n ((z ^ 2) ^ 2) := by
          congr 1
          ring
    _ = GaussianFinite.gaussSq n (gaussianResidue n (z ^ 2)) :=
      gaussianResidue_sq n (z ^ 2)
    _ = GaussianFinite.gaussFourth n (gaussianResidue n z) := by
      rw [gaussianResidue_sq]
      rfl

/-- Reduction of an integral homogeneous-space right side is exactly the
right side evaluated by the finite checker. -/
theorem gaussianResidue_homogeneousSpaceRhs
    (n : ℕ) [NeZero n] (a d e U V : GaussianInt) :
    gaussianResidue n
        (d * U ^ 4 + a * U ^ 2 * V ^ 2 + e * V ^ 4) =
      GaussianFinite.homogeneousSpaceRhs n
        (gaussianResidue n a) (gaussianResidue n d)
        (gaussianResidue n e) (gaussianResidue n U)
        (gaussianResidue n V) := by
  have hassoc :
      d * U ^ 4 + a * U ^ 2 * V ^ 2 + e * V ^ 4 =
        d * U ^ 4 + a * (U ^ 2 * V ^ 2) + e * V ^ 4 := by
    ring
  rw [hassoc]
  simp only [gaussianResidue_add, gaussianResidue_mul,
    gaussianResidue_sq, gaussianResidue_fourth]
  rfl

/-- Any coprime integral homogeneous-space solution survives reduction at an
even modulus and is therefore found by the exhaustive finite checker. -/
theorem hasPrimitiveHomogeneousSpaceSolution_of_integral
    (n : ℕ) [NeZero n] (hn : Even n)
    (a d e U V W : GaussianInt)
    (hUV : IsRelPrime U V)
    (hEq :
      W ^ 2 =
        d * U ^ 4 + a * U ^ 2 * V ^ 2 + e * V ^ 4) :
    GaussianFinite.hasPrimitiveHomogeneousSpaceSolution n
        (gaussianResidue n a) (gaussianResidue n d)
        (gaussianResidue n e) = true := by
  let rU := gaussianResidue n U
  let rV := gaussianResidue n V
  let rW := gaussianResidue n W
  have hred :
      GaussianFinite.gaussSq n rW =
        GaussianFinite.homogeneousSpaceRhs n
          (gaussianResidue n a) (gaussianResidue n d)
          (gaussianResidue n e) rU rV := by
    calc
      GaussianFinite.gaussSq n rW =
          gaussianResidue n (W ^ 2) := by
            exact (gaussianResidue_sq n W).symm
      _ =
          gaussianResidue n
            (d * U ^ 4 + a * U ^ 2 * V ^ 2 + e * V ^ 4) := by
              rw [hEq]
      _ =
          GaussianFinite.homogeneousSpaceRhs n
            (gaussianResidue n a) (gaussianResidue n d)
            (gaussianResidue n e) rU rV := by
              exact gaussianResidue_homogeneousSpaceRhs n a d e U V
  have hrW : rW ∈ GaussianFinite.gaussResidues n :=
    gaussianResidue_mem n W
  have hsquare :
      GaussianFinite.gaussSq n rW ∈
        GaussianFinite.gaussSquareResidues n := by
    rw [GaussianFinite.gaussSquareResidues, List.mem_eraseDups]
    apply List.mem_map.mpr
    exact ⟨rW, hrW, rfl⟩
  have hrhs :
      GaussianFinite.homogeneousSpaceRhs n
          (gaussianResidue n a) (gaussianResidue n d)
          (gaussianResidue n e) rU rV ∈
        GaussianFinite.gaussSquareResidues n := by
    rw [← hred]
    exact hsquare
  rw [GaussianFinite.hasPrimitiveHomogeneousSpaceSolution]
  apply List.any_eq_true.mpr
  refine ⟨rU, gaussianResidue_mem n U, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨rV, gaussianResidue_mem n V, ?_⟩
  apply Bool.and_eq_true_iff.mpr
  constructor
  · exact lambdaPrimitive_gaussianResidue n hn hUV
  · exact List.contains_iff_mem.mpr hrhs

/-- A nonzero affine point whose `x`-coordinate has squareclass `d` produces
the usual field-valued two-descent homogeneous-space witness. -/
theorem fieldHomogeneousSpace_of_squareClass
    {A B d x y : GaussianRat}
    (hd : d ≠ 0) (hx : x ≠ 0)
    (hxy : (curve A B).toAffine.Equation x y)
    (hclass : squareClassOf x hx = squareClassOf d hd) :
    ∃ z : GaussianRat, z ≠ 0 ∧ x = d * z ^ 2 ∧
      let N := y / (d * z)
      N ^ 2 = d * z ^ 4 + A * z ^ 2 + B / d := by
  rcases (squareClassOf_eq_iff hx hd).mp hclass with ⟨z, hz, hxz⟩
  refine ⟨z, hz, hxz, ?_⟩
  dsimp only
  have hcurve :
      y ^ 2 = x * (x ^ 2 + A * x + B) :=
    curve_equation_iff.mp hxy
  rw [hxz] at hcurve
  field_simp [hd, hz]
  linear_combination hcurve

/-- After writing the squareclass parameter in lowest Gaussian terms, the
field-valued homogeneous-space square root is integral.  The output retains
coprimality of `U,V`, which is the input needed to prove local primitivity. -/
theorem integralHomogeneousSpace_of_squareClass
    (a b d e : GaussianInt) (hd : d ≠ 0) (hbe : b = d * e)
    {x y : GaussianRat}
    (hx : x ≠ 0)
    (hxy :
      (curve (algebraMap GaussianInt GaussianRat a)
        (algebraMap GaussianInt GaussianRat b)).toAffine.Equation x y)
    (hclass :
      squareClassOf x hx =
        squareClassOf (algebraMap GaussianInt GaussianRat d)
          (algebraMap_gaussianInt_ne_zero hd)) :
    ∃ U V W : GaussianInt,
      V ≠ 0 ∧ IsRelPrime U V ∧
        W ^ 2 =
          d * U ^ 4 + a * U ^ 2 * V ^ 2 + e * V ^ 4 := by
  let dK : GaussianRat := algebraMap GaussianInt GaussianRat d
  have hdK : dK ≠ 0 := algebraMap_gaussianInt_ne_zero hd
  rcases fieldHomogeneousSpace_of_squareClass hdK hx hxy hclass with
    ⟨z, hz, hxz, hN⟩
  let U : GaussianInt := IsFractionRing.num GaussianInt z
  let V : GaussianInt := IsFractionRing.den GaussianInt z
  have hV : V ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp
      (IsFractionRing.den GaussianInt z).2
  have hVK :
      algebraMap GaussianInt GaussianRat V ≠ 0 :=
    algebraMap_gaussianInt_ne_zero hV
  have hzfrac :
      z =
        algebraMap GaussianInt GaussianRat U /
          algebraMap GaussianInt GaussianRat V := by
    exact (IsFractionRing.mk'_num_den' GaussianInt z).symm
  have hrel : IsRelPrime U V :=
    IsFractionRing.num_den_reduced GaussianInt z
  let N : GaussianRat := y / (dK * z)
  let M : GaussianRat :=
    N * algebraMap GaussianInt GaussianRat V ^ 2
  let rhs : GaussianInt :=
    d * U ^ 4 + a * U ^ 2 * V ^ 2 + e * V ^ 4
  have hN' :
      N ^ 2 =
        dK * z ^ 4 +
          algebraMap GaussianInt GaussianRat a * z ^ 2 +
          algebraMap GaussianInt GaussianRat b / dK := by
    simpa only [N] using hN
  have hM :
      M ^ 2 = algebraMap GaussianInt GaussianRat rhs := by
    calc
      M ^ 2 =
          N ^ 2 * algebraMap GaussianInt GaussianRat V ^ 4 := by
        dsimp only [M]
        ring
      _ =
          (dK * z ^ 4 +
              algebraMap GaussianInt GaussianRat a * z ^ 2 +
              algebraMap GaussianInt GaussianRat b / dK) *
            algebraMap GaussianInt GaussianRat V ^ 4 := by
        rw [hN']
      _ = algebraMap GaussianInt GaussianRat rhs := by
        dsimp only [rhs, dK]
        simp only [map_add, map_mul, map_pow]
        rw [hzfrac, hbe]
        simp only [map_mul]
        field_simp [hVK, algebraMap_gaussianInt_ne_zero hd]
        have hcancel :
            algebraMap GaussianInt GaussianRat d *
                  algebraMap GaussianInt GaussianRat V ^ 4 *
                  algebraMap GaussianInt GaussianRat e *
                  (algebraMap GaussianInt GaussianRat d)⁻¹ =
                algebraMap GaussianInt GaussianRat V ^ 4 *
                  algebraMap GaussianInt GaussianRat e := by
          calc
            _ =
                (algebraMap GaussianInt GaussianRat V ^ 4 *
                    algebraMap GaussianInt GaussianRat e) *
                  (algebraMap GaussianInt GaussianRat d *
                    (algebraMap GaussianInt GaussianRat d)⁻¹) := by
              ring
            _ = _ := by
              rw [mul_inv_cancel₀ (algebraMap_gaussianInt_ne_zero hd)]
              simp
        have hcancelDiv :
            algebraMap GaussianInt GaussianRat d *
                  algebraMap GaussianInt GaussianRat V ^ 4 *
                  algebraMap GaussianInt GaussianRat e /
                  algebraMap GaussianInt GaussianRat d =
                algebraMap GaussianInt GaussianRat V ^ 4 *
                  algebraMap GaussianInt GaussianRat e := by
          rw [div_eq_mul_inv]
          exact hcancel
        rw [hcancelDiv]
  have hMint : IsIntegral GaussianInt (M ^ 2) := by
    rw [hM]
    exact isIntegral_algebraMap
  rcases
      IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
        (R := GaussianInt) (K := GaussianRat)
        (x := M) (n := 2) (by norm_num) hMint with
    ⟨W, hW⟩
  refine ⟨U, V, W, hV, hrel, ?_⟩
  apply FaithfulSMul.algebraMap_injective GaussianInt GaussianRat
  rw [map_pow]
  rw [hW, hM]

/-- A closed negative finite row excludes the corresponding squareclass on
every nonzero affine solution of the original Gaussian curve equation.  The
finite row is the only certificate argument; denominator clearing,
primitivity, and reduction are all proved above. -/
theorem squareClass_ne_of_localObstruction
    (n : ℕ) [NeZero n] (hn : Even n)
    (a b d e : GaussianInt) (hd : d ≠ 0) (hbe : b = d * e)
    {x y : GaussianRat}
    (hx : x ≠ 0)
    (hxy :
      (curve (algebraMap GaussianInt GaussianRat a)
        (algebraMap GaussianInt GaussianRat b)).toAffine.Equation x y)
    (hobs :
      GaussianFinite.hasPrimitiveHomogeneousSpaceSolution n
        (gaussianResidue n a) (gaussianResidue n d)
        (gaussianResidue n e) = false) :
    squareClassOf x hx ≠
      squareClassOf (algebraMap GaussianInt GaussianRat d)
        (algebraMap_gaussianInt_ne_zero hd) := by
  intro hclass
  rcases
      integralHomogeneousSpace_of_squareClass
        a b d e hd hbe hx hxy hclass with
    ⟨U, V, W, _, hUV, hEq⟩
  have htrue :=
    hasPrimitiveHomogeneousSpaceSolution_of_integral
      n hn a d e U V W hUV hEq
  rw [hobs] at htrue
  contradiction

/-- Point-level form of `squareClass_ne_of_localObstruction`: a genuine
nonsingular affine point supplies the curve equation used by the bridge. -/
theorem squareClass_ne_of_localObstruction_of_affinePoint
    (n : ℕ) [NeZero n] (hn : Even n)
    (a b d e : GaussianInt) (hd : d ≠ 0) (hbe : b = d * e)
    {x y : GaussianRat}
    (hx : x ≠ 0)
    (hpoint :
      (curve (algebraMap GaussianInt GaussianRat a)
        (algebraMap GaussianInt GaussianRat b)).toAffine.Nonsingular x y)
    (hobs :
      GaussianFinite.hasPrimitiveHomogeneousSpaceSolution n
        (gaussianResidue n a) (gaussianResidue n d)
        (gaussianResidue n e) = false) :
    squareClassOf x hx ≠
      squareClassOf (algebraMap GaussianInt GaussianRat d)
        (algebraMap_gaussianInt_ne_zero hd) :=
  squareClass_ne_of_localObstruction
    n hn a b d e hd hbe hx hpoint.left hobs

end GaussianObstructionBridge

end

end Cuboid2
