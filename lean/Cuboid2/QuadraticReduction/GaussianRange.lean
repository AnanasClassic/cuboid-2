import Cuboid2.QuadraticReduction.GaussianPrimes
import Cuboid2.QuadraticReduction.GaussianSupport
import Cuboid2.QuadraticReduction.GaussianUFD

/-!
# Global support of the four Gaussian Kummer images

This module combines the genuine prime valuations on `ℚ(i)` with unique
factorization in `ℤ[i]`.  Its first endpoint gives the exact squarefree
support statement before the separate `lambda`-local obstruction is applied.
-/

namespace Cuboid2

noncomputable section

namespace GaussianRange

open GaussianDescent GaussianFraction GaussianPrimes GaussianSupport

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

private theorem algebraMap_gaussianInt_ne_zero
    {r : GaussianInt} (hr : r ≠ 0) :
    algebraMap GaussianInt GaussianRat r ≠ 0 := by
  intro h
  apply hr
  apply FaithfulSMul.algebraMap_injective GaussianInt GaussianRat
  simpa only [map_zero] using h

/-- Multiplying an integral representative by another representative and
obtaining a unit-base times a square gives the expected field squareclass. -/
private theorem squareClassOf_algebraMap_eq_of_mul_eq
    {r d g z s : GaussianInt}
    (hr : r ≠ 0) (hd : d ≠ 0) (hg : g ≠ 0)
    (hz : z ≠ 0) (hs : s ≠ 0)
    (h : r * d = g * z ^ 2 * s ^ 2) :
    squareClassOf (algebraMap GaussianInt GaussianRat r)
        (algebraMap_gaussianInt_ne_zero hr) =
      squareClassOf (algebraMap GaussianInt GaussianRat (g * d))
        (algebraMap_gaussianInt_ne_zero (mul_ne_zero hg hd)) := by
  let dK : GaussianRat := algebraMap GaussianInt GaussianRat d
  have hdK : dK ≠ 0 := algebraMap_gaussianInt_ne_zero hd
  apply (squareClassOf_eq_iff
    (algebraMap_gaussianInt_ne_zero hr)
    (algebraMap_gaussianInt_ne_zero (mul_ne_zero hg hd))).mpr
  refine ⟨algebraMap GaussianInt GaussianRat (z * s) / dK,
    div_ne_zero (algebraMap_gaussianInt_ne_zero (mul_ne_zero hz hs)) hdK,
    ?_⟩
  have hK := congrArg (algebraMap GaussianInt GaussianRat) h
  simp only [map_mul, map_pow] at hK
  calc
    algebraMap GaussianInt GaussianRat r =
        (algebraMap GaussianInt GaussianRat g *
            algebraMap GaussianInt GaussianRat z ^ 2 *
            algebraMap GaussianInt GaussianRat s ^ 2) / dK :=
      (eq_div_iff hdK).2 hK
    _ = algebraMap GaussianInt GaussianRat (g * d) *
        (algebraMap GaussianInt GaussianRat (z * s) / dK) ^ 2 := by
      simp only [map_mul]
      field_simp [hdK]
      ring

/-- Every prime divisor of a unit times powers of two fixed primes is
associated to one of those primes. -/
theorem prime_dvd_unit_mul_two_prime_powers
    {q u L P : GaussianInt} {m n : ℕ}
    (hq : Prime q) (hu : IsUnit u)
    (hL : Prime L) (hP : Prime P)
    (hdiv : q ∣ u * L ^ m * P ^ n) :
    Associated q L ∨ Associated q P := by
  rcases hq.dvd_mul.mp hdiv with hqUL | hqPn
  · rcases hq.dvd_mul.mp hqUL with hqu | hqLm
    · exact (hq.irreducible.not_dvd_isUnit hu hqu).elim
    · exact Or.inl
        (hq.associated_of_dvd hL (hq.dvd_of_dvd_pow hqLm))
  · exact Or.inr
      (hq.associated_of_dvd hP (hq.dvd_of_dvd_pow hqPn))

/-- The global UFD support theorem for an actual nonzero affine abscissa.
The hypotheses on `B` only record its already checked integral
factorization. -/
theorem curve_abscissa_supported_on_two_primes
    {A B L P : GaussianInt}
    (hL : Prime L) (hP : Prime P) (hLP : ¬Associated L P)
    (hBsupport : ∀ q : GaussianInt, Prime q → q ∣ B →
      Associated q L ∨ Associated q P)
    {x y : GaussianRat} (hx : x ≠ 0)
    (hcurve :
      y ^ 2 =
        x * (x ^ 2 +
          algebraMap GaussianInt GaussianRat A * x +
          algebraMap GaussianInt GaussianRat B)) :
    ∃ eL eP : ℕ, eL ≤ 1 ∧ eP ≤ 1 ∧
      ∃ s : GaussianInt, ∃ u : GaussianIntˣ,
        (IsFractionRing.num GaussianInt x *
            (IsFractionRing.den GaussianInt x : GaussianInt)) *
              L ^ eL * P ^ eP =
          (u : GaussianInt) * s ^ 2 := by
  have hn : IsFractionRing.num GaussianInt x ≠ 0 :=
    (IsFractionRing.num_eq_zero x).not.mpr hx
  have hd :
      (IsFractionRing.den GaussianInt x : GaussianInt) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp
      (IsFractionRing.den GaussianInt x).property
  apply GaussianUFD.exists_unit_mul_square_of_even_multiplicity_off_two_primes
    (mul_ne_zero hn hd) hL hP hLP
  intro q hq hqL hqP
  apply curve_abscissa_num_mul_den_even hq
  · intro hqB
    rcases hBsupport q hq hqB with h | h
    · exact hqL h
    · exact hqP h
  · exact hx
  · exact hcurve

/-- Squareclass form of `curve_abscissa_supported_on_two_primes`.  The unit
part is reduced to the two representatives `1` and `i`; both distinguished
prime exponents are zero or one. -/
theorem curve_abscissa_squareClass_supported_on_two_primes
    {A B L P : GaussianInt}
    (hL : Prime L) (hP : Prime P) (hLP : ¬Associated L P)
    (hBsupport : ∀ q : GaussianInt, Prime q → q ∣ B →
      Associated q L ∨ Associated q P)
    {x y : GaussianRat} (hx : x ≠ 0)
    (hcurve :
      y ^ 2 =
        x * (x ^ 2 +
          algebraMap GaussianInt GaussianRat A * x +
          algebraMap GaussianInt GaussianRat B)) :
    ∃ eL eP : ℕ, eL ≤ 1 ∧ eP ≤ 1 ∧
      ∃ g : GaussianInt, ∃ hg : g ≠ 0,
        (g = 1 ∨ g = gaussianIInt) ∧
          squareClassOf x hx =
            squareClassOf
              (algebraMap GaussianInt GaussianRat
                (g * L ^ eL * P ^ eP))
              (algebraMap_gaussianInt_ne_zero
                (mul_ne_zero
                  (mul_ne_zero hg (pow_ne_zero eL hL.ne_zero))
                  (pow_ne_zero eP hP.ne_zero))) := by
  let r : GaussianInt :=
    IsFractionRing.num GaussianInt x *
      (IsFractionRing.den GaussianInt x : GaussianInt)
  have hr : r ≠ 0 := by
    apply mul_ne_zero
    · exact (IsFractionRing.num_eq_zero x).not.mpr hx
    · exact mem_nonZeroDivisors_iff_ne_zero.mp
        (IsFractionRing.den GaussianInt x).property
  obtain ⟨eL, eP, heL, heP, s, u, hcompletion⟩ :=
    curve_abscissa_supported_on_two_primes
      hL hP hLP hBsupport hx hcurve
  let d : GaussianInt := L ^ eL * P ^ eP
  have hd : d ≠ 0 :=
    mul_ne_zero (pow_ne_zero eL hL.ne_zero) (pow_ne_zero eP hP.ne_zero)
  have hs : s ≠ 0 := by
    intro hs0
    rw [hs0, zero_pow (by norm_num), mul_zero] at hcompletion
    exact mul_ne_zero (mul_ne_zero hr (pow_ne_zero eL hL.ne_zero))
      (pow_ne_zero eP hP.ne_zero) hcompletion
  obtain ⟨z, huz | huz⟩ := unit_eq_square_or_i_mul_square u
  · have hz : z ≠ 0 := by
      intro hz0
      rw [hz0, zero_pow (by norm_num)] at huz
      exact u.ne_zero huz
    refine ⟨eL, eP, heL, heP, 1, one_ne_zero, Or.inl rfl, ?_⟩
    rw [squareClassOf_eq_num_mul_den hx]
    have hEq : r * d = 1 * z ^ 2 * s ^ 2 := by
      dsimp only [r, d] at hcompletion ⊢
      rw [huz] at hcompletion
      simpa [mul_assoc] using hcompletion
    have hsc := squareClassOf_algebraMap_eq_of_mul_eq
      hr hd one_ne_zero hz hs hEq
    simpa only [r, d, mul_assoc] using hsc
  · have hz : z ≠ 0 := by
      intro hz0
      rw [hz0, zero_pow (by norm_num), mul_zero] at huz
      exact u.ne_zero huz
    have hI : gaussianIInt ≠ 0 := by
      intro h
      have := congrArg Zsqrtd.norm h
      norm_num at this
    refine ⟨eL, eP, heL, heP, gaussianIInt, hI, Or.inr rfl, ?_⟩
    rw [squareClassOf_eq_num_mul_den hx]
    have hEq : r * d = gaussianIInt * z ^ 2 * s ^ 2 := by
      dsimp only [r, d] at hcompletion ⊢
      rw [huz] at hcompletion
      simpa [mul_assoc] using hcompletion
    have hsc := squareClassOf_algebraMap_eq_of_mul_eq
      hr hd hI hz hs hEq
    simpa only [r, d, mul_assoc] using hsc

/-! ## The two eight-element raw support sets -/

/-- The squareclass of `lambda = 1+i`. -/
def classLambda : SquareClass :=
  squareClassOf
    (algebraMap GaussianInt GaussianRat gaussianLambdaInt)
    (algebraMap_gaussianInt_ne_zero gaussianLambdaInt_prime.ne_zero)

/-- The squareclass of `i*lambda`. -/
def classILambda : SquareClass :=
  squareClassOf
    (algebraMap GaussianInt GaussianRat
      (gaussianIInt * gaussianLambdaInt))
    (algebraMap_gaussianInt_ne_zero
      (mul_ne_zero
        (by
          intro h
          have := congrArg Zsqrtd.norm h
          norm_num at this)
        gaussianLambdaInt_prime.ne_zero))

/-- The squareclass of `lambda*pi`. -/
def classLambdaPi : SquareClass :=
  squareClassOf
    (algebraMap GaussianInt GaussianRat
      (gaussianLambdaInt * gaussianPiInt))
    (algebraMap_gaussianInt_ne_zero
      (mul_ne_zero gaussianLambdaInt_prime.ne_zero
        gaussianPiInt_prime.ne_zero))

/-- The squareclass of `i*lambda*pi`. -/
def classILambdaPi : SquareClass :=
  squareClassOf
    (algebraMap GaussianInt GaussianRat
      (gaussianIInt * gaussianLambdaInt * gaussianPiInt))
    (algebraMap_gaussianInt_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (by
            intro h
            have := congrArg Zsqrtd.norm h
            norm_num at this)
          gaussianLambdaInt_prime.ne_zero)
        gaussianPiInt_prime.ne_zero))

/-- The squareclass of `lambda*rho`. -/
def classLambdaRho : SquareClass :=
  squareClassOf
    (algebraMap GaussianInt GaussianRat
      (gaussianLambdaInt * gaussianRhoInt))
    (algebraMap_gaussianInt_ne_zero
      (mul_ne_zero gaussianLambdaInt_prime.ne_zero
        gaussianRhoInt_prime.ne_zero))

/-- The squareclass of `i*lambda*rho`. -/
def classILambdaRho : SquareClass :=
  squareClassOf
    (algebraMap GaussianInt GaussianRat
      (gaussianIInt * gaussianLambdaInt * gaussianRhoInt))
    (algebraMap_gaussianInt_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (by
            intro h
            have := congrArg Zsqrtd.norm h
            norm_num at this)
          gaussianLambdaInt_prime.ne_zero)
        gaussianRhoInt_prime.ne_zero))

/-- Raw support at `lambda` and `pi`, before the mod-4 lambda obstruction. -/
theorem curve_abscissa_pi_raw_cases
    {A B : GaussianInt}
    (hBsupport : ∀ q : GaussianInt, Prime q → q ∣ B →
      Associated q gaussianLambdaInt ∨ Associated q gaussianPiInt)
    {x y : GaussianRat} (hx : x ≠ 0)
    (hcurve :
      y ^ 2 =
        x * (x ^ 2 +
          algebraMap GaussianInt GaussianRat A * x +
          algebraMap GaussianInt GaussianRat B)) :
    squareClassOf x hx = 1 ∨
      squareClassOf x hx = classI ∨
      squareClassOf x hx = classLambda ∨
      squareClassOf x hx = classILambda ∨
      squareClassOf x hx = classPi ∨
      squareClassOf x hx = classIPi ∨
      squareClassOf x hx = classLambdaPi ∨
      squareClassOf x hx = classILambdaPi := by
  obtain ⟨eL, eP, heL, heP, g, _hg0, hg, hclass⟩ :=
    curve_abscissa_squareClass_supported_on_two_primes
      gaussianLambdaInt_prime gaussianPiInt_prime
      lambda_not_associated_pi hBsupport hx hcurve
  have heLCases : eL = 0 ∨ eL = 1 := by omega
  have hePCases : eP = 0 ∨ eP = 1 := by omega
  rcases heLCases with rfl | rfl <;>
    rcases hePCases with rfl | rfl <;>
    rcases hg with rfl | rfl
  · refine Or.inl (hclass.trans ?_)
    calc
      squareClassOf
          (algebraMap GaussianInt GaussianRat
            (1 * gaussianLambdaInt ^ 0 * gaussianPiInt ^ 0)) _ =
        squareClassOf 1 one_ne_zero := by
          apply squareClassOf_congr
          simpa only [pow_zero, mul_one] using
            (map_one (algebraMap GaussianInt GaussianRat))
      _ = 1 := squareClassOf_one
  · refine Or.inr (Or.inl (hclass.trans ?_))
    unfold GaussianDescent.classI
    apply squareClassOf_congr
    simpa only [pow_zero, mul_one] using
      GaussianPrimes.algebraMap_gaussianIInt
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hclass.trans ?_)))))
    unfold GaussianDescent.classPi
    apply squareClassOf_congr
    simpa only [pow_zero, pow_one, one_mul] using
      GaussianPrimes.algebraMap_gaussianPiInt
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hclass.trans ?_))))))
    unfold GaussianDescent.classIPi
    apply squareClassOf_congr
    have hmap := congrArg₂ (fun a b : GaussianRat => a * b)
      GaussianPrimes.algebraMap_gaussianIInt
      GaussianPrimes.algebraMap_gaussianPiInt
    simpa only [pow_zero, pow_one, one_mul, map_mul, map_one, mul_one] using hmap
  · refine Or.inr (Or.inr (Or.inl (hclass.trans ?_)))
    unfold classLambda
    apply squareClassOf_congr
    simp
  · refine Or.inr (Or.inr (Or.inr (Or.inl (hclass.trans ?_))))
    unfold classILambda
    apply squareClassOf_congr
    simp
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (hclass.trans ?_)))))))
    unfold classLambdaPi
    apply squareClassOf_congr
    simp
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (hclass.trans ?_)))))))
    unfold classILambdaPi
    apply squareClassOf_congr
    simp

/-- Raw support at `lambda` and `rho`, before the mod-4 lambda obstruction. -/
theorem curve_abscissa_rho_raw_cases
    {A B : GaussianInt}
    (hBsupport : ∀ q : GaussianInt, Prime q → q ∣ B →
      Associated q gaussianLambdaInt ∨ Associated q gaussianRhoInt)
    {x y : GaussianRat} (hx : x ≠ 0)
    (hcurve :
      y ^ 2 =
        x * (x ^ 2 +
          algebraMap GaussianInt GaussianRat A * x +
          algebraMap GaussianInt GaussianRat B)) :
    squareClassOf x hx = 1 ∨
      squareClassOf x hx = classI ∨
      squareClassOf x hx = classLambda ∨
      squareClassOf x hx = classILambda ∨
      squareClassOf x hx = classRho ∨
      squareClassOf x hx = classIRho ∨
      squareClassOf x hx = classLambdaRho ∨
      squareClassOf x hx = classILambdaRho := by
  obtain ⟨eL, eP, heL, heP, g, _hg0, hg, hclass⟩ :=
    curve_abscissa_squareClass_supported_on_two_primes
      gaussianLambdaInt_prime gaussianRhoInt_prime
      lambda_not_associated_rho hBsupport hx hcurve
  have heLCases : eL = 0 ∨ eL = 1 := by omega
  have hePCases : eP = 0 ∨ eP = 1 := by omega
  rcases heLCases with rfl | rfl <;>
    rcases hePCases with rfl | rfl <;>
    rcases hg with rfl | rfl
  · refine Or.inl (hclass.trans ?_)
    calc
      squareClassOf
          (algebraMap GaussianInt GaussianRat
            (1 * gaussianLambdaInt ^ 0 * gaussianRhoInt ^ 0)) _ =
        squareClassOf 1 one_ne_zero := by
          apply squareClassOf_congr
          simpa only [pow_zero, mul_one] using
            (map_one (algebraMap GaussianInt GaussianRat))
      _ = 1 := squareClassOf_one
  · refine Or.inr (Or.inl (hclass.trans ?_))
    unfold GaussianDescent.classI
    apply squareClassOf_congr
    simpa only [pow_zero, mul_one] using
      GaussianPrimes.algebraMap_gaussianIInt
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hclass.trans ?_)))))
    unfold GaussianDescent.classRho
    apply squareClassOf_congr
    simpa only [pow_zero, pow_one, one_mul] using
      GaussianPrimes.algebraMap_gaussianRhoInt
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hclass.trans ?_))))))
    unfold GaussianDescent.classIRho
    apply squareClassOf_congr
    have hmap := congrArg₂ (fun a b : GaussianRat => a * b)
      GaussianPrimes.algebraMap_gaussianIInt
      GaussianPrimes.algebraMap_gaussianRhoInt
    simpa only [pow_zero, pow_one, one_mul, map_mul, map_one, mul_one] using hmap
  · refine Or.inr (Or.inr (Or.inl (hclass.trans ?_)))
    unfold classLambda
    apply squareClassOf_congr
    simp
  · refine Or.inr (Or.inr (Or.inr (Or.inl (hclass.trans ?_))))
    unfold classILambda
    apply squareClassOf_congr
    simp
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (hclass.trans ?_)))))))
    unfold classLambdaRho
    apply squareClassOf_congr
    simp
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (hclass.trans ?_)))))))
    unfold classILambdaRho
    apply squareClassOf_congr
    simp

end GaussianRange

end

end Cuboid2
