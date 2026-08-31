import Cuboid2.QuadraticReduction.GaussianCover
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.RingTheory.Int.Basic

/-!
# The rational octic cover splits into two Gaussian covers

This file formalizes the elementary primitive-Pythagorean-triple argument
which sends every rational point of the octic curve to one of the two
quartic covers over `ℚ(i)`.
-/

namespace Cuboid2

noncomputable section

/-- The real part of the denominator-cleared Gaussian quartic. -/
def gaussianSplitA (m n : ℤ) : ℤ :=
  2 * m ^ 4 - n ^ 4

/-- The imaginary part of the denominator-cleared Gaussian quartic. -/
def gaussianSplitB (m n : ℤ) : ℤ :=
  2 * n ^ 2 * (m ^ 2 - n ^ 2)

/-- A rational number whose square is an integer is itself an integer. -/
theorem rat_isInt_of_sq_eq_int
    {x : ℚ} {N : ℤ} (h : x ^ 2 = (N : ℚ)) :
    ∃ z : ℤ, x = z := by
  have hden : (x ^ 2).den = 1 := by
    rw [h]
    exact Rat.den_intCast N
  rw [Rat.den_pow] at hden
  have hxden : x.den = 1 := by
    nlinarith [x.den_pos]
  exact ⟨x.num, (Rat.coe_int_num_of_den_eq_one hxden).symm⟩

/-- Clearing the denominator of an octic point gives an integral
Pythagorean triple. -/
theorem octic_denominator_pythagorean (P : OcticPoint) :
    let m : ℤ := P.u.num
    let n : ℤ := P.u.den
    ∃ R : ℤ,
      P.r * (n : ℚ) ^ 4 = R ∧
        PythagoreanTriple (gaussianSplitA m n) (gaussianSplitB m n) R := by
  let m : ℤ := P.u.num
  let n : ℤ := P.u.den
  have hnInt : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast P.u.den_ne_zero
  have hn : (n : ℚ) ≠ 0 := by
    exact_mod_cast hnInt
  have hu : P.u = (m : ℚ) / (n : ℚ) := by
    exact P.u.num_div_den.symm
  have hsq :
      (P.r * (n : ℚ) ^ 4) ^ 2 =
        ((gaussianSplitA m n) ^ 2 + (gaussianSplitB m n) ^ 2 : ℤ) := by
    calc
      (P.r * (n : ℚ) ^ 4) ^ 2 =
          P.r ^ 2 * (n : ℚ) ^ 8 := by ring
      _ = octicRhs P.u * (n : ℚ) ^ 8 := by rw [P.onCurve]
      _ = ((gaussianSplitA m n) ^ 2 +
          (gaussianSplitB m n) ^ 2 : ℤ) := by
        rw [hu]
        norm_num [octicRhs, gaussianSplitA, gaussianSplitB]
        field_simp [hn]
        ring
  obtain ⟨R, hR⟩ := rat_isInt_of_sq_eq_int hsq
  refine ⟨R, hR, ?_⟩
  rw [hR] at hsq
  unfold PythagoreanTriple
  have hsqInt :
      (gaussianSplitA m n) ^ 2 + (gaussianSplitB m n) ^ 2 = R ^ 2 := by
    exact_mod_cast hsq.symm
  simpa [m, n, pow_two] using hsqInt

/-- When the reduced denominator is odd, the two legs obtained from the
Gaussian norm factorization are coprime. -/
theorem gaussianSplit_coprime_of_odd
    {m n : ℤ} (hmn : IsCoprime m n) (hn : Odd n) :
    IsCoprime (gaussianSplitA m n) (gaussianSplitB m n) := by
  have hmn42 : IsCoprime (m ^ 4) (n ^ 2) :=
    hmn.pow
  have h2n2 : IsCoprime (2 : ℤ) (n ^ 2) :=
    (Int.isCoprime_two_left.mpr hn).pow_right
  have hAn2 : IsCoprime (gaussianSplitA m n) (n ^ 2) := by
    have h := h2n2.mul_left hmn42
    have h' := h.add_mul_left_left (-(n ^ 2))
    have heq :
        2 * m ^ 4 + n ^ 2 * (-(n ^ 2)) = gaussianSplitA m n := by
      simp only [gaussianSplitA]
      ring
    rw [← heq]
    exact h'
  have hnd : IsCoprime n (m ^ 2 - n ^ 2) := by
    have h := hmn.symm.pow_right (n := 2)
    have h' := h.add_mul_right_right (-n)
    have heq : m ^ 2 + (-n) * n = m ^ 2 - n ^ 2 := by ring
    rw [← heq]
    exact h'
  have hn4d : IsCoprime (n ^ 4) (m ^ 2 - n ^ 2) :=
    hnd.pow_left
  have hAd : IsCoprime (gaussianSplitA m n) (m ^ 2 - n ^ 2) := by
    have h := hn4d.add_mul_left_left (2 * (m ^ 2 + n ^ 2))
    have heq :
        n ^ 4 + (m ^ 2 - n ^ 2) * (2 * (m ^ 2 + n ^ 2)) =
          gaussianSplitA m n := by
      simp only [gaussianSplitA]
      ring
    rw [← heq]
    exact h
  have hA2 : IsCoprime (gaussianSplitA m n) (2 : ℤ) := by
    apply Int.isCoprime_two_right.mpr
    exact (even_two_mul (m ^ 4)).sub_odd hn.pow
  have hAB :
      IsCoprime (gaussianSplitA m n)
        (2 * (n ^ 2 * (m ^ 2 - n ^ 2))) :=
    hA2.mul_right (hAn2.mul_right hAd)
  simpa [gaussianSplitB, mul_assoc] using hAB

/-- The first leg after dividing the even-denominator triple by two. -/
def gaussianSplitEvenA (m N : ℤ) : ℤ :=
  m ^ 4 - 8 * N ^ 4

/-- The second leg after dividing the even-denominator triple by two. -/
def gaussianSplitEvenB (m N : ℤ) : ℤ :=
  (2 * N) ^ 2 * (m ^ 2 - (2 * N) ^ 2)

theorem gaussianSplitA_two_mul (m N : ℤ) :
    gaussianSplitA m (2 * N) = 2 * gaussianSplitEvenA m N := by
  simp only [gaussianSplitA, gaussianSplitEvenA]
  ring

theorem gaussianSplitB_two_mul (m N : ℤ) :
    gaussianSplitB m (2 * N) = 2 * gaussianSplitEvenB m N := by
  simp only [gaussianSplitB, gaussianSplitEvenB]
  ring

/-- In the even-denominator case, the two legs remaining after division by
two are coprime. -/
theorem gaussianSplitEven_coprime
    {m N : ℤ} (hmN : IsCoprime m N) (hm : Odd m) :
    IsCoprime (gaussianSplitEvenA m N) (gaussianSplitEvenB m N) := by
  have hAodd : Odd (gaussianSplitEvenA m N) := by
    apply hm.pow.sub_even
    have heq : 8 * N ^ 4 = 2 * (4 * N ^ 4) := by ring
    rw [heq]
    exact even_two_mul _
  have hA4 : IsCoprime (gaussianSplitEvenA m N) ((2 : ℤ) ^ 2) :=
    (Int.isCoprime_two_right.mpr hAodd).pow_right
  have hm4N2 : IsCoprime (m ^ 4) (N ^ 2) :=
    hmN.pow
  have hAN2 : IsCoprime (gaussianSplitEvenA m N) (N ^ 2) := by
    have h := hm4N2.add_mul_left_left (-8 * N ^ 2)
    have heq :
        m ^ 4 + N ^ 2 * (-8 * N ^ 2) = gaussianSplitEvenA m N := by
      simp only [gaussianSplitEvenA]
      ring
    rw [← heq]
    exact h
  have hNd : IsCoprime N (m ^ 2 - (2 * N) ^ 2) := by
    have h := hmN.symm.pow_right (n := 2)
    have h' := h.add_mul_right_right (-4 * N)
    have heq : m ^ 2 + (-4 * N) * N = m ^ 2 - (2 * N) ^ 2 := by ring
    rw [← heq]
    exact h'
  have hN4d : IsCoprime (N ^ 4) (m ^ 2 - (2 * N) ^ 2) :=
    hNd.pow_left
  have hdOdd : Odd (m ^ 2 - (2 * N) ^ 2) := by
    apply hm.pow.sub_even
    have heq : (2 * N) ^ 2 = 2 * (2 * N ^ 2) := by ring
    rw [heq]
    exact even_two_mul _
  have h8d : IsCoprime ((2 : ℤ) ^ 3) (m ^ 2 - (2 * N) ^ 2) :=
    (Int.isCoprime_two_left.mpr hdOdd).pow_left
  have h8N4d :
      IsCoprime ((2 : ℤ) ^ 3 * N ^ 4) (m ^ 2 - (2 * N) ^ 2) :=
    h8d.mul_left hN4d
  have hAd :
      IsCoprime (gaussianSplitEvenA m N) (m ^ 2 - (2 * N) ^ 2) := by
    have h := h8N4d.add_mul_left_left (m ^ 2 + 4 * N ^ 2)
    have heq :
        (2 : ℤ) ^ 3 * N ^ 4 +
            (m ^ 2 - (2 * N) ^ 2) * (m ^ 2 + 4 * N ^ 2) =
          gaussianSplitEvenA m N := by
      simp only [gaussianSplitEvenA]
      ring
    rw [← heq]
    exact h
  have hAB :
      IsCoprime (gaussianSplitEvenA m N)
        ((2 : ℤ) ^ 2 * (N ^ 2 * (m ^ 2 - (2 * N) ^ 2))) :=
    hA4.mul_right (hAN2.mul_right hAd)
  have heq :
      (2 : ℤ) ^ 2 * (N ^ 2 * (m ^ 2 - (2 * N) ^ 2)) =
        gaussianSplitEvenB m N := by
    simp only [gaussianSplitEvenB]
    ring
  rw [← heq]
  exact hAB

/-- The primitive triple in the odd-denominator case has the orientation
needed for a square of `c+di`. -/
theorem octic_odd_square_split
    (P : OcticPoint) (hn : Odd (P.u.den : ℤ)) :
    ∃ c d : ℤ,
      gaussianSplitA P.u.num P.u.den = c ^ 2 - d ^ 2 ∧
      gaussianSplitB P.u.num P.u.den = 2 * c * d := by
  obtain ⟨R, -, hTriple⟩ := octic_denominator_pythagorean P
  have hCoprime :
      IsCoprime (gaussianSplitA P.u.num P.u.den)
        (gaussianSplitB P.u.num P.u.den) :=
    gaussianSplit_coprime_of_odd P.u.isCoprime_num_den hn
  have hGcd :
      Int.gcd (gaussianSplitA P.u.num P.u.den)
        (gaussianSplitB P.u.num P.u.den) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp hCoprime
  obtain ⟨c, d, hLegs, -, -, -⟩ :=
    PythagoreanTriple.coprime_classification.mp ⟨hTriple, hGcd⟩
  rcases hLegs with hLegs | hLegs
  · exact ⟨c, d, hLegs.1, hLegs.2⟩
  · have hAodd : Odd (gaussianSplitA P.u.num P.u.den) := by
      apply (even_two_mul (P.u.num ^ 4)).sub_odd
      exact hn.pow
    have hAeven : Even (gaussianSplitA P.u.num P.u.den) := by
      rw [hLegs.1]
      have heq : 2 * c * d = 2 * (c * d) := by ring
      rw [heq]
      exact even_two_mul _
    exact False.elim ((Int.not_even_iff_odd.mpr hAodd) hAeven)

/-- The primitive triple after division by two in the even-denominator case
has the orientation needed for a square of `(1-i)(c+di)`. -/
theorem octic_even_square_split
    (P : OcticPoint) (hn : Even (P.u.den : ℤ)) :
    ∃ N c d : ℤ,
      P.u.den = 2 * N ∧
      gaussianSplitEvenA P.u.num N = c ^ 2 - d ^ 2 ∧
      gaussianSplitEvenB P.u.num N = 2 * c * d := by
  obtain ⟨N, hN⟩ := hn
  have hden : P.u.den = 2 * N := by
    rw [two_mul]
    exact hN
  obtain ⟨R, -, hTriple⟩ := octic_denominator_pythagorean P
  have hmden : IsCoprime P.u.num P.u.den :=
    P.u.isCoprime_num_den
  have hNdiv : N ∣ P.u.den := by
    rw [hden]
    exact ⟨2, by ring⟩
  have h2div : (2 : ℤ) ∣ P.u.den := by
    rw [hden]
    exact ⟨N, rfl⟩
  have hmN : IsCoprime P.u.num N :=
    hmden.of_isCoprime_of_dvd_right hNdiv
  have hm2 : IsCoprime P.u.num (2 : ℤ) :=
    hmden.of_isCoprime_of_dvd_right h2div
  have hmOdd : Odd P.u.num :=
    Int.isCoprime_two_right.mp hm2
  have hAeven :
      Even (gaussianSplitA P.u.num P.u.den) := by
    rw [hden, gaussianSplitA_two_mul]
    exact even_two_mul _
  have hBeven :
      Even (gaussianSplitB P.u.num P.u.den) := by
    rw [hden, gaussianSplitB_two_mul]
    exact even_two_mul _
  have hRsqEven : Even (R ^ 2) := by
    rw [pow_two]
    rw [← hTriple.eq]
    exact (hAeven.mul_right _).add (hBeven.mul_right _)
  have hReven : Even R := by
    by_contra hR
    have hRodd : Odd R := Int.not_even_iff_odd.mp hR
    exact (Int.not_even_iff_odd.mpr hRodd.pow) hRsqEven
  obtain ⟨R0, hR0⟩ := hReven
  have hR : R = 2 * R0 := by
    rw [two_mul]
    exact hR0
  have hHalfTriple :
      PythagoreanTriple
        (gaussianSplitEvenA P.u.num N)
        (gaussianSplitEvenB P.u.num N) R0 := by
    unfold PythagoreanTriple
    have h := hTriple.eq
    rw [hden, gaussianSplitA_two_mul, gaussianSplitB_two_mul, hR] at h
    nlinarith
  have hHalfCoprime :
      IsCoprime
        (gaussianSplitEvenA P.u.num N)
        (gaussianSplitEvenB P.u.num N) :=
    gaussianSplitEven_coprime hmN hmOdd
  have hHalfGcd :
      Int.gcd (gaussianSplitEvenA P.u.num N)
        (gaussianSplitEvenB P.u.num N) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp hHalfCoprime
  obtain ⟨c, d, hLegs, -, -, -⟩ :=
    PythagoreanTriple.coprime_classification.mp
      ⟨hHalfTriple, hHalfGcd⟩
  rcases hLegs with hLegs | hLegs
  · exact ⟨N, c, d, hden, hLegs.1, hLegs.2⟩
  · have hAodd : Odd (gaussianSplitEvenA P.u.num N) := by
      apply hmOdd.pow.sub_even
      have heq : 8 * N ^ 4 = 2 * (4 * N ^ 4) := by ring
      rw [heq]
      exact even_two_mul _
    have hAeven : Even (gaussianSplitEvenA P.u.num N) := by
      rw [hLegs.1]
      have heq : 2 * c * d = 2 * (c * d) := by ring
      rw [heq]
      exact even_two_mul _
    exact False.elim ((Int.not_even_iff_odd.mpr hAodd) hAeven)

/-- Every rational point of the octic curve lifts to one of its two Gaussian
quartic covers.  The choice is exactly the parity of the reduced
denominator. -/
theorem octic_to_gaussian_cover (P : OcticPoint) :
    (∃ C : GaussianCoverZeroPoint, C.u = P.u) ∨
      (∃ C : GaussianCoverOnePoint, C.u = P.u) := by
  rcases Int.even_or_odd (P.u.den : ℤ) with hn | hn
  · obtain ⟨N, c, d, hden, hA, hB⟩ :=
      octic_even_square_split P hn
    have hn0 : (P.u.den : ℚ) ≠ 0 := by
      exact_mod_cast P.u.den_ne_zero
    have hN0 : (N : ℚ) ≠ 0 := by
      intro h
      apply hn0
      rw [show (P.u.den : ℚ) = 2 * (N : ℚ) by exact_mod_cast hden]
      rw [h]
      norm_num
    let w : GaussianRat :=
      ⟨((c + d : ℤ) : ℚ) / (P.u.den : ℚ) ^ 2,
        ((d - c : ℤ) : ℚ) / (P.u.den : ℚ) ^ 2⟩
    have hw : w ^ 2 = -gaussianI * gaussianQuartic P.u := by
      have hu : P.u = (P.u.num : ℚ) / (P.u.den : ℚ) :=
        P.u.num_div_den.symm
      have hAq :
          (gaussianSplitEvenA P.u.num N : ℚ) =
            (c : ℚ) ^ 2 - (d : ℚ) ^ 2 := by
        exact_mod_cast hA
      have hBq :
          (gaussianSplitEvenB P.u.num N : ℚ) =
            2 * (c : ℚ) * (d : ℚ) := by
        exact_mod_cast hB
      norm_num [gaussianSplitEvenA] at hAq
      norm_num [gaussianSplitEvenB] at hBq
      have hqRe :
          2 * P.u ^ 4 - 1 =
            2 * ((c : ℚ) ^ 2 - (d : ℚ) ^ 2) /
              (P.u.den : ℚ) ^ 4 := by
        conv_lhs => rw [hu]
        rw [show (P.u.den : ℚ) = 2 * (N : ℚ) by exact_mod_cast hden]
        field_simp [hN0]
        nlinarith [hAq]
      have hqIm :
          2 * P.u ^ 2 - 2 =
            2 * (2 * (c : ℚ) * (d : ℚ)) /
              (P.u.den : ℚ) ^ 4 := by
        conv_lhs => rw [hu]
        rw [show (P.u.den : ℚ) = 2 * (N : ℚ) by exact_mod_cast hden]
        field_simp [hN0]
        nlinarith [hBq]
      have hqIm' :
          2 * (P.u * P.u) - 2 =
            2 * (2 * (c : ℚ) * (d : ℚ)) /
              (P.u.den : ℚ) ^ 4 := by
        simpa [pow_two] using hqIm
      have hNegI : -gaussianI = (⟨0, -1⟩ : GaussianRat) := by
        ext <;> simp
      rw [hNegI]
      ext
      · simp only [w, pow_two, QuadraticAlgebra.re_mul,
          gaussianI_re, gaussianI_im,
          gaussianQuartic_re, gaussianQuartic_im]
        rw [hqIm']
        field_simp [hn0]
        push_cast
        ring
      · simp only [w, pow_two, QuadraticAlgebra.im_mul,
          gaussianI_re, gaussianI_im,
          gaussianQuartic_re, gaussianQuartic_im]
        rw [hqRe]
        field_simp [hn0]
        push_cast
        ring
    exact Or.inr ⟨⟨P.u, w, hw⟩, rfl⟩
  · obtain ⟨c, d, hA, hB⟩ :=
      octic_odd_square_split P hn
    have hn0 : (P.u.den : ℚ) ≠ 0 := by
      exact_mod_cast P.u.den_ne_zero
    let v : GaussianRat :=
      ⟨(c : ℚ) / (P.u.den : ℚ) ^ 2,
        (d : ℚ) / (P.u.den : ℚ) ^ 2⟩
    have hv : v ^ 2 = gaussianQuartic P.u := by
      have hu : P.u = (P.u.num : ℚ) / (P.u.den : ℚ) :=
        P.u.num_div_den.symm
      have hAq :
          (gaussianSplitA P.u.num P.u.den : ℚ) =
            (c : ℚ) ^ 2 - (d : ℚ) ^ 2 := by
        exact_mod_cast hA
      have hBq :
          (gaussianSplitB P.u.num P.u.den : ℚ) =
            2 * (c : ℚ) * (d : ℚ) := by
        exact_mod_cast hB
      norm_num [gaussianSplitA] at hAq
      norm_num [gaussianSplitB] at hBq
      have hqRe :
          2 * P.u ^ 4 - 1 =
            ((c : ℚ) ^ 2 - (d : ℚ) ^ 2) /
              (P.u.den : ℚ) ^ 4 := by
        conv_lhs => rw [hu]
        field_simp [hn0]
        nlinarith [hAq]
      have hqIm :
          2 * P.u ^ 2 - 2 =
            2 * (c : ℚ) * (d : ℚ) /
              (P.u.den : ℚ) ^ 4 := by
        conv_lhs => rw [hu]
        field_simp [hn0]
        nlinarith [hBq]
      have hqIm' :
          2 * (P.u * P.u) - 2 =
            2 * (c : ℚ) * (d : ℚ) /
              (P.u.den : ℚ) ^ 4 := by
        simpa [pow_two] using hqIm
      ext
      · simp only [v, pow_two, QuadraticAlgebra.re_mul,
          gaussianQuartic_re]
        rw [hqRe]
        field_simp [hn0]
        ring
      · simp only [v, pow_two, QuadraticAlgebra.im_mul,
          gaussianQuartic_im]
        rw [hqIm']
        field_simp [hn0]
        ring
    exact Or.inl ⟨⟨P.u, v, hv⟩, rfl⟩

end

end Cuboid2
