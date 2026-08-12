import Cuboid2.FiveFive.ResultantCertificate

/-!
# Rational-root certificates for the `5+5` discriminant factors

The pinned `5+5` replay asks an external CAS to report that two explicit
discriminant factors, of degrees six and twenty-eight, have no rational roots.

This file moves that obligation into Lean.  For a rational number `x = n/d`,
a zero of either factor gives a zero of its homogeneous form at `(n,d)`.
The reduced numerator and denominator cannot both vanish modulo seven, while
a complete `49`-case kernel computation shows that neither homogeneous form
has a nontrivial zero over `ZMod 7`.

No primality oracle, factorization oracle, or external root finder is used.
-/

namespace Cuboid2

noncomputable section

/-- The degree-six discriminant factor from the pinned `5+5` certificate. -/
def fiveFiveDiscriminantP6 (s : ℚ) : ℚ :=
  s ^ 6 + 15 * s ^ 5 - 1585 * s ^ 4 + 3052 * s ^ 3 -
    1585 * s ^ 2 + 15 * s + 1

/-- The degree-twenty-eight discriminant factor from the pinned certificate. -/
def fiveFiveDiscriminantP28 (s : ℚ) : ℚ :=
  103680000 * s ^ 28 - 7521292800 * s ^ 27 +
    169819194368 * s ^ 26 - 1294911396672 * s ^ 25 +
    5782812799560 * s ^ 24 - 16312796194682 * s ^ 23 +
    26530306841415 * s ^ 22 - 10896270624660 * s ^ 21 -
    54726287337296 * s ^ 20 + 133633789213194 * s ^ 19 -
    113160119424615 * s ^ 18 - 66661996599936 * s ^ 17 +
    257666706220630 * s ^ 16 - 219804850864326 * s ^ 15 -
    42039280815751 * s ^ 14 + 237530759945852 * s ^ 13 -
    176268442531244 * s ^ 12 - 7327917745386 * s ^ 11 +
    97772884071815 * s ^ 10 - 65474588747304 * s ^ 9 +
    8804890164542 * s ^ 8 + 13121572011040 * s ^ 7 -
    9871152051904 * s ^ 6 + 3433840428544 * s ^ 5 -
    664203117056 * s ^ 4 + 64335036416 * s ^ 3 -
    1308557312 * s ^ 2 - 162529280 * s - 2097152

/-- Integral homogeneous form attached to `fiveFiveDiscriminantP6`. -/
def fiveFiveDiscriminantP6Hom (n d : ℤ) : ℤ :=
  n ^ 6 + 15 * n ^ 5 * d - 1585 * n ^ 4 * d ^ 2 +
    3052 * n ^ 3 * d ^ 3 - 1585 * n ^ 2 * d ^ 4 +
    15 * n * d ^ 5 + d ^ 6

/-- Integral homogeneous form attached to `fiveFiveDiscriminantP28`. -/
def fiveFiveDiscriminantP28Hom (n d : ℤ) : ℤ :=
  103680000 * n ^ 28 - 7521292800 * n ^ 27 * d +
    169819194368 * n ^ 26 * d ^ 2 -
    1294911396672 * n ^ 25 * d ^ 3 +
    5782812799560 * n ^ 24 * d ^ 4 -
    16312796194682 * n ^ 23 * d ^ 5 +
    26530306841415 * n ^ 22 * d ^ 6 -
    10896270624660 * n ^ 21 * d ^ 7 -
    54726287337296 * n ^ 20 * d ^ 8 +
    133633789213194 * n ^ 19 * d ^ 9 -
    113160119424615 * n ^ 18 * d ^ 10 -
    66661996599936 * n ^ 17 * d ^ 11 +
    257666706220630 * n ^ 16 * d ^ 12 -
    219804850864326 * n ^ 15 * d ^ 13 -
    42039280815751 * n ^ 14 * d ^ 14 +
    237530759945852 * n ^ 13 * d ^ 15 -
    176268442531244 * n ^ 12 * d ^ 16 -
    7327917745386 * n ^ 11 * d ^ 17 +
    97772884071815 * n ^ 10 * d ^ 18 -
    65474588747304 * n ^ 9 * d ^ 19 +
    8804890164542 * n ^ 8 * d ^ 20 +
    13121572011040 * n ^ 7 * d ^ 21 -
    9871152051904 * n ^ 6 * d ^ 22 +
    3433840428544 * n ^ 5 * d ^ 23 -
    664203117056 * n ^ 4 * d ^ 24 +
    64335036416 * n ^ 3 * d ^ 25 -
    1308557312 * n ^ 2 * d ^ 26 -
    162529280 * n * d ^ 27 - 2097152 * d ^ 28

private theorem fiveFiveDiscriminantP6_homogenize
    (n d : ℤ) (hd : d ≠ 0) :
    ((fiveFiveDiscriminantP6Hom n d : ℤ) : ℚ) =
      (d : ℚ) ^ 6 * fiveFiveDiscriminantP6 ((n : ℚ) / (d : ℚ)) := by
  unfold fiveFiveDiscriminantP6Hom fiveFiveDiscriminantP6
  push_cast
  field_simp [show (d : ℚ) ≠ 0 by exact_mod_cast hd]

private theorem fiveFiveDiscriminantP28_homogenize
    (n d : ℤ) (hd : d ≠ 0) :
    ((fiveFiveDiscriminantP28Hom n d : ℤ) : ℚ) =
      (d : ℚ) ^ 28 * fiveFiveDiscriminantP28 ((n : ℚ) / (d : ℚ)) := by
  unfold fiveFiveDiscriminantP28Hom fiveFiveDiscriminantP28
  push_cast
  field_simp [show (d : ℚ) ≠ 0 by exact_mod_cast hd]

/-- Reduction of the degree-six homogeneous form modulo seven. -/
private def fiveFiveDiscriminantP6HomMod7 (n d : ZMod 7) : ZMod 7 :=
  n ^ 6 + 15 * n ^ 5 * d - 1585 * n ^ 4 * d ^ 2 +
    3052 * n ^ 3 * d ^ 3 - 1585 * n ^ 2 * d ^ 4 +
    15 * n * d ^ 5 + d ^ 6

/-- Reduction of the degree-twenty-eight homogeneous form modulo seven. -/
private def fiveFiveDiscriminantP28HomMod7 (n d : ZMod 7) : ZMod 7 :=
  103680000 * n ^ 28 - 7521292800 * n ^ 27 * d +
    169819194368 * n ^ 26 * d ^ 2 -
    1294911396672 * n ^ 25 * d ^ 3 +
    5782812799560 * n ^ 24 * d ^ 4 -
    16312796194682 * n ^ 23 * d ^ 5 +
    26530306841415 * n ^ 22 * d ^ 6 -
    10896270624660 * n ^ 21 * d ^ 7 -
    54726287337296 * n ^ 20 * d ^ 8 +
    133633789213194 * n ^ 19 * d ^ 9 -
    113160119424615 * n ^ 18 * d ^ 10 -
    66661996599936 * n ^ 17 * d ^ 11 +
    257666706220630 * n ^ 16 * d ^ 12 -
    219804850864326 * n ^ 15 * d ^ 13 -
    42039280815751 * n ^ 14 * d ^ 14 +
    237530759945852 * n ^ 13 * d ^ 15 -
    176268442531244 * n ^ 12 * d ^ 16 -
    7327917745386 * n ^ 11 * d ^ 17 +
    97772884071815 * n ^ 10 * d ^ 18 -
    65474588747304 * n ^ 9 * d ^ 19 +
    8804890164542 * n ^ 8 * d ^ 20 +
    13121572011040 * n ^ 7 * d ^ 21 -
    9871152051904 * n ^ 6 * d ^ 22 +
    3433840428544 * n ^ 5 * d ^ 23 -
    664203117056 * n ^ 4 * d ^ 24 +
    64335036416 * n ^ 3 * d ^ 25 -
    1308557312 * n ^ 2 * d ^ 26 -
    162529280 * n * d ^ 27 - 2097152 * d ^ 28

private theorem fiveFiveDiscriminantP6HomMod7_eq_cast (n d : ℤ) :
    fiveFiveDiscriminantP6HomMod7 (n : ZMod 7) (d : ZMod 7) =
      (fiveFiveDiscriminantP6Hom n d : ZMod 7) := by
  unfold fiveFiveDiscriminantP6HomMod7 fiveFiveDiscriminantP6Hom
  push_cast
  ring

private theorem fiveFiveDiscriminantP28HomMod7_eq_cast (n d : ℤ) :
    fiveFiveDiscriminantP28HomMod7 (n : ZMod 7) (d : ZMod 7) =
      (fiveFiveDiscriminantP28Hom n d : ZMod 7) := by
  unfold fiveFiveDiscriminantP28HomMod7 fiveFiveDiscriminantP28Hom
  push_cast
  ring

/-- Exhaustive projective mod-seven check for the degree-six factor. -/
private theorem fiveFiveDiscriminantP6HomMod7_nonzero :
    ∀ n d : ZMod 7, ¬ (n = 0 ∧ d = 0) →
      fiveFiveDiscriminantP6HomMod7 n d ≠ 0 := by
  decide

/-- Exhaustive projective mod-seven check for the degree-twenty-eight factor. -/
private theorem fiveFiveDiscriminantP28HomMod7_nonzero :
    ∀ n d : ZMod 7, ¬ (n = 0 ∧ d = 0) →
      fiveFiveDiscriminantP28HomMod7 n d ≠ 0 := by
  decide

private theorem rat_num_den_not_both_zero_mod7 (x : ℚ) :
    ¬ ((((x.num : ℤ) : ZMod 7) = 0) ∧
      ((((x.den : ℕ) : ℤ) : ZMod 7) = 0)) := by
  rintro ⟨hnum, hden⟩
  have hnumInt : (7 : ℤ) ∣ x.num :=
    (CharP.intCast_eq_zero_iff (ZMod 7) 7 x.num).mp hnum
  have hnumNat : 7 ∣ x.num.natAbs := by
    rw [← Int.natCast_dvd]
    exact hnumInt
  have hdenInt : (7 : ℤ) ∣ (x.den : ℤ) :=
    (CharP.intCast_eq_zero_iff (ZMod 7) 7 (x.den : ℤ)).mp hden
  have hdenNat : 7 ∣ x.den := by
    exact_mod_cast hdenInt
  have hgcd : 7 ∣ Nat.gcd x.num.natAbs x.den :=
    Nat.dvd_gcd hnumNat hdenNat
  rw [x.reduced.gcd_eq_one] at hgcd
  norm_num at hgcd

/-- The degree-six discriminant factor has no rational root. -/
theorem fiveFiveDiscriminantP6_ne_zero (x : ℚ) :
    fiveFiveDiscriminantP6 x ≠ 0 := by
  intro hx
  have hdenZ : (x.den : ℤ) ≠ 0 := by
    exact_mod_cast (Rat.den_nz x)
  have hhomQ :=
    fiveFiveDiscriminantP6_homogenize x.num (x.den : ℤ) hdenZ
  have hrepr : (x.num : ℚ) / (x.den : ℚ) = x := Rat.num_div_den x
  have hdenCast : (((x.den : ℤ) : ℚ)) = (x.den : ℚ) := by norm_num
  rw [hdenCast] at hhomQ
  rw [hrepr, hx, mul_zero] at hhomQ
  have hhomZ : fiveFiveDiscriminantP6Hom x.num (x.den : ℤ) = 0 := by
    exact_mod_cast hhomQ
  have hcast :=
    congrArg (Int.castRingHom (ZMod 7)) hhomZ
  have hmod :
      fiveFiveDiscriminantP6HomMod7
        ((x.num : ℤ) : ZMod 7) (((x.den : ℕ) : ℤ) : ZMod 7) = 0 := by
    rw [fiveFiveDiscriminantP6HomMod7_eq_cast]
    simpa using hcast
  exact fiveFiveDiscriminantP6HomMod7_nonzero _ _
    (rat_num_den_not_both_zero_mod7 x) hmod

/-- The degree-twenty-eight discriminant factor has no rational root. -/
theorem fiveFiveDiscriminantP28_ne_zero (x : ℚ) :
    fiveFiveDiscriminantP28 x ≠ 0 := by
  intro hx
  have hdenZ : (x.den : ℤ) ≠ 0 := by
    exact_mod_cast (Rat.den_nz x)
  have hhomQ :=
    fiveFiveDiscriminantP28_homogenize x.num (x.den : ℤ) hdenZ
  have hrepr : (x.num : ℚ) / (x.den : ℚ) = x := Rat.num_div_den x
  have hdenCast : (((x.den : ℤ) : ℚ)) = (x.den : ℚ) := by norm_num
  rw [hdenCast] at hhomQ
  rw [hrepr, hx, mul_zero] at hhomQ
  have hhomZ : fiveFiveDiscriminantP28Hom x.num (x.den : ℤ) = 0 := by
    exact_mod_cast hhomQ
  have hcast :=
    congrArg (Int.castRingHom (ZMod 7)) hhomZ
  have hmod :
      fiveFiveDiscriminantP28HomMod7
        ((x.num : ℤ) : ZMod 7) (((x.den : ℕ) : ℤ) : ZMod 7) = 0 := by
    rw [fiveFiveDiscriminantP28HomMod7_eq_cast]
    simpa using hcast
  exact fiveFiveDiscriminantP28HomMod7_nonzero _ _
    (rat_num_den_not_both_zero_mod7 x) hmod

/-- Combined replacement for the external `ground_roots()` checks. -/
theorem fiveFive_discriminant_factors_have_no_rational_roots :
    (∀ x : ℚ, fiveFiveDiscriminantP6 x ≠ 0) ∧
      ∀ x : ℚ, fiveFiveDiscriminantP28 x ≠ 0 :=
  ⟨fiveFiveDiscriminantP6_ne_zero, fiveFiveDiscriminantP28_ne_zero⟩

/-- Palindromicity of the degree-six factor, useful for reciprocal intervals. -/
theorem fiveFiveDiscriminantP6_reciprocal
    {s : ℚ} (hs : s ≠ 0) :
    s ^ 6 * fiveFiveDiscriminantP6 s⁻¹ =
      fiveFiveDiscriminantP6 s := by
  unfold fiveFiveDiscriminantP6
  field_simp [hs]
  ring

end

end Cuboid2
