import Cuboid2.QuadraticReduction.CharacterDescent

/-!
# Elementary exclusion of the negative common square class

The negative branch in the common-character descent requires the rational
number `-(v² + 2) * (v⁴ + v² - 4)` to be a square.  Clearing a reduced
denominator gives an integral expression.  The four parity patterns are
excluded by kernel-reduced enumeration in `ZMod 8`, `ZMod 16`, and `ZMod 64`.
-/

namespace Cuboid2

noncomputable section

/-- Integral numerator obtained after clearing the sixth power of a denominator. -/
def negAux (m n : ℤ) : ℤ :=
  -(m ^ 2 + 2 * n ^ 2) * (m ^ 4 + m ^ 2 * n ^ 2 - 4 * n ^ 4)

private theorem oddOdd (a b w : ℤ) :
    w ^ 2 ≠ negAux (2 * a + 1) (2 * b + 1) := by
  intro h
  have hmod :
      ((w ^ 2 : ℤ) : ZMod 8) =
        ((negAux (2 * a + 1) (2 * b + 1) : ℤ) : ZMod 8) :=
    congrArg (fun x : ℤ => (x : ZMod 8)) h
  have hfinite :
      ∀ A B : ZMod 8,
        -((2 * A + 1) ^ 2 + 2 * (2 * B + 1) ^ 2) *
          ((2 * A + 1) ^ 4 + (2 * A + 1) ^ 2 * (2 * B + 1) ^ 2 -
            4 * (2 * B + 1) ^ 4) = 6 := by
    decide
  have hcast :
      ((negAux (2 * a + 1) (2 * b + 1) : ℤ) : ZMod 8) = 6 := by
    calc
      _ = -((2 * (a : ZMod 8) + 1) ^ 2 +
            2 * (2 * (b : ZMod 8) + 1) ^ 2) *
          ((2 * (a : ZMod 8) + 1) ^ 4 +
            (2 * (a : ZMod 8) + 1) ^ 2 * (2 * (b : ZMod 8) + 1) ^ 2 -
            4 * (2 * (b : ZMod 8) + 1) ^ 4) := by
              simp [negAux]
      _ = 6 := hfinite _ _
  have hsquare : ∀ W : ZMod 8, W ^ 2 ≠ 6 := by decide
  apply hsquare (w : ZMod 8)
  rw [hcast] at hmod
  simpa using hmod

private theorem oddEven (a b w : ℤ) :
    w ^ 2 ≠ negAux (2 * a + 1) (2 * b) := by
  intro h
  have hmod :
      ((w ^ 2 : ℤ) : ZMod 8) =
        ((negAux (2 * a + 1) (2 * b) : ℤ) : ZMod 8) :=
    congrArg (fun x : ℤ => (x : ZMod 8)) h
  let E : ZMod 8 :=
    -((2 * (a : ZMod 8) + 1) ^ 2 + 2 * (2 * (b : ZMod 8)) ^ 2) *
      ((2 * (a : ZMod 8) + 1) ^ 4 +
        (2 * (a : ZMod 8) + 1) ^ 2 * (2 * (b : ZMod 8)) ^ 2 -
        4 * (2 * (b : ZMod 8)) ^ 4)
  have hfinite : ∀ A B : ZMod 8,
      -((2 * A + 1) ^ 2 + 2 * (2 * B) ^ 2) *
          ((2 * A + 1) ^ 4 + (2 * A + 1) ^ 2 * (2 * B) ^ 2 -
            4 * (2 * B) ^ 4) = 3 ∨
        -((2 * A + 1) ^ 2 + 2 * (2 * B) ^ 2) *
          ((2 * A + 1) ^ 4 + (2 * A + 1) ^ 2 * (2 * B) ^ 2 -
            4 * (2 * B) ^ 4) = 7 := by decide
  have hcast : ((negAux (2 * a + 1) (2 * b) : ℤ) : ZMod 8) = E := by
    dsimp [E]
    simp [negAux]
  have hexpr : E = 3 ∨ E = 7 := hfinite _ _
  have hsquare3 : ∀ W : ZMod 8, W ^ 2 ≠ 3 := by decide
  have hsquare7 : ∀ W : ZMod 8, W ^ 2 ≠ 7 := by decide
  rw [hcast] at hmod
  rcases hexpr with hexpr | hexpr
  · apply hsquare3 (w : ZMod 8)
    rw [hexpr] at hmod
    simpa using hmod
  · apply hsquare7 (w : ZMod 8)
    rw [hexpr] at hmod
    simpa using hmod

private theorem fourOdd (a b w : ℤ) :
    w ^ 2 ≠ negAux (4 * a) (2 * b + 1) := by
  intro h
  have hmod :
      ((w ^ 2 : ℤ) : ZMod 16) =
        ((negAux (4 * a) (2 * b + 1) : ℤ) : ZMod 16) :=
    congrArg (fun x : ℤ => (x : ZMod 16)) h
  have hfinite :
      ∀ A B : ZMod 16,
        -((4 * A) ^ 2 + 2 * (2 * B + 1) ^ 2) *
          ((4 * A) ^ 4 + (4 * A) ^ 2 * (2 * B + 1) ^ 2 -
            4 * (2 * B + 1) ^ 4) = 8 := by decide
  have hcast : ((negAux (4 * a) (2 * b + 1) : ℤ) : ZMod 16) = 8 := by
    calc
      _ = -((4 * (a : ZMod 16)) ^ 2 +
            2 * (2 * (b : ZMod 16) + 1) ^ 2) *
          ((4 * (a : ZMod 16)) ^ 4 +
            (4 * (a : ZMod 16)) ^ 2 * (2 * (b : ZMod 16) + 1) ^ 2 -
            4 * (2 * (b : ZMod 16) + 1) ^ 4) := by
              simp [negAux]
      _ = 8 := hfinite _ _
  have hsquare : ∀ W : ZMod 16, W ^ 2 ≠ 8 := by decide
  apply hsquare (w : ZMod 16)
  rw [hcast] at hmod
  simpa using hmod

private theorem twoOddOdd (a b w : ℤ) :
    w ^ 2 ≠ negAux (2 * (2 * a + 1)) (2 * b + 1) := by
  intro h
  have hmod :
      ((w ^ 2 : ℤ) : ZMod 64) =
        ((negAux (2 * (2 * a + 1)) (2 * b + 1) : ℤ) : ZMod 64) :=
    congrArg (fun x : ℤ => (x : ZMod 64)) h
  have hfinite :
      ∀ A B : ZMod 64,
        -((2 * (2 * A + 1)) ^ 2 + 2 * (2 * B + 1) ^ 2) *
          ((2 * (2 * A + 1)) ^ 4 +
            (2 * (2 * A + 1)) ^ 2 * (2 * B + 1) ^ 2 -
            4 * (2 * B + 1) ^ 4) = 32 := by
    set_option maxRecDepth 100000 in
      set_option maxHeartbeats 2000000 in
        decide
  have hcast :
      ((negAux (2 * (2 * a + 1)) (2 * b + 1) : ℤ) : ZMod 64) = 32 := by
    calc
      _ = -((2 * (2 * (a : ZMod 64) + 1)) ^ 2 +
            2 * (2 * (b : ZMod 64) + 1) ^ 2) *
          ((2 * (2 * (a : ZMod 64) + 1)) ^ 4 +
            (2 * (2 * (a : ZMod 64) + 1)) ^ 2 *
              (2 * (b : ZMod 64) + 1) ^ 2 -
            4 * (2 * (b : ZMod 64) + 1) ^ 4) := by
              simp [negAux]
      _ = 32 := hfinite _ _
  have hsquare : ∀ W : ZMod 64, W ^ 2 ≠ 32 := by
    decide
  apply hsquare (w : ZMod 64)
  rw [hcast] at hmod
  simpa using hmod

/-- The cleared integral expression is never a square for coprime inputs. -/
theorem negAux_not_isSquare_of_coprime (m n : ℤ)
    (hcop : m.natAbs.Coprime n.natAbs) :
    ¬ IsSquare (negAux m n) := by
  rintro ⟨w, hw⟩
  rcases Int.even_or_odd m with hm | hm
  · rcases even_iff_exists_two_mul.mp hm with ⟨a, rfl⟩
    rcases Int.even_or_odd n with hn | hn
    · rcases even_iff_exists_two_mul.mp hn with ⟨b, rfl⟩
      apply (Nat.not_coprime_of_dvd_of_dvd (d := 2) (by norm_num)
        (by simp [Int.natAbs_mul]) (by simp [Int.natAbs_mul])) hcop
    · rcases odd_iff_exists_bit1.mp hn with ⟨b, rfl⟩
      rcases Int.even_or_odd a with ha | ha
      · rcases even_iff_exists_two_mul.mp ha with ⟨c, rfl⟩
        apply fourOdd c b w
        rw [show (2 : ℤ) * (2 * c) = 4 * c by ring] at hw
        simpa [pow_two] using hw.symm
      · rcases odd_iff_exists_bit1.mp ha with ⟨c, rfl⟩
        apply twoOddOdd c b w
        simpa [pow_two] using hw.symm
  · rcases odd_iff_exists_bit1.mp hm with ⟨a, rfl⟩
    rcases Int.even_or_odd n with hn | hn
    · rcases even_iff_exists_two_mul.mp hn with ⟨b, rfl⟩
      apply oddEven a b w
      simpa [pow_two] using hw.symm
    · rcases odd_iff_exists_bit1.mp hn with ⟨b, rfl⟩
      apply oddOdd a b w
      simpa [pow_two] using hw.symm

/-- Right-hand side of the necessary square equation in the negative branch. -/
def negativeSquareclassRhs (v : ℚ) : ℚ :=
  -(v ^ 2 + 2) * (v ^ 4 + v ^ 2 - 4)

/-- The negative common square class is impossible over the rationals. -/
theorem negativeSquareclassRhs_not_isSquare (v : ℚ) :
    ¬ IsSquare (negativeSquareclassRhs v) := by
  intro hs
  let m : ℤ := v.num
  let n : ℤ := v.den
  have hn : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast v.den_ne_zero
  have hidentity :
      ((negAux m n : ℤ) : ℚ) =
        negativeSquareclassRhs v * (n : ℚ) ^ 6 := by
    rw [← v.num_div_den]
    dsimp [m, n, negAux, negativeSquareclassRhs]
    push_cast
    field_simp [hn]
  have hden : IsSquare ((n : ℚ) ^ 6) := by
    refine ⟨(n : ℚ) ^ 3, ?_⟩
    ring
  have hintRat : IsSquare ((negAux m n : ℤ) : ℚ) := by
    rw [hidentity]
    exact hs.mul hden
  have hint : IsSquare (negAux m n) :=
    Rat.isSquare_intCast_iff.mp hintRat
  apply negAux_not_isSquare_of_coprime m n
  · simpa [m, n] using v.reduced
  · exact hint

/-- A solution of the negative `h,k` branch would make its auxiliary value a
square.  This is the completed-square identity for the quadratic in `U`. -/
theorem negativeSquareclassRhs_isSquare_of_relation {U v : ℚ}
    (hrel : e1HKRelation (-2 * U) (-v ^ 2) = 0) :
    IsSquare (negativeSquareclassRhs v) := by
  refine ⟨2 * ((v ^ 2 + 1) * U - 1), ?_⟩
  calc
    negativeSquareclassRhs v =
        (2 * ((v ^ 2 + 1) * U - 1)) *
          (2 * ((v ^ 2 + 1) * U - 1)) -
        (v ^ 2 + 1) * e1HKRelation (-2 * U) (-v ^ 2) := by
          simp [negativeSquareclassRhs, e1HKRelation]
          ring
    _ = _ := by rw [hrel]; ring

/-- There are no rational points in the negative common-squareclass branch. -/
theorem e1_negative_squareclass_impossible (U v : ℚ) :
    e1HKRelation (-2 * U) (-v ^ 2) ≠ 0 := by
  intro hrel
  exact negativeSquareclassRhs_not_isSquare v
    (negativeSquareclassRhs_isSquare_of_relation hrel)

end

end Cuboid2
