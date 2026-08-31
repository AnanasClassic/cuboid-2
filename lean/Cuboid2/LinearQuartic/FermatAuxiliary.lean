import Mathlib.NumberTheory.FLT.Four
import Mathlib.Data.Rat.Sqrt

/-!
# Fermat descent auxiliaries for the specialized linear branch

Mathlib contains Fermat's descent for

`a⁴ + b⁴ = c²`.

The signed-square covers used by the Sharipov specialization also require
the companion difference theorem

`a⁴ - b⁴ = c²`.

This file proves that theorem by the same primitive-Pythagorean-triple
descent.  It then records the two fourth-power corollaries needed by the
sextic classifications.
-/

namespace Cuboid2

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A nontrivial integral solution of `a⁴ - b⁴ = c²`. -/
def Fermat4Sub (a b c : ℤ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ^ 4 - b ^ 4 = c ^ 2

namespace Fermat4Sub

/-- Scaling preserves and reflects nontrivial difference solutions. -/
theorem mul {a b c k : ℤ} (hk : k ≠ 0) :
    Fermat4Sub a b c ↔
      Fermat4Sub (k * a) (k * b) (k ^ 2 * c) := by
  unfold Fermat4Sub
  constructor <;> intro h
  · refine ⟨mul_ne_zero hk h.1, mul_ne_zero hk h.2.1,
      mul_ne_zero (pow_ne_zero 2 hk) h.2.2.1, ?_⟩
    calc
      (k * a) ^ 4 - (k * b) ^ 4 =
          k ^ 4 * (a ^ 4 - b ^ 4) := by ring
      _ = k ^ 4 * c ^ 2 := by rw [h.2.2.2]
      _ = (k ^ 2 * c) ^ 2 := by ring
  · refine ⟨right_ne_zero_of_mul h.1, right_ne_zero_of_mul h.2.1,
      right_ne_zero_of_mul h.2.2.1, ?_⟩
    apply (mul_left_cancel₀ (pow_ne_zero 4 hk))
    calc
      k ^ 4 * (a ^ 4 - b ^ 4) =
          (k * a) ^ 4 - (k * b) ^ 4 := by ring
      _ = (k ^ 2 * c) ^ 2 := h.2.2.2
      _ = k ^ 4 * c ^ 2 := by ring

/-- A solution is minimal when its first coordinate has least absolute
value among all nontrivial solutions. -/
def Minimal (a b c : ℤ) : Prop :=
  Fermat4Sub a b c ∧
    ∀ a₁ b₁ c₁ : ℤ, Fermat4Sub a₁ b₁ c₁ →
      Int.natAbs a ≤ Int.natAbs a₁

/-- Every nontrivial solution would have a minimal one. -/
theorem exists_minimal {a b c : ℤ} (h : Fermat4Sub a b c) :
    ∃ a₀ b₀ c₀, Minimal a₀ b₀ c₀ := by
  classical
  let S : Set ℕ :=
    {n | ∃ s : ℤ × ℤ × ℤ,
      Fermat4Sub s.1 s.2.1 s.2.2 ∧ n = Int.natAbs s.1}
  have hS : S.Nonempty := by
    refine ⟨Int.natAbs a, ?_⟩
    exact ⟨⟨a, b, c⟩, h, rfl⟩
  let m : ℕ := Nat.find hS
  obtain ⟨s, hs, hm⟩ := Nat.find_spec hS
  refine ⟨s.1, s.2.1, s.2.2, hs, ?_⟩
  intro a₁ b₁ c₁ h₁
  rw [← hm]
  apply Nat.find_min'
  exact ⟨⟨a₁, b₁, c₁⟩, h₁, rfl⟩

/-- The first two coordinates of a minimal solution are coprime. -/
theorem coprime_of_minimal {a b c : ℤ} (h : Minimal a b c) :
    IsCoprime a b := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  by_contra hab
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hab
  obtain ⟨a₁, rfl⟩ := Int.natCast_dvd.mpr hpa
  obtain ⟨b₁, rfl⟩ := Int.natCast_dvd.mpr hpb
  have hpc : (p : ℤ) ^ 2 ∣ c := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero, ← h.1.2.2.2]
    refine ⟨a₁ ^ 4 - b₁ ^ 4, ?_⟩
    ring
  obtain ⟨c₁, rfl⟩ := hpc
  have hsmall : Fermat4Sub a₁ b₁ c₁ :=
    (Fermat4Sub.mul (Int.natCast_ne_zero.mpr hp.ne_zero)).mpr h.1
  apply Nat.le_lt_asymm (h.2 _ _ _ hsmall)
  rw [Int.natAbs_mul, lt_mul_iff_one_lt_left, Int.natAbs_natCast]
  · exact hp.one_lt
  · exact Int.natAbs_pos.mpr hsmall.1

/-- Negating the first coordinate preserves minimality. -/
theorem neg_first_of_minimal {a b c : ℤ} (h : Minimal a b c) :
    Minimal (-a) b c := by
  refine ⟨?_, ?_⟩
  · rcases h.1 with ⟨ha, hb, hc, heq⟩
    refine ⟨neg_ne_zero.mpr ha, hb, hc, ?_⟩
    calc
      (-a) ^ 4 - b ^ 4 = a ^ 4 - b ^ 4 := by ring
      _ = c ^ 2 := heq
  · simpa using h.2

/-- A hypothetical solution can be chosen minimal with positive first
coordinate. -/
theorem exists_pos_minimal {a b c : ℤ} (h : Fermat4Sub a b c) :
    ∃ a₀ b₀ c₀, Minimal a₀ b₀ c₀ ∧ 0 < a₀ := by
  obtain ⟨a₀, b₀, c₀, hmin⟩ := exists_minimal h
  rcases lt_trichotomy 0 a₀ with ha | ha | ha
  · exact ⟨a₀, b₀, c₀, hmin, ha⟩
  · exact False.elim (hmin.1.1 ha.symm)
  · exact ⟨-a₀, b₀, c₀, neg_first_of_minimal hmin, neg_pos.mpr ha⟩

/-- The two legs in the Pythagorean triple attached to a primitive
difference solution are coprime. -/
theorem squareLeg_coprime
    {a b c : ℤ} (h : Fermat4Sub a b c) (hab : IsCoprime a b) :
    IsCoprime (b ^ 2) c := by
  have hba : IsCoprime (b ^ 2) (a ^ 4) := by
    exact hab.symm.pow
  have hdiff : IsCoprime (b ^ 2) (a ^ 4 - b ^ 4) := by
    have hadd := hba.add_mul_left_right (-(b ^ 2))
    simpa only [show a ^ 4 + b ^ 2 * -(b ^ 2) =
        a ^ 4 - b ^ 4 by ring] using hadd
  rw [h.2.2.2] at hdiff
  exact (IsCoprime.pow_right_iff (by norm_num : 0 < 2)).mp hdiff

/-- A minimal positive difference solution produces a smaller one. -/
theorem not_minimal {a b c : ℤ} (h : Minimal a b c) (ha : 0 < a) :
    False := by
  have hab : IsCoprime a b := coprime_of_minimal h
  have htriple : PythagoreanTriple (b ^ 2) c (a ^ 2) := by
    unfold PythagoreanTriple
    nlinarith [h.1.2.2.2]
  have hlegs : Int.gcd (b ^ 2) c = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (squareLeg_coprime h.1 hab)
  have hhyp : 0 < a ^ 2 := sq_pos_of_pos ha
  rcases htriple.even_odd_of_coprime hlegs with heven | hodd
  · -- The square leg is even.  Parametrize twice, then split a product
    -- of three pairwise-coprime factors into squares.
    have hswap : PythagoreanTriple c (b ^ 2) (a ^ 2) := htriple.symm
    have hswapGcd : Int.gcd c (b ^ 2) = 1 := by
      rw [Int.gcd_comm]
      exact hlegs
    obtain ⟨m, n, hc, hb, ha2, hmn, hpar, hm0⟩ :=
      hswap.coprime_classification' hswapGcd heven.2 hhyp
    have hmpos : 0 < m := by
      have hb0 : b ^ 2 ≠ 0 := pow_ne_zero 2 h.1.2.1
      by_contra hm
      have hmzero : m = 0 := le_antisymm (le_of_not_gt hm) hm0
      rw [hmzero] at hb
      have : b ^ 2 = 0 := by simpa using hb
      exact hb0 this
    have hnpos : 0 < n := by
      have hbpos : 0 < b ^ 2 := sq_pos_of_ne_zero h.1.2.1
      nlinarith [hb]
    have ha2eq : a ^ 2 = m ^ 2 + n ^ 2 := ha2
    have hmnTriple : PythagoreanTriple m n a := by
      unfold PythagoreanTriple
      nlinarith
    rcases hpar with hmeven | hneven
    · have hnodd : n % 2 = 1 := hmeven.2
      have hmnGcd : Int.gcd n m = 1 := by
        rw [Int.gcd_comm]
        exact hmn
      obtain ⟨r, s, hnEq, hmEq, haEq, hrs, _hparrs, hr0⟩ :=
        hmnTriple.symm.coprime_classification'
          hmnGcd hnodd ha
      have hrpos : 0 < r := by
        by_contra hr
        have hrzero : r = 0 := le_antisymm (le_of_not_gt hr) hr0
        rw [hrzero] at hmEq
        simp at hmEq
        nlinarith
      have hspos : 0 < s := by nlinarith [hmEq, hmpos]
      have hdiffpos : 0 < r ^ 2 - s ^ 2 := by nlinarith [hnEq, hnpos]
      have hbEven : 2 ∣ b := by
        apply @Int.Prime.dvd_pow' _ 2 _ Nat.prime_two
        rw [hb, mul_assoc]
        exact dvd_mul_right 2 (m * n)
      obtain ⟨b₀, hb₀⟩ := hbEven
      have hprod :
          b₀ ^ 2 = r * (s * (r ^ 2 - s ^ 2)) := by
        rw [hb₀, hmEq, hnEq] at hb
        nlinarith [hb]
      have hrsCoprime : IsCoprime r s :=
        Int.isCoprime_iff_gcd_eq_one.mpr hrs
      have hrDiff : IsCoprime r (r ^ 2 - s ^ 2) := by
        have hpow : IsCoprime r (s ^ 2) := hrsCoprime.pow_right
        have hadd := hpow.add_mul_left_right (-r)
        have hneg := hadd.neg_right
        simpa only [show -(s ^ 2 + r * -r) =
            r ^ 2 - s ^ 2 by ring] using hneg
      have hsDiff : IsCoprime s (r ^ 2 - s ^ 2) := by
        have hpow : IsCoprime s (r ^ 2) := hrsCoprime.symm.pow_right
        have hadd := hpow.add_mul_left_right (-s)
        simpa only [show r ^ 2 + s * -s =
            r ^ 2 - s ^ 2 by ring] using hadd
      have hrRest : IsCoprime r (s * (r ^ 2 - s ^ 2)) :=
        hrsCoprime.mul_right hrDiff
      obtain ⟨r₀, hrSq⟩ :=
        Int.sq_of_isCoprime hrRest hprod.symm
      have hrNotNeg : ¬r = -r₀ ^ 2 := by
        intro hneg
        rw [hneg] at hrpos
        exact (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg r₀))) hrpos
      have hrSq' : r = r₀ ^ 2 := Or.resolve_right hrSq hrNotNeg
      have hrestPos : 0 < s * (r ^ 2 - s ^ 2) :=
        mul_pos hspos hdiffpos
      obtain ⟨d, hdSq⟩ :=
        Int.sq_of_isCoprime hrRest.symm (by
          rw [mul_comm]
          exact hprod.symm)
      have hdNotNeg : ¬s * (r ^ 2 - s ^ 2) = -d ^ 2 := by
        intro hneg
        rw [hneg] at hrestPos
        exact (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg d))) hrestPos
      have hdSq' :
          s * (r ^ 2 - s ^ 2) = d ^ 2 :=
        Or.resolve_right hdSq hdNotNeg
      obtain ⟨s₀, hsSq⟩ :=
        Int.sq_of_isCoprime hsDiff hdSq'
      have hsNotNeg : ¬s = -s₀ ^ 2 := by
        intro hneg
        rw [hneg] at hspos
        exact (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg s₀))) hspos
      have hsSq' : s = s₀ ^ 2 := Or.resolve_right hsSq hsNotNeg
      obtain ⟨t₀, htSq⟩ :=
        Int.sq_of_isCoprime hsDiff.symm (by
          rw [mul_comm]
          exact hdSq')
      have htNotNeg : ¬r ^ 2 - s ^ 2 = -t₀ ^ 2 := by
        intro hneg
        rw [hneg] at hdiffpos
        exact (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg t₀))) hdiffpos
      have htSq' :
          r ^ 2 - s ^ 2 = t₀ ^ 2 :=
        Or.resolve_right htSq htNotNeg
      have hnew : Fermat4Sub r₀ s₀ t₀ := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro hz
          rw [hz] at hrSq'
          simp at hrSq'
          linarith
        · intro hz
          rw [hz] at hsSq'
          simp at hsSq'
          linarith
        · intro hz
          rw [hz] at htSq'
          simp at htSq'
          nlinarith [hdiffpos]
        · rw [← htSq', hrSq', hsSq']
          ring
      have hsmall : Int.natAbs r₀ < Int.natAbs a := by
        have hr₀abs : (Int.natAbs r₀ : ℤ) ≤ r₀ ^ 2 :=
          Int.natAbs_le_self_sq r₀
        have hrlt : r₀ ^ 2 < a := by
          rw [← hrSq']
          nlinarith [haEq, hspos]
        apply Int.ofNat_lt.mp
        rw [Int.natAbs_of_nonneg (le_of_lt ha)]
        exact lt_of_le_of_lt hr₀abs hrlt
      exact (Nat.not_lt_of_ge (h.2 _ _ _ hnew)) hsmall
    · have hmodd : m % 2 = 1 := hneven.1
      obtain ⟨r, s, hmEq, hnEq, haEq, hrs, _hparrs, hr0⟩ :=
        hmnTriple.coprime_classification' hmn hmodd ha
      have hrpos : 0 < r := by
        by_contra hr
        have hrzero : r = 0 := le_antisymm (le_of_not_gt hr) hr0
        rw [hrzero] at hnEq
        simp at hnEq
        nlinarith
      have hspos : 0 < s := by nlinarith [hnEq, hnpos]
      have hdiffpos : 0 < r ^ 2 - s ^ 2 := by nlinarith [hmEq, hmpos]
      have hbEven : 2 ∣ b := by
        apply @Int.Prime.dvd_pow' _ 2 _ Nat.prime_two
        rw [hb, mul_assoc]
        exact dvd_mul_right 2 (m * n)
      obtain ⟨b₀, hb₀⟩ := hbEven
      have hprod :
          b₀ ^ 2 = r * (s * (r ^ 2 - s ^ 2)) := by
        rw [hb₀, hmEq, hnEq] at hb
        nlinarith [hb]
      have hrsCoprime : IsCoprime r s :=
        Int.isCoprime_iff_gcd_eq_one.mpr hrs
      have hrDiff : IsCoprime r (r ^ 2 - s ^ 2) := by
        have hpow : IsCoprime r (s ^ 2) := hrsCoprime.pow_right
        have hadd := hpow.add_mul_left_right (-r)
        have hneg := hadd.neg_right
        simpa only [show -(s ^ 2 + r * -r) =
            r ^ 2 - s ^ 2 by ring] using hneg
      have hsDiff : IsCoprime s (r ^ 2 - s ^ 2) := by
        have hpow : IsCoprime s (r ^ 2) := hrsCoprime.symm.pow_right
        have hadd := hpow.add_mul_left_right (-s)
        simpa only [show r ^ 2 + s * -s =
            r ^ 2 - s ^ 2 by ring] using hadd
      have hrRest : IsCoprime r (s * (r ^ 2 - s ^ 2)) :=
        hrsCoprime.mul_right hrDiff
      obtain ⟨r₀, hrSq⟩ :=
        Int.sq_of_isCoprime hrRest hprod.symm
      have hrSq' : r = r₀ ^ 2 := by
        rcases hrSq with hsq | hsq
        · exact hsq
        · exfalso
          rw [hsq] at hrpos
          exact (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg r₀))) hrpos
      obtain ⟨d, hdSq⟩ :=
        Int.sq_of_isCoprime hrRest.symm (by
          rw [mul_comm]
          exact hprod.symm)
      have hdSq' : s * (r ^ 2 - s ^ 2) = d ^ 2 := by
        rcases hdSq with hsq | hsq
        · exact hsq
        · exfalso
          have hrestPos : 0 < s * (r ^ 2 - s ^ 2) :=
            mul_pos hspos hdiffpos
          rw [hsq] at hrestPos
          exact (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg d))) hrestPos
      obtain ⟨s₀, hsSq⟩ :=
        Int.sq_of_isCoprime hsDiff hdSq'
      have hsSq' : s = s₀ ^ 2 := by
        rcases hsSq with hsq | hsq
        · exact hsq
        · exfalso
          rw [hsq] at hspos
          exact (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg s₀))) hspos
      obtain ⟨t₀, htSq⟩ :=
        Int.sq_of_isCoprime hsDiff.symm (by
          rw [mul_comm]
          exact hdSq')
      have htSq' : r ^ 2 - s ^ 2 = t₀ ^ 2 := by
        rcases htSq with hsq | hsq
        · exact hsq
        · exfalso
          rw [hsq] at hdiffpos
          exact (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg t₀))) hdiffpos
      have hnew : Fermat4Sub r₀ s₀ t₀ := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro hz
          rw [hz] at hrSq'
          simp at hrSq'
          linarith
        · intro hz
          rw [hz] at hsSq'
          simp at hsSq'
          linarith
        · intro hz
          rw [hz] at htSq'
          simp at htSq'
          nlinarith [hdiffpos]
        · rw [← htSq', hrSq', hsSq']
          ring
      have hsmall : Int.natAbs r₀ < Int.natAbs a := by
        have hr₀abs : (Int.natAbs r₀ : ℤ) ≤ r₀ ^ 2 :=
          Int.natAbs_le_self_sq r₀
        have hrlt : r₀ ^ 2 < a := by
          rw [← hrSq']
          nlinarith [haEq, hspos]
        apply Int.ofNat_lt.mp
        rw [Int.natAbs_of_nonneg (le_of_lt ha)]
        exact lt_of_le_of_lt hr₀abs hrlt
      exact (Nat.not_lt_of_ge (h.2 _ _ _ hnew)) hsmall
  · -- The square leg is odd.  One parametrization already gives a
    -- smaller difference solution.
    obtain ⟨m, n, hb, hc, ha2, _hmn, _hpar, hm0⟩ :=
      htriple.coprime_classification' hlegs hodd.1 hhyp
    have hmpos : 0 < m := by
      by_contra hm
      have hmzero : m = 0 := le_antisymm (le_of_not_gt hm) hm0
      rw [hmzero] at hc
      simp at hc
      exact h.1.2.2.1 (by nlinarith)
    have hn0 : n ≠ 0 := by
      intro hn
      rw [hn] at hc
      simp at hc
      exact h.1.2.2.1 hc
    have hnSqPos : 0 < n ^ 2 := sq_pos_of_ne_zero hn0
    have hnew : Fermat4Sub m n (a * b) := by
      refine ⟨ne_of_gt hmpos, hn0, mul_ne_zero h.1.1 h.1.2.1, ?_⟩
      calc
        m ^ 4 - n ^ 4 =
            (m ^ 2 + n ^ 2) * (m ^ 2 - n ^ 2) := by ring
        _ = a ^ 2 * b ^ 2 := by rw [← ha2, ← hb]
        _ = (a * b) ^ 2 := by ring
    have hmlt : Int.natAbs m < Int.natAbs a := by
      have hmabs : (Int.natAbs m : ℤ) = m := by
        exact Int.natAbs_of_nonneg hm0
      have haabs : (Int.natAbs a : ℤ) = a :=
        Int.natAbs_of_nonneg (le_of_lt ha)
      apply Int.ofNat_lt.mp
      rw [hmabs, haabs]
      nlinarith [ha2, hnSqPos]
    exact (Nat.not_lt_of_ge (h.2 _ _ _ hnew)) hmlt

end Fermat4Sub

/-- Fermat's difference theorem: a nontrivial fourth-power difference
cannot be a square. -/
theorem not_fermat_4_sub {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) :
    a ^ 4 - b ^ 4 ≠ c ^ 2 := by
  intro heq
  obtain ⟨a₀, b₀, c₀, hmin, ha₀⟩ :=
    Fermat4Sub.exists_pos_minimal ⟨ha, hb, hc, heq⟩
  exact Fermat4Sub.not_minimal hmin ha₀

/-- Two is not a square in the rationals. -/
theorem rat_two_not_square : ¬IsSquare (2 : ℚ) := by
  intro hsquare
  obtain ⟨a, ha⟩ :=
    Rat.isSquare_intCast_iff.mp hsquare
  have haEven : (2 : ℤ) ∣ a := by
    apply @Int.Prime.dvd_pow' _ 2 _ Nat.prime_two
    rw [pow_two, ← ha]
  obtain ⟨b, hb⟩ := haEven
  have hfour : (4 : ℤ) ∣ 2 := by
    refine ⟨b * b, ?_⟩
    calc
      (2 : ℤ) = a * a := ha
      _ = 4 * (b * b) := by rw [hb]; ring
  norm_num at hfour

/-- The equation `x⁴ + y⁴ = 2z²` has only the diagonal integral
solutions. -/
theorem fourth_add_fourth_eq_two_square
    {x y z : ℤ} (h : x ^ 4 + y ^ 4 = 2 * z ^ 2) :
    x ^ 2 = y ^ 2 := by
  by_contra hxy
  have hx0 : x ≠ 0 := by
    intro hx
    have hy0 : y ≠ 0 := by
      intro hy
      apply hxy
      simp [hx, hy]
    have hz0 : z ≠ 0 := by
      intro hz
      rw [hx, hz] at h
      norm_num at h
      exact hy0 h
    have hsquare : IsSquare (2 : ℚ) := by
      refine ⟨(y : ℚ) ^ 2 / (z : ℚ), ?_⟩
      have hq : (y : ℚ) ^ 4 = 2 * (z : ℚ) ^ 2 := by
        exact_mod_cast (by simpa [hx] using h)
      field_simp [show (z : ℚ) ≠ 0 by exact_mod_cast hz0]
      nlinarith [hq]
    exact rat_two_not_square hsquare
  have hy0 : y ≠ 0 := by
    intro hy
    have hz0 : z ≠ 0 := by
      intro hz
      rw [hy, hz] at h
      norm_num at h
      exact hx0 h
    have hsquare : IsSquare (2 : ℚ) := by
      refine ⟨(x : ℚ) ^ 2 / (z : ℚ), ?_⟩
      have hq : (x : ℚ) ^ 4 = 2 * (z : ℚ) ^ 2 := by
        exact_mod_cast (by simpa [hy] using h)
      field_simp [show (z : ℚ) ≠ 0 by exact_mod_cast hz0]
      nlinarith [hq]
    exact rat_two_not_square hsquare
  let d : ℤ := z ^ 2 - y ^ 4
  have hdiff :
      z ^ 4 - (x * y) ^ 4 = d ^ 2 := by
    have hid :
        (z ^ 4 - (x * y) ^ 4) - d ^ 2 =
          y ^ 4 * (2 * z ^ 2 - (x ^ 4 + y ^ 4)) := by
      dsimp only [d]
      ring
    rw [h] at hid
    norm_num at hid
    linarith
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz] at h
    have hx4 : 0 ≤ x ^ 4 := by positivity
    have hy4 : 0 ≤ y ^ 4 := by positivity
    have hx4zero : x ^ 4 = 0 := by nlinarith
    exact hx0 ((pow_eq_zero_iff (by norm_num : 4 ≠ 0)).mp hx4zero)
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
  have hd0 : d ≠ 0 := by
    intro hd0
    have hdEq : x ^ 4 = y ^ 4 := by
      dsimp only [d] at hd0
      nlinarith [h, hd0]
    have hsquares : (x ^ 2) ^ 2 = (y ^ 2) ^ 2 := by
      nlinarith [hdEq]
    exact hxy (sq_eq_sq_iff_eq_or_eq_neg.mp hsquares |>.resolve_right
      (by
        intro hneg
        have hx2 : x ^ 2 = 0 := by
          nlinarith [sq_nonneg x, sq_nonneg y]
        exact hx0 ((pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hx2)))
  exact not_fermat_4_sub hz0 hxy0 hd0 hdiff

end

end Cuboid2
