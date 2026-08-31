import Cuboid2.FiveFive.ResultantCritical
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Projective first-contact transport for the `5+5` fibre family

The compact projective boundary prevents affine roots from escaping to
infinity. A first new root along a critical-free parameter segment is a local
minimum, hence also a derivative root, contradicting the checked Bézout
certificate.
-/

namespace Cuboid2

open Set Polynomial

noncomputable section

/-- Compact affine/projective boundary used to retain roots escaping to infinity. -/
def projectiveDiamond : Set (ℝ × ℝ) :=
  (Icc (-1) 1 ×ˢ Icc 0 1) ∩ {z | |z.1| + z.2 = 1}

/-- The standard compactification of a real affine point. -/
def projectivePoint (y : ℝ) : ℝ × ℝ :=
  (y / (|y| + 1), 1 / (|y| + 1))

/-- The projective diamond is compact as a closed subset of a compact box. -/
theorem projectiveDiamond_compact : IsCompact projectiveDiamond := by
  apply (isCompact_Icc.prod isCompact_Icc).inter_right
  exact isClosed_eq
    ((continuous_fst.abs).add continuous_snd)
    continuous_const

/-- Every compactified affine point lies on the projective diamond. -/
theorem projectivePoint_mem_diamond (y : ℝ) :
    projectivePoint y ∈ projectiveDiamond := by
  have hr : 0 < |y| + 1 := by positivity
  have habs : |y| / (|y| + 1) < 1 := by
    apply (div_lt_one hr).2
    linarith [abs_nonneg y]
  have hcoord : |y / (|y| + 1)| = |y| / (|y| + 1) := by
    rw [abs_div, abs_of_pos hr]
  have hu : |y / (|y| + 1)| ≤ 1 := by
    rw [hcoord]
    exact habs.le
  constructor
  · constructor
    · exact (abs_le.mp hu)
    · constructor
      · change 0 ≤ 1 / (|y| + 1)
        positivity
      · change 1 / (|y| + 1) ≤ 1
        exact (div_le_one hr).2 (by linarith [abs_nonneg y])
  · change |y / (|y| + 1)| + 1 / (|y| + 1) = 1
    rw [hcoord]
    field_simp

/-- An affine point has nonzero homogeneous denominator after compactification. -/
@[simp] theorem projectivePoint_second_ne_zero (y : ℝ) :
    (projectivePoint y).2 ≠ 0 := by
  simp [projectivePoint]
  positivity

/-- Dehomogenizing a compactified affine point recovers its original coordinate. -/
theorem projectivePoint_ratio (y : ℝ) :
    (projectivePoint y).1 / (projectivePoint y).2 = y := by
  simp [projectivePoint]
  field_simp

/--
A positive even-degree polynomial fibre cannot acquire an affine real root
along a critical-free segment from a strictly positive sample fibre.
-/
theorem no_root_along_critical_free_segment
    (F D : ℝ → ℝ → ℝ) (H : ℝ → ℝ → ℝ → ℝ)
    (q s : ℝ) (hq : 0 < q) (hs : 0 < s)
    (hsample : ∀ y, 0 < F q y)
    (hHcontinuous : Continuous (fun p : ℝ × ℝ × ℝ =>
      H p.1 p.2.1 p.2.2))
    (hHatOne : ∀ t y, H t y 1 = F t y)
    (hHscale : ∀ t u v, v ≠ 0 → H t u v = v ^ 16 * F t (u / v))
    (hHatZero : ∀ t u, H t u 0 = t ^ 8 * u ^ 16)
    (hderiv : ∀ t y, HasDerivAt (F t) (D t y) y)
    (hnoMultiple :
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ y,
        ¬ (F (q + t * (s - q)) y = 0 ∧ D (q + t * (s - q)) y = 0)) :
    ∀ y, F s y ≠ 0 := by
  let a : ℝ → ℝ := fun t => q + t * (s - q)
  have ha_zero : a 0 = q := by simp [a]
  have ha_one : a 1 = s := by simp [a]
  have ha_pos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 < a t := by
    have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    rcases ht.1.eq_or_lt with rfl | htpos
    · simpa [a] using hq
    · have hleft : 0 ≤ (1 - t) * q := mul_nonneg ht' hq.le
      have hright : 0 < t * s := mul_pos htpos hs
      rw [show a t = (1 - t) * q + t * s by simp [a]; ring]
      linarith
  have hFcontinuous (y : ℝ) : Continuous (fun t => F (a t) y) := by
    have hcomp := hHcontinuous.comp
      (show Continuous (fun t : ℝ => (a t, (y, 1))) by
        dsimp [a]
        fun_prop)
    have hcomp' : Continuous (fun t => H (a t) y 1) := by
      change Continuous ((fun p : ℝ × (ℝ × ℝ) =>
        H p.1 p.2.1 p.2.2) ∘ fun t : ℝ => (a t, (y, 1)))
      exact hcomp
    simpa only [hHatOne] using hcomp'
  have hsampleProjective (z : ℝ × ℝ) (hz : z ∈ projectiveDiamond) :
      H q z.1 z.2 ≠ 0 := by
    rcases eq_or_ne z.2 0 with hv | hv
    · have huabs : |z.1| = 1 := by
        have hzsum := hz.2
        change |z.1| + z.2 = 1 at hzsum
        simpa [hv] using hzsum
      have hu : z.1 ≠ 0 := by
        intro hu
        simp [hu] at huabs
      rw [hv, hHatZero]
      exact mul_ne_zero (pow_ne_zero 8 (ne_of_gt hq)) (pow_ne_zero 16 hu)
    · rw [hHscale q z.1 z.2 hv]
      exact mul_ne_zero (pow_ne_zero 16 hv) (ne_of_gt (hsample _))
  let K : Set (ℝ × (ℝ × ℝ)) := Icc (0 : ℝ) 1 ×ˢ projectiveDiamond
  let Z : Set (ℝ × (ℝ × ℝ)) :=
    K ∩ {p | H (a p.1) p.2.1 p.2.2 = 0}
  have hKcompact : IsCompact K :=
    isCompact_Icc.prod projectiveDiamond_compact
  have hzeroClosed :
      IsClosed {p : ℝ × (ℝ × ℝ) | H (a p.1) p.2.1 p.2.2 = 0} := by
    apply isClosed_eq
    · have hcomp := hHcontinuous.comp
        (show Continuous (fun p : ℝ × (ℝ × ℝ) =>
            (a p.1, (p.2.1, p.2.2))) by
          dsimp [a]
          fun_prop)
      change Continuous ((fun p : ℝ × (ℝ × ℝ) =>
        H p.1 p.2.1 p.2.2) ∘
          fun p : ℝ × (ℝ × ℝ) => (a p.1, (p.2.1, p.2.2)))
      exact hcomp
    · fun_prop
  have hZcompact : IsCompact Z :=
    hKcompact.inter_right hzeroClosed
  let T : Set ℝ := Prod.fst '' Z
  have hTcompact : IsCompact T :=
    hZcompact.image continuous_fst
  intro y hy
  have htargetZ : (1, projectivePoint y) ∈ Z := by
    constructor
    · exact ⟨by norm_num, projectivePoint_mem_diamond y⟩
    · change H (a 1) (projectivePoint y).1 (projectivePoint y).2 = 0
      rw [hHscale (a 1) (projectivePoint y).1 (projectivePoint y).2
          (projectivePoint_second_ne_zero y),
        projectivePoint_ratio, ha_one, hy, mul_zero]
  have hTnonempty : T.Nonempty :=
    ⟨1, ⟨(1, projectivePoint y), htargetZ, rfl⟩⟩
  obtain ⟨t, htT, htmin⟩ :=
    hTcompact.exists_isMinOn hTnonempty continuous_id.continuousOn
  rcases htT with ⟨⟨t', z⟩, htzZ, ht'eq⟩
  change t' = t at ht'eq
  subst t'
  have htIcc : t ∈ Icc (0 : ℝ) 1 := htzZ.1.1
  have hzDiamond : z ∈ projectiveDiamond := htzZ.1.2
  have hHzero : H (a t) z.1 z.2 = 0 := htzZ.2
  have ht_ne_zero : t ≠ 0 := by
    intro ht
    subst t
    exact hsampleProjective z hzDiamond (by simpa [ha_zero] using hHzero)
  have ht_pos : 0 < t := lt_of_le_of_ne htIcc.1 (Ne.symm ht_ne_zero)
  have hzv : z.2 ≠ 0 := by
    intro hv
    have huabs : |z.1| = 1 := by
      have hzsum := hzDiamond.2
      change |z.1| + z.2 = 1 at hzsum
      simpa [hv] using hzsum
    have hu : z.1 ≠ 0 := by
      intro hu
      simp [hu] at huabs
    rw [hv, hHatZero] at hHzero
    exact
      (mul_ne_zero (pow_ne_zero 8 (ne_of_gt (ha_pos htIcc)))
        (pow_ne_zero 16 hu)) hHzero
  let ystar : ℝ := z.1 / z.2
  have hrootstar : F (a t) ystar = 0 := by
    rw [hHscale (a t) z.1 z.2 hzv] at hHzero
    exact (mul_eq_zero.mp hHzero).resolve_left (pow_ne_zero 16 hzv)
  have hnonneg (w : ℝ) : 0 ≤ F (a t) w := by
    by_contra hw
    have hwneg : F (a t) w < 0 := lt_of_not_ge hw
    have hzeroMem : (0 : ℝ) ∈ Icc (F (a t) w) (F (a 0) w) := by
      constructor
      · exact hwneg.le
      · rw [ha_zero]
        exact (hsample w).le
    have ht0 : 0 ≤ t := htIcc.1
    rcases intermediate_value_Icc' ht0 (hFcontinuous w).continuousOn hzeroMem with
      ⟨r, hrIcc, hrzero⟩
    have hrt : r < t := by
      apply lt_of_le_of_ne hrIcc.2
      intro hrt
      subst r
      linarith
    have hr01 : r ∈ Icc (0 : ℝ) 1 :=
      ⟨hrIcc.1, hrIcc.2.trans htIcc.2⟩
    have hrZ : (r, projectivePoint w) ∈ Z := by
      change F (a r) w = 0 at hrzero
      constructor
      · exact ⟨hr01, projectivePoint_mem_diamond w⟩
      · change H (a r) (projectivePoint w).1 (projectivePoint w).2 = 0
        rw [hHscale (a r) (projectivePoint w).1 (projectivePoint w).2
            (projectivePoint_second_ne_zero w),
          projectivePoint_ratio, hrzero, mul_zero]
    have hrT : r ∈ T :=
      ⟨(r, projectivePoint w), hrZ, rfl⟩
    exact (not_le_of_gt hrt) (htmin hrT)
  have hlocal : IsLocalMin (F (a t)) ystar := by
    apply IsMinOn.isLocalMin (s := Set.univ)
    · intro w _
      rw [hrootstar]
      exact hnonneg w
    · exact Filter.univ_mem
  have hDzero : D (a t) ystar = 0 :=
    hlocal.hasDerivAt_eq_zero (hderiv (a t) ystar)
  exact hnoMultiple t htIcc ystar ⟨hrootstar, hDzero⟩

/--
Specialization of projective first contact to the `5+5` family. It requires
only that the straight parameter segment avoid `1` and both critical factors.
-/
theorem fiveFiveResultantFactorReal_ne_zero_of_segment
    (q s : ℝ) (hq : 0 < q) (hs : 0 < s)
    (hsample : ∀ y, 0 < fiveFiveResultantFactorReal q y)
    (hcritical :
      ∀ t ∈ Icc (0 : ℝ) 1,
        q + t * (s - q) ≠ 1 ∧
        fiveFiveDiscriminantP6PolyReal.eval (q + t * (s - q)) ≠ 0 ∧
        fiveFiveDiscriminantP28PolyReal.eval (q + t * (s - q)) ≠ 0) :
    ∀ y, fiveFiveResultantFactorReal s y ≠ 0 := by
  apply no_root_along_critical_free_segment
    fiveFiveResultantFactorReal fiveFiveResultantFactorDerivativeReal
    fiveFiveResultantFactorHomogeneousReal q s hq hs hsample
    continuous_fiveFiveResultantFactorHomogeneousReal
    fiveFiveResultantFactorHomogeneousReal_at_one
    fiveFiveResultantFactorHomogeneousReal_scale
    fiveFiveResultantFactorHomogeneousReal_at_zero
  · intro t y
    simpa only [eval_fiveFiveResultantFactorPolyReal,
      eval_derivative_fiveFiveResultantFactorPolyReal] using
        (fiveFiveResultantFactorPolyReal t).hasDerivAt y
  · intro t ht y
    simpa only [eval_fiveFiveResultantFactorPolyReal,
      eval_derivative_fiveFiveResultantFactorPolyReal] using
        (fiveFiveResultantFactorPolyReal_no_multiple_root
          (by
            have hq' : 0 ≤ (1 - t) * q :=
              mul_nonneg (sub_nonneg.mpr ht.2) hq.le
            have hs' : 0 ≤ t * s := mul_nonneg ht.1 hs.le
            have hsum : 0 < (1 - t) * q + t * s := by
              rcases ht.1.eq_or_lt with rfl | htpos
              · simpa using hq
              · have : 0 < t * s := mul_pos htpos hs
                linarith
            rw [show q + t * (s - q) = (1 - t) * q + t * s by ring]
            exact hsum)
          (hcritical t ht).1 (hcritical t ht).2.1
          (hcritical t ht).2.2 y)

/-- The lower positive root of the degree-six critical factor. -/
def fiveFiveP6LowCut : ℝ :=
  fiveFiveDiscriminantP6_existsUnique_low_root.exists.choose

/-- The first positive root of the degree-twenty-eight critical factor. -/
def fiveFiveP28FirstCut : ℝ :=
  fiveFiveDiscriminantP28_existsUnique_first_root.exists.choose

/-- The second positive root of the degree-twenty-eight critical factor. -/
def fiveFiveP28SecondCut : ℝ :=
  fiveFiveDiscriminantP28_existsUnique_second_root.exists.choose

/-- The third positive root of the degree-twenty-eight critical factor. -/
def fiveFiveP28ThirdCut : ℝ :=
  fiveFiveDiscriminantP28_existsUnique_third_root.exists.choose

/-- The upper positive root of the degree-six critical factor. -/
def fiveFiveP6HighCut : ℝ :=
  fiveFiveDiscriminantP6_existsUnique_high_root.exists.choose

theorem fiveFiveP6LowCut_spec :
    fiveFiveP6LowCut ∈ Icc (31 / 1000) (32 / 1000) ∧
      fiveFiveDiscriminantP6PolyReal.eval fiveFiveP6LowCut = 0 :=
  fiveFiveDiscriminantP6_existsUnique_low_root.exists.choose_spec

theorem fiveFiveP28FirstCut_spec :
    fiveFiveP28FirstCut ∈ Icc (47 / 100) (471 / 1000) ∧
      fiveFiveDiscriminantP28PolyReal.eval fiveFiveP28FirstCut = 0 :=
  fiveFiveDiscriminantP28_existsUnique_first_root.exists.choose_spec

theorem fiveFiveP28SecondCut_spec :
    fiveFiveP28SecondCut ∈ Icc (786 / 25) (629 / 20) ∧
      fiveFiveDiscriminantP28PolyReal.eval fiveFiveP28SecondCut = 0 :=
  fiveFiveDiscriminantP28_existsUnique_second_root.exists.choose_spec

theorem fiveFiveP28ThirdCut_spec :
    fiveFiveP28ThirdCut ∈ Icc (1583 / 50) (3167 / 100) ∧
      fiveFiveDiscriminantP28PolyReal.eval fiveFiveP28ThirdCut = 0 :=
  fiveFiveDiscriminantP28_existsUnique_third_root.exists.choose_spec

theorem fiveFiveP6HighCut_spec :
    fiveFiveP6HighCut ∈ Icc (159 / 5) (319 / 10) ∧
      fiveFiveDiscriminantP6PolyReal.eval fiveFiveP6HighCut = 0 :=
  fiveFiveDiscriminantP6_existsUnique_high_root.exists.choose_spec

/-- Exact order of the five positive critical roots and the exceptional point `1`. -/
theorem fiveFive_critical_cut_order :
    0 < fiveFiveP6LowCut ∧
    fiveFiveP6LowCut < fiveFiveP28FirstCut ∧
    fiveFiveP28FirstCut < 1 ∧
    1 < fiveFiveP28SecondCut ∧
    fiveFiveP28SecondCut < fiveFiveP28ThirdCut ∧
    fiveFiveP28ThirdCut < fiveFiveP6HighCut := by
  rcases fiveFiveP6LowCut_spec with ⟨hlow, _⟩
  rcases fiveFiveP28FirstCut_spec with ⟨hfirst, _⟩
  rcases fiveFiveP28SecondCut_spec with ⟨hsecond, _⟩
  rcases fiveFiveP28ThirdCut_spec with ⟨hthird, _⟩
  rcases fiveFiveP6HighCut_spec with ⟨hhigh, _⟩
  norm_num at hlow hfirst hsecond hthird hhigh
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- The seven rational samples lie in the seven complementary real cells. -/
theorem fiveFive_sample_real_parameter_cells :
    (1 / 100 : ℝ) ∈ Ioo 0 fiveFiveP6LowCut ∧
    (1 / 5 : ℝ) ∈ Ioo fiveFiveP6LowCut fiveFiveP28FirstCut ∧
    (4 / 5 : ℝ) ∈ Ioo fiveFiveP28FirstCut 1 ∧
    (2 : ℝ) ∈ Ioo 1 fiveFiveP28SecondCut ∧
    (63 / 2 : ℝ) ∈ Ioo fiveFiveP28SecondCut fiveFiveP28ThirdCut ∧
    (317 / 10 : ℝ) ∈ Ioo fiveFiveP28ThirdCut fiveFiveP6HighCut ∧
    (fiveFiveP6HighCut : ℝ) < 40 := by
  rcases fiveFiveP6LowCut_spec with ⟨hlow, _⟩
  rcases fiveFiveP28FirstCut_spec with ⟨hfirst, _⟩
  rcases fiveFiveP28SecondCut_spec with ⟨hsecond, _⟩
  rcases fiveFiveP28ThirdCut_spec with ⟨hthird, _⟩
  rcases fiveFiveP6HighCut_spec with ⟨hhigh, _⟩
  norm_num at hlow hfirst hsecond hthird hhigh
  constructor
  · constructor <;> nlinarith
  constructor
  · constructor <;> nlinarith
  constructor
  · constructor <;> nlinarith
  constructor
  · constructor <;> nlinarith
  constructor
  · constructor <;> nlinarith
  constructor
  · constructor <;> nlinarith
  · nlinarith

/-- Every positive real root of `P6` is one of its two named cuts. -/
theorem fiveFiveDiscriminantP6_root_eq_cut
    {x : ℝ} (hx : 0 < x)
    (hroot : fiveFiveDiscriminantP6PolyReal.eval x = 0) :
    x = fiveFiveP6LowCut ∨ x = fiveFiveP6HighCut := by
  rcases fiveFiveDiscriminantP6_positive_root_mem_brackets hx hroot with
    hlow | hhigh
  · left
    exact fiveFiveDiscriminantP6_existsUnique_low_root.unique
      ⟨hlow, hroot⟩ fiveFiveP6LowCut_spec
  · right
    exact fiveFiveDiscriminantP6_existsUnique_high_root.unique
      ⟨hhigh, hroot⟩ fiveFiveP6HighCut_spec

/-- Every positive real root of `P28` is one of its three named cuts. -/
theorem fiveFiveDiscriminantP28_root_eq_cut
    {x : ℝ} (hx : 0 < x)
    (hroot : fiveFiveDiscriminantP28PolyReal.eval x = 0) :
    x = fiveFiveP28FirstCut ∨
      x = fiveFiveP28SecondCut ∨ x = fiveFiveP28ThirdCut := by
  rcases fiveFiveDiscriminantP28_positive_root_mem_brackets hx hroot with
    hfirst | hsecond | hthird
  · exact Or.inl
      (fiveFiveDiscriminantP28_existsUnique_first_root.unique
        ⟨hfirst, hroot⟩ fiveFiveP28FirstCut_spec)
  · exact Or.inr (Or.inl
      (fiveFiveDiscriminantP28_existsUnique_second_root.unique
        ⟨hsecond, hroot⟩ fiveFiveP28SecondCut_spec))
  · exact Or.inr (Or.inr
      (fiveFiveDiscriminantP28_existsUnique_third_root.unique
        ⟨hthird, hroot⟩ fiveFiveP28ThirdCut_spec))

/-- A convex parameter segment stays in any open interval containing both endpoints. -/
theorem affine_segment_mem_Ioo
    {l r q s t : ℝ} (hq : q ∈ Ioo l r) (hs : s ∈ Ioo l r)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    q + t * (s - q) ∈ Ioo l r := by
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hform :
      q + t * (s - q) = (1 - t) * q + t * s := by ring
  rw [hform]
  constructor
  · rcases ht.1.eq_or_lt with rfl | htpos
    · simpa using hq.1
    · have hleft : 0 ≤ (1 - t) * (q - l) :=
        mul_nonneg ht' (sub_nonneg.mpr hq.1.le)
      have hright : 0 < t * (s - l) :=
        mul_pos htpos (sub_pos.mpr hs.1)
      nlinarith
  · rcases ht.1.eq_or_lt with rfl | htpos
    · simpa using hq.2
    · have hleft : 0 ≤ (1 - t) * (r - q) :=
        mul_nonneg ht' (sub_nonneg.mpr hq.2.le)
      have hright : 0 < t * (r - s) :=
        mul_pos htpos (sub_pos.mpr hs.2)
      nlinarith

/-- A convex segment stays strictly above a common lower bound. -/
theorem affine_segment_gt
    {l q s t : ℝ} (hq : l < q) (hs : l < s)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    l < q + t * (s - q) := by
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  rcases ht.1.eq_or_lt with rfl | htpos
  · simpa using hq
  · have hleft : 0 ≤ (1 - t) * (q - l) :=
      mul_nonneg ht' (sub_nonneg.mpr hq.le)
    have hright : 0 < t * (s - l) :=
      mul_pos htpos (sub_pos.mpr hs)
    rw [show q + t * (s - q) = (1 - t) * q + t * s by ring]
    nlinarith

/--
Positive parameters away from the six named cuts and `1` avoid every factor
in the critical-locus certificate.
-/
theorem fiveFive_critical_free_of_ne_cuts
    {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1)
    (hlow : x ≠ fiveFiveP6LowCut)
    (hfirst : x ≠ fiveFiveP28FirstCut)
    (hsecond : x ≠ fiveFiveP28SecondCut)
    (hthird : x ≠ fiveFiveP28ThirdCut)
    (hhigh : x ≠ fiveFiveP6HighCut) :
    x ≠ 1 ∧ fiveFiveDiscriminantP6PolyReal.eval x ≠ 0 ∧
      fiveFiveDiscriminantP28PolyReal.eval x ≠ 0 := by
  refine ⟨hx1, ?_, ?_⟩
  · intro hroot
    rcases fiveFiveDiscriminantP6_root_eq_cut hx hroot with h | h
    · exact hlow h
    · exact hhigh h
  · intro hroot
    rcases fiveFiveDiscriminantP28_root_eq_cut hx hroot with h | h | h
    · exact hfirst h
    · exact hsecond h
    · exact hthird h

/-- Rational parameters remain nonroots of `P6` after casting to `ℝ`. -/
theorem fiveFiveDiscriminantP6PolyReal_ratCast_ne_zero (s : ℚ) :
    fiveFiveDiscriminantP6PolyReal.eval (s : ℝ) ≠ 0 := by
  intro hroot
  apply fiveFiveDiscriminantP6_ne_zero s
  have hcast : (fiveFiveDiscriminantP6 s : ℝ) = 0 := by
    simpa [fiveFiveDiscriminantP6, eval_fiveFiveDiscriminantP6PolyReal] using hroot
  exact_mod_cast hcast

/-- Rational parameters remain nonroots of `P28` after casting to `ℝ`. -/
theorem fiveFiveDiscriminantP28PolyReal_ratCast_ne_zero (s : ℚ) :
    fiveFiveDiscriminantP28PolyReal.eval (s : ℝ) ≠ 0 := by
  intro hroot
  apply fiveFiveDiscriminantP28_ne_zero s
  have hcast : (fiveFiveDiscriminantP28 s : ℝ) = 0 := by
    simpa [fiveFiveDiscriminantP28, fiveFiveDiscriminantP28PolyReal] using hroot
  exact_mod_cast hcast

/-- The first complementary parameter cell is critical-free. -/
theorem fiveFive_critical_free_below_p6_low
    {x : ℝ} (hx0 : 0 < x) (hx : x < fiveFiveP6LowCut) :
    x ≠ 1 ∧ fiveFiveDiscriminantP6PolyReal.eval x ≠ 0 ∧
      fiveFiveDiscriminantP28PolyReal.eval x ≠ 0 := by
  rcases fiveFive_critical_cut_order with ⟨_, h₁, h₂, h₃, h₄, h₅⟩
  exact fiveFive_critical_free_of_ne_cuts hx0
    (ne_of_lt (hx.trans (h₁.trans h₂)))
    (ne_of_lt hx)
    (ne_of_lt (hx.trans h₁))
    (ne_of_lt (hx.trans (h₁.trans (h₂.trans h₃))))
    (ne_of_lt (hx.trans (h₁.trans (h₂.trans (h₃.trans h₄)))))
    (ne_of_lt (hx.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅))))))

/-- The cell between the lower `P6` cut and first `P28` cut is critical-free. -/
theorem fiveFive_critical_free_p6_low_p28_first
    {x : ℝ} (hx : x ∈ Ioo fiveFiveP6LowCut fiveFiveP28FirstCut) :
    x ≠ 1 ∧ fiveFiveDiscriminantP6PolyReal.eval x ≠ 0 ∧
      fiveFiveDiscriminantP28PolyReal.eval x ≠ 0 := by
  rcases fiveFive_critical_cut_order with ⟨h₀, _, h₂, h₃, h₄, h₅⟩
  exact fiveFive_critical_free_of_ne_cuts (h₀.trans hx.1)
    (ne_of_lt (hx.2.trans h₂))
    (ne_of_gt hx.1)
    (ne_of_lt hx.2)
    (ne_of_lt (hx.2.trans (h₂.trans h₃)))
    (ne_of_lt (hx.2.trans (h₂.trans (h₃.trans h₄))))
    (ne_of_lt (hx.2.trans (h₂.trans (h₃.trans (h₄.trans h₅)))))

/-- The cell between the first `P28` cut and `1` is critical-free. -/
theorem fiveFive_critical_free_p28_first_one
    {x : ℝ} (hx : x ∈ Ioo fiveFiveP28FirstCut 1) :
    x ≠ 1 ∧ fiveFiveDiscriminantP6PolyReal.eval x ≠ 0 ∧
      fiveFiveDiscriminantP28PolyReal.eval x ≠ 0 := by
  rcases fiveFive_critical_cut_order with ⟨h₀, h₁, _, h₃, h₄, h₅⟩
  exact fiveFive_critical_free_of_ne_cuts (h₀.trans (h₁.trans hx.1))
    (ne_of_lt hx.2)
    (ne_of_gt (h₁.trans hx.1))
    (ne_of_gt hx.1)
    (ne_of_lt (hx.2.trans h₃))
    (ne_of_lt (hx.2.trans (h₃.trans h₄)))
    (ne_of_lt (hx.2.trans (h₃.trans (h₄.trans h₅))))

/-- The cell between `1` and the second `P28` cut is critical-free. -/
theorem fiveFive_critical_free_one_p28_second
    {x : ℝ} (hx : x ∈ Ioo 1 fiveFiveP28SecondCut) :
    x ≠ 1 ∧ fiveFiveDiscriminantP6PolyReal.eval x ≠ 0 ∧
      fiveFiveDiscriminantP28PolyReal.eval x ≠ 0 := by
  rcases fiveFive_critical_cut_order with ⟨h₀, h₁, h₂, _, h₄, h₅⟩
  exact fiveFive_critical_free_of_ne_cuts (zero_lt_one.trans hx.1)
    (ne_of_gt hx.1)
    (ne_of_gt (h₁.trans (h₂.trans hx.1)))
    (ne_of_gt (h₂.trans hx.1))
    (ne_of_lt hx.2)
    (ne_of_lt (hx.2.trans h₄))
    (ne_of_lt (hx.2.trans (h₄.trans h₅)))

/-- The cell between the second and third `P28` cuts is critical-free. -/
theorem fiveFive_critical_free_p28_second_third
    {x : ℝ} (hx : x ∈ Ioo fiveFiveP28SecondCut fiveFiveP28ThirdCut) :
    x ≠ 1 ∧ fiveFiveDiscriminantP6PolyReal.eval x ≠ 0 ∧
      fiveFiveDiscriminantP28PolyReal.eval x ≠ 0 := by
  rcases fiveFive_critical_cut_order with ⟨h₀, h₁, h₂, h₃, _, h₅⟩
  exact fiveFive_critical_free_of_ne_cuts
    (zero_lt_one.trans (h₃.trans hx.1))
    (ne_of_gt (h₃.trans hx.1))
    (ne_of_gt (h₁.trans (h₂.trans (h₃.trans hx.1))))
    (ne_of_gt (h₂.trans (h₃.trans hx.1)))
    (ne_of_gt hx.1)
    (ne_of_lt hx.2)
    (ne_of_lt (hx.2.trans h₅))

/-- The cell between the third `P28` cut and upper `P6` cut is critical-free. -/
theorem fiveFive_critical_free_p28_third_p6_high
    {x : ℝ} (hx : x ∈ Ioo fiveFiveP28ThirdCut fiveFiveP6HighCut) :
    x ≠ 1 ∧ fiveFiveDiscriminantP6PolyReal.eval x ≠ 0 ∧
      fiveFiveDiscriminantP28PolyReal.eval x ≠ 0 := by
  rcases fiveFive_critical_cut_order with ⟨h₀, h₁, h₂, h₃, h₄, _⟩
  exact fiveFive_critical_free_of_ne_cuts
    (zero_lt_one.trans (h₃.trans (h₄.trans hx.1)))
    (ne_of_gt (h₃.trans (h₄.trans hx.1)))
    (ne_of_gt (h₁.trans (h₂.trans (h₃.trans (h₄.trans hx.1)))))
    (ne_of_gt (h₂.trans (h₃.trans (h₄.trans hx.1))))
    (ne_of_gt (h₄.trans hx.1))
    (ne_of_gt hx.1)
    (ne_of_lt hx.2)

/-- The final complementary parameter cell is critical-free. -/
theorem fiveFive_critical_free_above_p6_high
    {x : ℝ} (hx : fiveFiveP6HighCut < x) :
    x ≠ 1 ∧ fiveFiveDiscriminantP6PolyReal.eval x ≠ 0 ∧
      fiveFiveDiscriminantP28PolyReal.eval x ≠ 0 := by
  rcases fiveFive_critical_cut_order with ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩
  exact fiveFive_critical_free_of_ne_cuts
    (h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans hx))))))
    (ne_of_gt (h₃.trans (h₄.trans (h₅.trans hx))))
    (ne_of_gt (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans hx))))))
    (ne_of_gt (h₂.trans (h₃.trans (h₄.trans (h₅.trans hx)))))
    (ne_of_gt (h₄.trans (h₅.trans hx)))
    (ne_of_gt (h₅.trans hx))
    (ne_of_gt hx)

end

end Cuboid2
