import Cuboid2.QuadraticReduction.GaussianMordellWeil
import Cuboid2.QuadraticReduction.GaussianSaturationFinite
import Cuboid2.QuadraticReduction.GaussianP37Bridge

/-!
# Index-independent arithmetic for the visible Gaussian point

This file contains only group theory and integer arithmetic.  It never assumes
that the visible point `P=(2,2)` is primitive and it does not construct or
assume a reduction map.

Given an additive equivalence with `ℤ × ZMod 2`, the distinguished
two-torsion point is forced to be `(0,1)`.  We then use the corresponding free
generator to write both `P` and an arbitrary point in normal form.  The
distinct Kummer classes of `P` and `T` force the free coefficient of `P` to be
odd.  Finally, an inverse of that coefficient modulo `84` converts the paired
finite row into congruences with `±P`, while a separate proved coprimality at
`37` supplies the denominator condition for the rational formal parameter.
-/

namespace Cuboid2
namespace GaussianIndexIndependent

noncomputable section

open GaussianDescent
open GaussianP37
open GaussianP37Bridge
open GaussianRankArithmetic

private theorem gaussianRat_irreducible_fact :
    ∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x := by
  intro x hx
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

local instance : Fact (∀ x : ℚ, x ^ 2 ≠ (-1 : ℚ) + 0 * x) :=
  ⟨gaussianRat_irreducible_fact⟩

abbrev DescentE0Point := (curve E0A E0B).toAffine.Point
abbrev E0Point := gaussianE0.toAffine.Point

/-- The descent presentation is definitionally the displayed Gaussian
Weierstrass model; this equivalence exposes that identification at the group
level for later consumers. -/
def actualE0PointEquiv :
    E0Point ≃+ DescentE0Point :=
  AddEquiv.refl _

/-- The visible point, in the model on which the Kummer homomorphism is
defined. -/
abbrev visiblePoint : E0Point := gaussianE0P

/-- The named two-torsion point, in the same descent model. -/
abbrev twoTorsionPoint : E0Point := gaussianE0T

@[simp] theorem actualE0PointEquiv_visible :
    actualE0PointEquiv visiblePoint = GaussianDescent.gaussianE0P := by
  rfl

@[simp] theorem actualE0PointEquiv_twoTorsion :
    actualE0PointEquiv twoTorsionPoint =
      torsion E0A E0B E0B_ne_zero E0C_ne_zero := by
  rfl

private abbrev e0AlphaHom : E0Point →+ Additive SquareClass :=
  (alphaHom E0A E0B E0B_ne_zero E0C_ne_zero).comp
    actualE0PointEquiv.toAddMonoidHom

private theorem e0AlphaHom_gaussianE0P :
    e0AlphaHom visiblePoint = Additive.ofMul classI := by
  change
    Additive.ofMul
        (alpha E0A E0B E0B_ne_zero E0C_ne_zero
          (actualE0PointEquiv visiblePoint)) =
      Additive.ofMul classI
  rw [actualE0PointEquiv_visible]
  exact congrArg Additive.ofMul alpha_gaussianE0P

private theorem e0AlphaHom_gaussianE0T :
    e0AlphaHom twoTorsionPoint = Additive.ofMul classIPi := by
  change
    Additive.ofMul
        (alpha E0A E0B E0B_ne_zero E0C_ne_zero
          (actualE0PointEquiv twoTorsionPoint)) =
      Additive.ofMul classIPi
  rw [actualE0PointEquiv_twoTorsion]
  exact congrArg Additive.ofMul alpha_gaussianE0T

private theorem twoTorsionPoint_ne_zero : twoTorsionPoint ≠ 0 := by
  exact gaussianE0T_ne_zero

private theorem two_nsmul_twoTorsionPoint :
    2 • twoTorsionPoint = 0 := by
  exact two_nsmul_gaussianE0T

/-- The free generator selected by an abstract rank-one normal form. -/
def freeGenerator (e : E0Point ≃+ ℤ × ZMod 2) : E0Point :=
  e.symm (1, 0)

@[simp] theorem freeGenerator_image (e : E0Point ≃+ ℤ × ZMod 2) :
    e (freeGenerator e) = (1, 0) :=
  e.apply_symm_apply (1, 0)

/-- Every Gaussian squareclass has additive exponent two. -/
theorem two_nsmul_additive_squareClass (d : Additive SquareClass) :
    2 • d = 0 := by
  rw [two_nsmul]
  change Additive.ofMul (d.toMul * d.toMul) = Additive.ofMul 1
  rw [squareClass_mul_self]

/-- Any additive equivalence with `ℤ × ZMod 2` sends the named nonzero
two-torsion point to the unique nonzero two-torsion element `(0,1)`. -/
theorem gaussianE0T_image
    (e : E0Point ≃+ ℤ × ZMod 2) :
    e twoTorsionPoint = (0, 1) := by
  have htwo : 2 • e twoTorsionPoint = 0 := by
    rw [two_nsmul]
    calc
      e twoTorsionPoint + e twoTorsionPoint =
          e (twoTorsionPoint + twoTorsionPoint) := (e.map_add _ _).symm
      _ = e 0 := congrArg e (by
        simpa [two_nsmul] using two_nsmul_twoTorsionPoint)
      _ = 0 := e.map_zero
  have hfirst : (e twoTorsionPoint).1 = 0 := by
    have h := congrArg Prod.fst htwo
    norm_num [two_nsmul] at h
    omega
  have hsecond_ne : (e twoTorsionPoint).2 ≠ 0 := by
    intro hsecond
    apply twoTorsionPoint_ne_zero
    apply e.injective
    rw [map_zero]
    apply Prod.ext
    · exact hfirst
    · exact hsecond
  have hsecond : (e twoTorsionPoint).2 = 1 := by
    have hlt : (e twoTorsionPoint).2.val < 2 := ZMod.val_lt _
    have hval_ne : (e twoTorsionPoint).2.val ≠ 0 := by
      intro hval
      apply hsecond_ne
      exact (ZMod.val_eq_zero _).mp hval
    have hval : (e twoTorsionPoint).2.val = 1 := by omega
    exact (ZMod.val_eq_one (by norm_num) _).mp hval
  exact Prod.ext hfirst hsecond

/-- Normal form with respect to the free generator selected by `e` and the
already named two-torsion point. -/
theorem exists_normalForm
    (e : E0Point ≃+ ℤ × ZMod 2) (Q : E0Point) :
    ∃ k : ℤ, ∃ ε : ℕ, ε < 2 ∧
      Q = k • freeGenerator e + ε • twoTorsionPoint := by
  exact
    GaussianGlobal.exists_named_rank_one_two_torsion_normal_form
      e (freeGenerator e) twoTorsionPoint
      (freeGenerator_image e) (gaussianE0T_image e) Q

/-- The visible point and an arbitrary point admit simultaneous normal forms
for the same abstract free generator. -/
theorem exists_visible_and_point_normalForms
    (e : E0Point ≃+ ℤ × ZMod 2) (Q : E0Point) :
    ∃ m k : ℤ, ∃ δ ε : ℕ,
      δ < 2 ∧ ε < 2 ∧
      visiblePoint = m • freeGenerator e + δ • twoTorsionPoint ∧
      Q = k • freeGenerator e + ε • twoTorsionPoint := by
  obtain ⟨m, δ, hδ, hP⟩ := exists_normalForm e visiblePoint
  obtain ⟨k, ε, hε, hQ⟩ := exists_normalForm e Q
  exact ⟨m, k, δ, ε, hδ, hε, hP, hQ⟩

private theorem alphaHom_even_zsmul
    (R : E0Point) (z : ℤ) :
    e0AlphaHom ((z + z) • R) = 0 := by
  rw [map_zsmul, add_zsmul]
  change
    z • alphaHom E0A E0B E0B_ne_zero E0C_ne_zero R +
        z • alphaHom E0A E0B E0B_ne_zero E0C_ne_zero R =
      0
  rw [← two_nsmul]
  exact two_nsmul_additive_squareClass _

/-- The visible point has odd coefficient in every rank-one normal form.

This uses only the genuine Kummer homomorphism and the already proved
inequalities `classI ≠ 1` and `classI ≠ classIPi`; no primitivity conclusion is
drawn.
-/
theorem visibleCoefficient_odd
    (e : E0Point ≃+ ℤ × ZMod 2)
    {m : ℤ} {δ : ℕ} (hδ : δ < 2)
    (hP :
      visiblePoint = m • freeGenerator e + δ • twoTorsionPoint) :
    Odd m := by
  rcases Int.even_or_odd m with hm | hm
  · rcases hm with ⟨z, hz⟩
    subst m
    have hmap := congrArg
      e0AlphaHom hP
    rw [map_add, alphaHom_even_zsmul] at hmap
    interval_cases δ
    · simp only [zero_nsmul, map_zero, add_zero,
        e0AlphaHom_gaussianE0P] at hmap
      exact (classI_ne_one <| congrArg Additive.toMul hmap).elim
    · simp only [one_nsmul, zero_add, e0AlphaHom_gaussianE0P,
        e0AlphaHom_gaussianE0T] at hmap
      exact (classI_ne_classIPi <| congrArg Additive.toMul hmap).elim
  · exact hm

/-! ## Inverting the unknown index modulo the paired finite period -/

/-- The canonical integer representative of the inverse of `m` modulo `84`.
The proof of invertibility is kept separate so the definition remains total. -/
def inverseMod84 (m : ℤ) : ℤ :=
  (((m : ZMod 84)⁻¹).val : ℤ)

/-- Coprimality with `84` makes `inverseMod84` a genuine inverse. -/
theorem mul_inverseMod84_modEq
    {m : ℤ} (hm : IsCoprime m (84 : ℤ)) :
    m * inverseMod84 m ≡ 1 [ZMOD 84] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ 84).mp
  simpa [inverseMod84] using
    (ZMod.coe_int_mul_val_inv (n := 84) hm)

/-- The paired-row coefficient attached to a free coefficient `k`. -/
def rowResidue (k n : ℤ) : ℕ :=
  (k * n).natMod 12

private theorem modEq_twelve_of_natMod_eq_one
    {a : ℤ} (h : a.natMod 12 = 1) :
    a ≡ 1 [ZMOD 12] := by
  change a % 12 = 1 % 12
  simp only [Int.natMod] at h
  have hnonneg : 0 ≤ a % 12 := Int.emod_nonneg a (by norm_num)
  have hlt : a % 12 < 12 := Int.emod_lt_of_pos a (by norm_num)
  norm_num
  omega

private theorem modEq_twelve_of_natMod_eq_eleven
    {a : ℤ} (h : a.natMod 12 = 11) :
    a ≡ -1 [ZMOD 12] := by
  change a % 12 = (-1 : ℤ) % 12
  simp only [Int.natMod] at h
  have hnonneg : 0 ≤ a % 12 := Int.emod_nonneg a (by norm_num)
  have hlt : a % 12 < 12 := Int.emod_lt_of_pos a (by norm_num)
  norm_num
  omega

/-- The `+P` paired row means that the free coefficient of `Q` is congruent
to that of `P` modulo `12`, without dividing by `m` in characteristic zero. -/
theorem coefficient_modEq_of_row_one
    {m k n : ℤ}
    (hinv : m * n ≡ 1 [ZMOD 84])
    (hrow : rowResidue k n = 1) :
    k ≡ m [ZMOD 12] := by
  have hinv12 : m * n ≡ 1 [ZMOD 12] :=
    hinv.of_dvd (by norm_num)
  have hkn : k * n ≡ 1 [ZMOD 12] :=
    modEq_twelve_of_natMod_eq_one hrow
  calc
    k ≡ k * (m * n) [ZMOD 12] := by
      simpa using (hinv12.mul_left k).symm
    _ = (k * n) * m := by ring
    _ ≡ 1 * m [ZMOD 12] := hkn.mul_right m
    _ = m := one_mul m

/-- The `-P` paired row gives the corresponding negative congruence. -/
theorem coefficient_modEq_of_row_eleven
    {m k n : ℤ}
    (hinv : m * n ≡ 1 [ZMOD 84])
    (hrow : rowResidue k n = 11) :
    k ≡ -m [ZMOD 12] := by
  have hinv12 : m * n ≡ 1 [ZMOD 12] :=
    hinv.of_dvd (by norm_num)
  have hkn : k * n ≡ -1 [ZMOD 12] :=
    modEq_twelve_of_natMod_eq_eleven hrow
  calc
    k ≡ k * (m * n) [ZMOD 12] := by
      simpa using (hinv12.mul_left k).symm
    _ = (k * n) * m := by ring
    _ ≡ (-1) * m [ZMOD 12] := hkn.mul_right m
    _ = -m := neg_one_mul m

/-- Canonical-inverse form of the `+P` row congruence. -/
theorem coefficient_modEq_of_inverseMod84_row_one
    {m k : ℤ} (hm : IsCoprime m (84 : ℤ))
    (hrow : rowResidue k (inverseMod84 m) = 1) :
    k ≡ m [ZMOD 12] :=
  coefficient_modEq_of_row_one (mul_inverseMod84_modEq hm) hrow

/-- Canonical-inverse form of the `-P` row congruence. -/
theorem coefficient_modEq_of_inverseMod84_row_eleven
    {m k : ℤ} (hm : IsCoprime m (84 : ℤ))
    (hrow : rowResidue k (inverseMod84 m) = 11) :
    k ≡ -m [ZMOD 12] :=
  coefficient_modEq_of_row_eleven (mul_inverseMod84_modEq hm) hrow

/-! ## The torsion twist and the index-independent group identity -/

/-- The torsion twist after replacing the free generator by the inverse
multiple of the visible point. -/
def rowTwist (k n : ℤ) (δ ε : ℕ) : Twist :=
  if (ε : ℤ) ≡ (k * n) * δ [ZMOD 2] then .plain else .torsion

@[simp] theorem rowTwist_eq_plain_iff
    (k n : ℤ) (δ ε : ℕ) :
    rowTwist k n δ ε = .plain ↔
      (ε : ℤ) ≡ (k * n) * δ [ZMOD 2] := by
  simp [rowTwist]

/-- A plain reindexed twist is exactly the parity relation needed to clear the
unknown index from the two global normal forms. -/
theorem torsionCoefficient_modEq_of_plain
    {m k n : ℤ} {δ ε : ℕ}
    (hinv : m * n ≡ 1 [ZMOD 84])
    (hplain : rowTwist k n δ ε = .plain) :
    m * (ε : ℤ) ≡ k * (δ : ℤ) [ZMOD 2] := by
  have hinv2 : m * n ≡ 1 [ZMOD 2] :=
    hinv.of_dvd (by norm_num)
  have htwist :
      (ε : ℤ) ≡ (k * n) * δ [ZMOD 2] :=
    (rowTwist_eq_plain_iff k n δ ε).mp hplain
  calc
    m * (ε : ℤ) ≡ m * ((k * n) * δ) [ZMOD 2] :=
      htwist.mul_left m
    _ = (k * (δ : ℤ)) * (m * n) := by ring
    _ ≡ (k * (δ : ℤ)) * 1 [ZMOD 2] :=
      hinv2.mul_left (k * (δ : ℤ))
    _ = k * (δ : ℤ) := mul_one _

/-- Clearing the unknown index gives an actual characteristic-zero group
identity.  This is the replacement for the invalid assumption that every
point is an integral multiple of the visible point. -/
theorem indexCleared_point_eq
    (e : E0Point ≃+ ℤ × ZMod 2)
    {Q : E0Point} {m k : ℤ} {δ ε : ℕ}
    (hP :
      visiblePoint = m • freeGenerator e + δ • twoTorsionPoint)
    (hQ :
      Q = k • freeGenerator e + ε • twoTorsionPoint)
    (htorsion :
      m * (ε : ℤ) ≡ k * (δ : ℤ) [ZMOD 2]) :
    m • Q = k • visiblePoint := by
  apply e.injective
  simp only [hP, hQ, map_zsmul, map_add, map_nsmul,
    freeGenerator_image, gaussianE0T_image]
  apply Prod.ext
  · simp [mul_comm]
  · have hcast :
        ((m * (ε : ℤ) : ℤ) : ZMod 2) =
          ((k * (δ : ℤ) : ℤ) : ZMod 2) :=
      (ZMod.intCast_eq_intCast_iff _ _ 2).2 htorsion
    simpa [mul_comm] using hcast

/-- Combined pure-group endpoint for a plain paired row. -/
theorem indexCleared_point_eq_of_plain
    (e : E0Point ≃+ ℤ × ZMod 2)
    {Q : E0Point} {m k n : ℤ} {δ ε : ℕ}
    (hP :
      visiblePoint = m • freeGenerator e + δ • twoTorsionPoint)
    (hQ :
      Q = k • freeGenerator e + ε • twoTorsionPoint)
    (hinv : m * n ≡ 1 [ZMOD 84])
    (hplain : rowTwist k n δ ε = .plain) :
    m • Q = k • visiblePoint :=
  indexCleared_point_eq e hP hQ
    (torsionCoefficient_modEq_of_plain hinv hplain)

/-- With the canonical inverse modulo `84`, a surviving `+P` plain row
simultaneously gives the coefficient congruence and the index-cleared global
point identity. -/
theorem indexIndependent_row_one
    (e : E0Point ≃+ ℤ × ZMod 2)
    {Q : E0Point} {m k : ℤ} {δ ε : ℕ}
    (hP :
      visiblePoint = m • freeGenerator e + δ • twoTorsionPoint)
    (hQ :
      Q = k • freeGenerator e + ε • twoTorsionPoint)
    (hm : IsCoprime m (84 : ℤ))
    (hrow : rowResidue k (inverseMod84 m) = 1)
    (hplain :
      rowTwist k (inverseMod84 m) δ ε = .plain) :
    k ≡ m [ZMOD 12] ∧ m • Q = k • visiblePoint :=
  ⟨coefficient_modEq_of_inverseMod84_row_one hm hrow,
    indexCleared_point_eq_of_plain e hP hQ
      (mul_inverseMod84_modEq hm) hplain⟩

/-- The corresponding package for a surviving `-P` plain row. -/
theorem indexIndependent_row_eleven
    (e : E0Point ≃+ ℤ × ZMod 2)
    {Q : E0Point} {m k : ℤ} {δ ε : ℕ}
    (hP :
      visiblePoint = m • freeGenerator e + δ • twoTorsionPoint)
    (hQ :
      Q = k • freeGenerator e + ε • twoTorsionPoint)
    (hm : IsCoprime m (84 : ℤ))
    (hrow : rowResidue k (inverseMod84 m) = 11)
    (hplain :
      rowTwist k (inverseMod84 m) δ ε = .plain) :
    k ≡ -m [ZMOD 12] ∧ m • Q = k • visiblePoint :=
  ⟨coefficient_modEq_of_inverseMod84_row_eleven hm hrow,
    indexCleared_point_eq_of_plain e hP hQ
      (mul_inverseMod84_modEq hm) hplain⟩

/-! ## Rational parameters without a primitivity assumption -/

private theorem nonzero_of_isCoprime_84
    {m : ℤ} (hm : IsCoprime m (84 : ℤ)) :
    m ≠ 0 := by
  intro h
  subst m
  norm_num at hm

private theorem natAbs_coprime_37
    {m : ℤ} (hm : IsCoprime m (37 : ℤ)) :
    m.natAbs.Coprime 37 := by
  simpa using (Int.isCoprime_iff_nat_coprime.mp hm)

/-- Rational formal parameter for the row centered at `P`.  Its numerator is
the integral quotient forced by `k ≡ m (mod 12)` and its positive denominator
is `|m|`. -/
def parameterAtP
    (k m : ℤ) (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : IsCoprime m (37 : ℤ))
    (_hrow : k ≡ m [ZMOD 12]) :
    RationalParameter where
  numerator := (k - m) / 12
  denominator := m.natAbs
  denominator_pos := Int.natAbs_pos.mpr (nonzero_of_isCoprime_84 hm84)
  denominator_coprime := natAbs_coprime_37 hm37

@[simp] theorem parameterAtP_numerator
    (k m : ℤ) (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : IsCoprime m (37 : ℤ))
    (hrow : k ≡ m [ZMOD 12]) :
    (parameterAtP k m hm84 hm37 hrow).numerator = (k - m) / 12 :=
  rfl

@[simp] theorem parameterAtP_denominator
    (k m : ℤ) (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : IsCoprime m (37 : ℤ))
    (hrow : k ≡ m [ZMOD 12]) :
    (parameterAtP k m hm84 hm37 hrow).denominator = m.natAbs :=
  rfl

/-- Rational formal parameter for the row centered at `-P`. -/
def parameterAtNegP
    (k m : ℤ) (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : IsCoprime m (37 : ℤ))
    (_hrow : k ≡ -m [ZMOD 12]) :
    RationalParameter where
  numerator := (k + m) / 12
  denominator := m.natAbs
  denominator_pos := Int.natAbs_pos.mpr (nonzero_of_isCoprime_84 hm84)
  denominator_coprime := natAbs_coprime_37 hm37

@[simp] theorem parameterAtNegP_numerator
    (k m : ℤ) (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : IsCoprime m (37 : ℤ))
    (hrow : k ≡ -m [ZMOD 12]) :
    (parameterAtNegP k m hm84 hm37 hrow).numerator = (k + m) / 12 :=
  rfl

@[simp] theorem parameterAtNegP_denominator
    (k m : ℤ) (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : IsCoprime m (37 : ℤ))
    (hrow : k ≡ -m [ZMOD 12]) :
    (parameterAtNegP k m hm84 hm37 hrow).denominator = m.natAbs :=
  rfl

private theorem twelve_dvd_sub_of_modEq
    {a b : ℤ} (h : a ≡ b [ZMOD 12]) :
    (12 : ℤ) ∣ a - b := by
  have hd : (12 : ℤ) ∣ b - a := h.dvd
  rw [show a - b = -(b - a) by ring]
  exact Dvd.dvd.neg_right hd

/-- The numerator stored for the `P` disk clears its factor `12` exactly. -/
theorem parameterAtP_numerator_mul_twelve
    {k m : ℤ} (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : IsCoprime m (37 : ℤ))
    (hrow : k ≡ m [ZMOD 12]) :
    (parameterAtP k m hm84 hm37 hrow).numerator * 12 = k - m := by
  rw [parameterAtP_numerator]
  exact Int.ediv_mul_cancel (twelve_dvd_sub_of_modEq hrow)

/-- The numerator stored for the `-P` disk clears its factor `12` exactly. -/
theorem parameterAtNegP_numerator_mul_twelve
    {k m : ℤ} (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : IsCoprime m (37 : ℤ))
    (hrow : k ≡ -m [ZMOD 12]) :
    (parameterAtNegP k m hm84 hm37 hrow).numerator * 12 = k + m := by
  rw [parameterAtNegP_numerator]
  apply Int.ediv_mul_cancel
  have hd : (12 : ℤ) ∣ k - (-m) :=
    twelve_dvd_sub_of_modEq hrow
  simpa using hd

/-- Vanishing of the `P`-disk numerator recovers the exact coefficient
identity `k=m`. -/
theorem eq_of_parameterAtP_numerator_eq_zero
    {k m : ℤ} (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : IsCoprime m (37 : ℤ))
    (hrow : k ≡ m [ZMOD 12])
    (hzero : (parameterAtP k m hm84 hm37 hrow).numerator = 0) :
    k = m := by
  have hd : (12 : ℤ) ∣ k - m := twelve_dvd_sub_of_modEq hrow
  have hexact : (k - m) / 12 * 12 = k - m :=
    Int.ediv_mul_cancel hd
  rw [parameterAtP_numerator] at hzero
  rw [hzero] at hexact
  omega

/-- Vanishing of the `-P`-disk numerator recovers `k=-m`. -/
theorem eq_neg_of_parameterAtNegP_numerator_eq_zero
    {k m : ℤ} (hm84 : IsCoprime m (84 : ℤ))
    (hm37 : IsCoprime m (37 : ℤ))
    (hrow : k ≡ -m [ZMOD 12])
    (hzero : (parameterAtNegP k m hm84 hm37 hrow).numerator = 0) :
    k = -m := by
  have hd : (12 : ℤ) ∣ k - (-m) :=
    twelve_dvd_sub_of_modEq hrow
  have hd' : (12 : ℤ) ∣ k + m := by simpa using hd
  have hexact : (k + m) / 12 * 12 = k + m :=
    Int.ediv_mul_cancel hd'
  rw [parameterAtNegP_numerator] at hzero
  rw [hzero] at hexact
  omega

end

end GaussianIndexIndependent
end Cuboid2
