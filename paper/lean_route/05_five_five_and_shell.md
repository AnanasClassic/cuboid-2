# Sharipov's second cuboid conjecture: shell + symmetric 5+5 branch (Lean → paper notes)

Sources: `lean/Cuboid2/{Polynomial,Scaling,Factorization,FactorizationClassification,Capell,CapellDegree,CapellFactor,CapellQuintic,Main}.lean` and `lean/Cuboid2/FiveFive/*.lean`.

Conventions. "ring" = identity verified by Lean's `ring` normalizer; "norm_num" = exact rational arithmetic; "decide" = kernel evaluation of a finite decidable proposition. The shell and FiveFive files contain **no `native_decide`, no `sorry`, no `axiom`**.

---

## Part A. Exact mathematical statements

### A.1 The polynomials (`Polynomial.lean`)

**Normalized quintic** (`normalizedQuintic s`):

    P_s(x) = x^5 + (2+s)(3−2s) x^4
                 + (1 + 10s + 4s^2 − 14s^3 + s^4) x^3
                 − s(1 − 14s + 4s^2 + 10s^3 + s^4) x^2
                 − s^3 (1+2s)(3s−2) x
                 − s^5.

**Sharipov's polynomial** (`sharipovPolynomial p q : ℤ[X]`, `sharipovPolynomialQ p q : ℚ[X]`):

    Q_{p,q}(t) = t^10 + (2q^2 + p^2)(3q^2 − 2p^2) t^8
               + (q^8 + 10p^2q^6 + 4p^4q^4 − 14p^6q^2 + p^8) t^6
               − p^2q^2 (q^8 − 14p^2q^6 + 4p^4q^4 + 10p^6q^2 + p^8) t^4
               − p^6q^6 (q^2 + 2p^2)(3p^2 − 2q^2) t^2
               − p^10 q^10.

**Parameter**: `sharipovParameter p q = (p/q)^2 =: s`.

Bookkeeping: `normalizedQuintic_monic`, `normalizedQuintic_degree` (= 5), `sharipovPolynomialOver_monic`, `sharipovPolynomialOver_degree` (= 10), `sharipovPolynomial_coeff_zero`, `sharipovPolynomial_isPrimitive`, `map_sharipovPolynomial`.

**Gauss-lemma transfer** (`sharipovPolynomial_irreducible_iff_rational`): Irreducible over ℤ ⇔ over ℚ, from Mathlib `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`. Direction used in `Main.lean`: ℚ ⇒ ℤ.

**Scaling identity** (`eval_sharipov_scaling`; field K, q ≠ 0): Q_{p,q}(t) = q^20 · P_{(p/q)^2}(t^2/q^4). Proof: `field_simp`+ring.

### A.2 Polynomial form of scaling; irreducibility transfer (`Scaling.lean`)

`normalizedEvenPolynomial s := (normalizedQuintic s).comp (X^2)` = P_s(X^2); monic, degree 10.

`sharipovPolynomialQ_eq_scaleRoots` (0<q): Q_{p,q} = scaleRoots(P_s(X^2), q^2). Proved by agreement at every t ∈ ℚ (`scaleRoots_eval_mul`) plus `Polynomial.eq_of_infinite_eval_eq`.

`irreducible_scaleRoots_iff` (r ≠ 0): Irreducible(scaleRoots P r) ⇔ Irreducible P.

Hence `sharipovPolynomialQ_irreducible_iff_normalizedEven` (0<q): Irreducible Q_{p,q} ⇔ Irreducible P_s(X^2).

### A.3 The three cases (`Factorization.lean`)

    LinearQuarticCase s     := ∃ r ∈ ℚ, P_s(r) = 0.
    QuadraticCubicCase s    := ∃ A B ∈ ℚ[X], A monic deg 2, B monic deg 3, P_s = A·B.
    SymmetricFiveFiveCase s := ∃ R ∈ ℚ[X], R monic, deg R = 5, R irreducible, P_s(X^2) = R(X)·(−R(−X)).

`irreducible_of_factorization_cases`: if ¬Irreducible P ⇒ (linear ∨ quadratic ∨ symmetric) and all three are refuted, P is irreducible. `sharipovParameter_pos`, `sharipovParameter_ne_one` (s = 1 ⇔ p = q).

### A.4 Elementary reducible-quintic classification (`FactorizationClassification.lean`)

`monic_quintic_reducible_cases`: a monic P ∈ ℚ[X], deg 5, not irreducible, has a rational root or a monic 2+3 factorization. Proof: Mathlib `Monic.irreducible_iff_lt_natDegree_lt` (no monic divisor of degree 1..⌊5/2⌋ = 2). `normalizedQuintic_reducible_cases`.

### A.5 Specialized Capell argument (`Capell*.lean`)

Definitions: `reflectPolynomial P := P.comp(−X)`; `expand ℚ 2 F` = F(X^2); `contract 2 F` = polynomial with i-th coefficient coeff_{2i}(F). `monicReflection R := (−1)^{deg R}·R(−X)`.

Reflection algebra (`Capell.lean`): involution, multiplicative; `reflectPolynomial_coeff`: coeff_n(P(−X)) = (−1)^n coeff_n(P); `reflectPolynomial_dvd_of_dvd_fixed` (F(−X)=F, P | F ⇒ P(−X) | F); `expand_contract_two_of_reflectPolynomial_eq` (F(−X)=F ⇒ F = (contract 2 F)(X^2)); `symmetric_product_eq_expand_contract` (P·P(−X) = G(X^2)).

Descent (`CapellDegree.lean`): `dvd_of_expand_two_dvd_expand_two`: A(X^2) | P(X^2) ⇒ A | P (apply contract 2: `contract_mul_expand`, `contract_expand`); `natDegree_eq_of_symmetric_product_dvd_expand_irreducible`: R, P irreducible, R·R(−X) | P(X^2) ⇒ deg R = deg P.

Reflection orbit (`CapellFactor.lean`): `eq_monicReflection_of_monic_of_associated_reflect` (R monic, R ~ R(−X) ⇒ R = (−1)^{deg R}R(−X)); `exists_monic_irreducible_factor_le_half`; `mul_reflectPolynomial_dvd_of_not_associated` (R irreducible, R | F, R(−X) | F, R ≁ R(−X) ⇒ R·R(−X) | F; uses R(−X) prime in ℚ[X]).

`not_associated_reflect_of_irreducible_quintic_factor`: P irreducible, deg P = 5, R monic irreducible, R | P(X^2), deg R ≤ 5 ⇒ R ≁ R(−X). Proof by parity of deg R:
- deg R = 2k: R(−X) = R ⇒ R = S(X^2), S = contract 2 R; S | P; deg S = k > 0 so S ~ P ⇒ deg S = 5; but 2 deg S = deg R ≤ 5. Contradiction.
- deg R = 2k+1: R(−X) = −R ⇒ R(0) = 0 ⇒ X | R | P(X^2) ⇒ P(0) = 0 ⇒ X | P ⇒ X ~ P ⇒ deg P = 1 ≠ 5.

**Reduction** (`normalizedEven_capell_reduction`): ¬Irreducible P_s(X^2) ⇒ ¬Irreducible P_s ∨ SymmetricFiveFiveCase s. Proof: assume P_s irreducible. Pick monic irreducible R | P_s(X^2) with deg R ≤ 5. R ≁ R(−X). R(−X) | P_s(X^2). So R·R(−X) | P_s(X^2); deg R = 5; R·(−R(−X)) is monic of degree 10 dividing the monic degree-10 P_s(X^2), hence equal.

### A.6 Shell assembly (`Main.lean`)

`sharipov_composition_reduction`, `sharipov_factorization_classification`, `linear_quartic_impossible`, `quadratic_cubic_impossible`, `symmetric_five_five_impossible` (s>0, s≠1), `sharipovPolynomialQ_irreducible`, `sharipov_second_cuboid_conjecture` (ℤ[X]), `no_nontrivial_factorization`. The 5+5 branch uses only 0<s and s≠1; coprimality is consumed only by 1+4 and 2+3.

---

## Part B. The symmetric 5+5 branch

### B.1 Five coefficient equations (`FiveFive/Basic.lean`)

`quinticFactor a b c d e := X^5 + aX^4 + bX^3 + cX^2 + dX + e`.

`normalizedEvenPolynomial_explicit` (ring): P_s(X^2) = X^10 + c8 X^8 + c6 X^6 + c4 X^4 + c2 X^2 − s^5 with
    c8 = (2+s)(3−2s), c6 = 1 + 10s + 4s^2 − 14s^3 + s^4, c4 = −s(1 − 14s + 4s^2 + 10s^3 + s^4), c2 = −s^3(1+2s)(3s−2).

`quinticFactor_symmetric_product` (ring):
    R(X)·(−R(−X)) = X^10 + (2b − a^2)X^8 + (b^2 + 2d − 2ac)X^6 + (2bd − c^2 − 2ae)X^4 + (d^2 − 2ce)X^2 − e^2.

`FiveFiveCoefficientSolution s` = (a,b,c,d,e) ∈ ℚ^5 with
    (E8) 2b − a^2 = c8; (E6) b^2 + 2d − 2ac = c6; (E4) 2bd − c^2 − 2ae = c4; (E2) d^2 − 2ce = c2; (E0) e^2 = s^5.
`coefficientSolution_of_symmetricFiveFiveCase`. Irreducibility of R is not used from here on.

### B.2 Normalization and reduction to G2 = G3 = 0 (`FiveFive/Reduction.lean`)

`r := e/s^2`, `y := a/r`, `z := d/r^4`.
- `r_sq`: r^2 = s. `e_eq_r_pow_five`: e = r^5 (sign-sensitive). `b_formula`: b = (a^2 + c8)/2. `c_formula`: c = (d^2 − c2)/(2r^5). a = ry, d = r^4 z.

Cleared equations (`fiveFiveE2`, `fiveFiveE3`):
    E2(r,a,d) = a^4r^5 − 4a^2r^9 − 2a^2r^7 + 12a^2r^5 − 4ad^2 − 24ar^10 + 4ar^8 + 8ar^6 + 8dr^5 + 60r^11 − 39r^9 − 52r^7 + 32r^5
    E3(r,a,d) = 4a^2dr^10 − 8ar^15 − d^4 − 12d^2r^10 + 2d^2r^8 + 4d^2r^6 − 8dr^14 − 4dr^12 + 24dr^10 − 32r^20 + 52r^18 + 39r^16 − 60r^14
with E2 = 4r^5(b^2 + 2d − 2ac − c6), E3 = 4r^10(2bd − c^2 − 2ae − c4).

Normalized equations (`fiveFiveG2`, `fiveFiveG3`):
    G2(s,y,z) = −4s^3y^2 − 24s^3y + 60s^3 + s^2y^4 − 2s^2y^2 − 4s^2yz^2 + 4s^2y + 8s^2z − 39s^2 + 12sy^2 + 8sy − 52s + 32
    G3(s,y,z) = −32s^3 − 12s^2z^2 − 8s^2z + 52s^2 + 4sy^2z − 8sy − sz^4 + 2sz^2 − 4sz + 39s + 4z^2 + 24z − 60
`g2_zero`, `g3_zero`: E2(r,ry,r^4z) = r^5·G2(r^2,y,z), E3(r,ry,r^4z) = r^14·G3(r^2,y,z).

`FiveFiveReducedPoint s` = (y,z) with G2 = G3 = 0. Reciprocal symmetry: s^3·G2(1/s,z,y) = −G3(s,y,z) (not used in the final chain).

As polynomials in z:
    G2 = (−4s^2y) z^2 + (8s^2) z + [−4s^3y^2 − 24s^3y + 60s^3 + s^2y^4 − 2s^2y^2 + 4s^2y − 39s^2 + 12sy^2 + 8sy − 52s + 32]
    G3 = (−s) z^4 + (−12s^2 + 2s + 4) z^2 + (−8s^2 + 4sy^2 − 4s + 24) z + (−32s^3 + 52s^2 − 8sy + 39s − 60).

### B.3 Resultant in z (`Resultant.lean`, `ResultantCertificate.lean`, `ResultantPolynomial.lean`)

Mathlib route (side result, NOT on the final chain): `fiveFiveResultant s y := Polynomial.resultant G2Poly G3Poly`; `fiveFiveResultant_eq_zero_of_common_root`.

Explicit route (used): F(s,y) := `fiveFiveResultantFactor s y`, 104 integer terms (`ResultantCertificate.lean` lines 22–39). Docstring: "primitive resultant factor after removing s^2" (not proved, not needed).
- deg_y F = 16, deg_s F = 12.
- Coefficient of y^16: s^8; y^15, y^13: 0; y^14: −8s^7(s+2)(2s−3); y^12: 4s^6(24s^4 + 84s^3 − 177s^2 − 124s + 248); y^11: −384s^8.
- Coefficient of y^0: 12960000s^12 − 30931200s^11 − 16244128s^10 + 96898160s^9 − 41403359s^8 − 100331856s^7 + 93598176s^6 + 26662144s^5 − 61456128s^4 + 14524416s^3 + 11501568s^2 − 6815744s + 1048576.
- Constant term 2^20.

Multipliers: `fiveFiveBezoutU` (deg_s 9, deg_y 12, deg_z 3), `fiveFiveBezoutV` (deg_s 9, deg_y 10, deg_z 1).

**Bézout identity** (`fiveFive_bezout_identity`, ring): U·G2 + V·G3 = F(s,y). Hence G2 = G3 = 0 ⇒ F(s,y) = 0.

### B.4 P6, P28 and the ZMod 7 rational-root exclusion (`DiscriminantRoots.lean`)

    P6(s) = s^6 + 15s^5 − 1585s^4 + 3052s^3 − 1585s^2 + 15s + 1   (palindromic)
    P28(s) = 103680000 s^28 − 7521292800 s^27 + 169819194368 s^26 − 1294911396672 s^25 + … − 1308557312 s^2 − 162529280 s − 2097152
(degree 28, leading 103680000 = 2^11·3^4·5^4, constant −2^21; all 29 coefficients at `DiscriminantRoots.lean` lines 28–42.)

`fiveFive_discriminant_factors_have_no_rational_roots`: for all x ∈ ℚ, P6(x) ≠ 0 and P28(x) ≠ 0. Proof: homogenize; x = n/d lowest terms; n, d not both ≡ 0 (mod 7); exhaustive check over 48 pairs in (ZMod 7)^2 \ {0} by `decide` (`fiveFiveDiscriminantP6HomMod7_nonzero`, `…P28…`).

### B.5 Exact isolating brackets (`DiscriminantIntervals.lean`)

Endpoint signs (norm_num): P6(31/1000) > 0, P6(32/1000) < 0; P6(159/5) < 0, P6(319/10) > 0; P28(47/100) < 0, P28(471/1000) > 0; P28(786/25) > 0, P28(629/20) < 0; P28(1583/50) < 0, P28(3167/100) > 0.
Order: 0 < 31/1000 < 32/1000 < 47/100 < 471/1000 < 1 < 786/25 < 629/20 < 1583/50 < 3167/100 < 159/5 < 319/10.
Cuts: c1 ∈ [31/1000, 32/1000] (P6), c2 ∈ [47/100, 471/1000] (P28), c3 ∈ [786/25, 629/20] (P28), c4 ∈ [1583/50, 3167/100] (P28), c5 ∈ [159/5, 319/10] (P6), plus the cut 1. Samples 1/100, 1/5, 4/5, 2, 63/2, 317/10, 40 lie one in each of (0,c1), (c1,c2), (c2,1), (1,c3), (c3,c4), (c4,c5), (c5,∞).

### B.6 Real root isolation (`DiscriminantP6Roots.lean`, `DiscriminantP28Local.lean`, `DiscriminantP28Roots.lean`)

Method: on [a,b] put t = a + (b−a)x; exhibit rationals β_k > 0 with ±P(a+(b−a)x) = Σ β_k x^k(1−x)^{n−k} (identity by `ring`); positivity by `positivity`. On [a,∞): power basis with positive coefficients. Strict monotonicity from derivative sign + `strictMonoOn_of_deriv_pos`; existence by IVT; uniqueness by injectivity.

P6: > 0 on [0, 31/1000]; P6' < 0 on [31/1000, 32/1000]; < 0 on [32/1000, 1], [1,10], [10,159/5]; P6' > 0 on [159/5, 319/10]; > 0 on [319/10, ∞). ⇒ exactly two positive roots (`fiveFiveDiscriminantP6_existsUnique_low_root`, `_high_root`).

P28: < 0 on [0, 47/100]; P28' > 0 on [47/100, 471/1000]; > 0 on [471/1000, 4/5], [4/5, 786/25]; P28' < 0 on [786/25, 629/20]; < 0 on [629/20, 1583/50]; P28' > 0 on [1583/50, 3167/100] (`DiscriminantP28Local.lean`, u = 1583/50 + x/100); > 0 on [3167/100, ∞). ⇒ exactly three positive roots (`fiveFiveDiscriminantP28_exactly_three_positive_roots`).

### B.7 Real fibre family and critical-locus certificate (`ResultantCritical.lean`, 2647 lines)

`fiveFiveResultantFactorPolyReal s ∈ ℝ[X]`; homogenization H(s,u,v) = Σ_k Coeff_k(s) u^k v^{16−k}: continuous, H(s,y,1) = F(s,y), H(s,u,v) = v^16 F(s,u/v), H(s,u,0) = s^8u^16. `fiveFiveCriticalBezoutU s y` (deg_y 14; deg_s ≤ 69, ~80-digit integers), `fiveFiveCriticalBezoutV s y` (deg_y 15).

**Critical-locus identity** (`fiveFive_critical_bezout_identity`, ring, maxHeartbeats 4·10^6):
    U_c(s,y)·F(s,y) + V_c(s,y)·∂_yF(s,y) = 2^38 · s^5 · (s−1)^10 · (s+1)^3 · P6(s) · P28(s)^2.
`fiveFiveResultantFactorPolyReal_no_multiple_root`: for real s > 0, s ≠ 1, P6(s) ≠ 0, P28(s) ≠ 0, no y with F = ∂_yF = 0.

### B.8 Seven sample certificates (`SamplePositivityReal.lean`)

Each is an identity F(s₀, c·x) = (positive combination of squares), checked by `ring`, then `positivity`.

| s₀ | y = c·x | certificate |
|---|---|---|
| 1/100 | y = 30x | sparse diagonally-dominant SOS |
| 1/5 | y = 3x | same shape plus γ(x^3+1)^2 |
| 4/5 | y = x | Gram/LDL: F = Σ_{j=0}^{7} d_j ℓ_j(x)^2 + d_8 |
| 2 | y = 3x | Gram/LDL |
| 63/2 | y = 7x | Gram/LDL |
| 317/10 | y = 7x | Gram/LDL |
| 40 | y = 10x | Gram/LDL |

### B.9 Projective first-contact transport (`RootTransport.lean`)

`projectiveDiamond := {(u,v) ∈ [−1,1]×[0,1] : |u| + v = 1}` (compact); `projectivePoint y := (y/(|y|+1), 1/(|y|+1))`.

**General lemma** `no_root_along_critical_free_segment`: F, D, H, q, s > 0, with (i) F(q,y) > 0 ∀y; (ii) H continuous with the homogenization properties; (iii) ∂_y F = D; (iv) with a(t) := q + t(s−q), for all t ∈ [0,1], y: ¬(F(a(t),y) = 0 ∧ D(a(t),y) = 0). Then F(s,y) ≠ 0 ∀y.
Proof: Z := {(t,z) ∈ [0,1]×Diamond : H(a(t),z) = 0} compact; least t* with a zero; t* > 0 and v* ≠ 0 (infinity excluded by leading coefficient a(t)^8 ≠ 0); F(a(t*),·) ≥ 0 by IVT in t; so y* is a local minimum with value 0 ⇒ D = 0, contradicting (iv).

`fiveFiveResultantFactorReal_ne_zero_of_segment`; named cuts `fiveFiveP6LowCut`, `fiveFiveP28FirstCut`, `fiveFiveP28SecondCut`, `fiveFiveP28ThirdCut`, `fiveFiveP6HighCut`; `fiveFive_critical_cut_order`: 0 < c1 < c2 < 1 < c3 < c4 < c5; seven cell lemmas `fiveFive_critical_free_*`.

### B.10 Final assembly (`RootExclusion.lean`)

`fiveFiveResultantFactor_ne_zero` (s ∈ ℚ, 0 < s, s ≠ 1, y ∈ ℚ): F(s,y) ≠ 0. Cast to ℝ; s ≠ c_i since P6(s), P28(s) ≠ 0 for rational s; trichotomy locates s in an open cell; apply the segment lemma from that cell's sample.
`fiveFive_reduced_locus_empty`, `symmetric_five_five_impossible_from_reduced`.

---

## Part C. Logical flow: SymmetricFiveFiveCase s (s > 0, s ≠ 1) ⇒ False

1. P_s(X^2) = R(X)·(−R(−X)), R monic degree 5.
2. Coefficient comparison ⇒ (E8),(E6),(E4),(E2),(E0).
3. r := e/s^2, r^2 = s, e = r^5; b, c eliminated; y := a/r, z := d/r^4.
4. E2 = E3 = 0 ⇒ G2(s,y,z) = G3(s,y,z) = 0.
5. U G2 + V G3 = F ⇒ F(s,y) = 0.
6. F(s,y) ≠ 0: (a) s not a root of P6/P28 (ZMod 7) so s is in an open cell; (b) the cell's sample q has F(q,·) > 0; (c) along [q,s] no fibre has a multiple root; (d) projective first contact ⇒ no real root.
7. Contradiction.

---

## Part D. Nature of each certificate

**`decide`**: only the two ZMod 7 lemmas. No `native_decide`.

**`ring`/`field_simp`**: scaling; explicit even polynomial; symmetric product; e2/e3/g2/g3; Bézout identity; homogenization identities; all Bernstein/power-basis identities; the critical Bézout identity; the seven SOS identities.

**`norm_num`**: ten endpoint signs; orderings; Bernstein values at x = 1.

**Mathlib**: Gauss lemma (`Monic.irreducible_iff_irreducible_map_fraction_map`); scaleRoots API; `Monic.irreducible_iff_lt_natDegree_lt`; expand/contract (`contract_mul_expand`, `contract_expand`); UFD (`WfDvdMonoid.exists_irreducible_factor`, `irreducible_iff_prime`); `Polynomial.resultant` (side route); `Rat.num_div_den`, `Rat.reduced`; analysis (`Polynomial.hasDerivAt`, `strictMonoOn_of_deriv_pos`, IVT, `IsCompact.exists_isMinOn`, `IsLocalMin.hasDerivAt_eq_zero`).

---

## Part E. Subtle points

1. **s = 1.** The critical identity carries (s−1)^10, so transport across 1 is impossible; 1 is a sixth cut with samples 4/5 and 2 on either side. s = 1 ⇔ p = q, excluded.
2. **Where s > 0 is used.** Division by s, r; the factor s^5 in the critical identity; positivity of a(t) along the segment so H(a(t),u,0) ≠ 0; cell decomposition lives in (0,∞).
3. **Sign of r.** Swapping R ↔ −R(−X) sends r ↦ −r, y ↦ y, z ↦ z: the normalized point is invariant.
4. **s is a rational square** by (E0); only substituted inside ring identities.
5. **Irreducibility of R is unused after B.1.**
6. **Mathlib's Sylvester resultant is not on the chain**; F is defined by its 104 terms and its only needed property is U G2 + V G3 = F.
7. Only F ≠ 0 needs s > 0, s ≠ 1.
8. **Why real analysis:** the cuts are irrational.
9. Transport needs **positivity** of the sample fibre, not mere nonvanishing.
10. **Uniqueness of roots in brackets is essential**; derivative Bernstein certificates supply it.
11. P28 appears **squared** in the critical identity, P6 to the first power.
12. **Sizes.** F: 104 terms; U,V: deg_s 9; U_c,V_c: deg_s ≤ 69, ~80-digit integers. P28 Bernstein data: ~90-digit rationals.
13. The Capell parity split uses only UFD structure of ℚ[X] and deg P = 5 odd.
14. The 5+5 branch depends on p,q only through s > 0, s ≠ 1.
