# The quadratic–cubic (2+3) branch: front end of the Lean formalization

Repository: `/Users/vlad/projects/cuboid-2`, sources under `lean/Cuboid2/`.
All files below are free of `sorry` and `axiom`. Throughout, `ε ∈ {+1, −1}` is a
"physical sign" (`PhysicalSign`, values `ε.value = ±1`), `s = (p/q)²`
(`sharipovParameter p q`) with `p, q ≥ 1`, `gcd(p,q) = 1`, `p ≠ q`.

## 0. Upstream objects used by the branch (from `Polynomial.lean`, `Factorization.lean`)

* `normalizedQuintic s` — the monic quintic
  `P_s(X) = X⁵ + c₄X⁴ + c₃X³ + c₂X² + c₁X + c₀` with
  `c₄ = (2+s)(3−2s)`, `c₃ = 1+10s+4s²−14s³+s⁴`, `c₂ = −s(1−14s+4s²+10s³+s⁴)`,
  `c₁ = −s³(1+2s)(−2+3s)`, `c₀ = −s⁵`.
* Sharipov's polynomial `Q_{p,q}(t) = t¹⁰ + (2q²+p²)(3q²−2p²)t⁸ + (q⁸+10p²q⁶+4p⁴q⁴−14p⁶q²+p⁸)t⁶ − p²q²(q⁸−14p²q⁶+4p⁴q⁴+10p⁶q²+p⁸)t⁴ − p⁶q⁶(q²+2p²)(−2q²+3p²)t² − p¹⁰q¹⁰`;
  scaling identity `Q_{p,q}(t) = q²⁰ P_s(t²/q⁴)` (`eval_sharipov_scaling`).
* `QuadraticCubicCase s` :⇔ ∃ monic `A, B ∈ ℚ[X]`, `deg A = 2`, `deg B = 3`, `P_s = A·B`.
* `sharipovParameter_pos`, `sharipovParameter_ne_one` (`s ≠ 1` iff `p ≠ q`).

The final consumer is `Main.lean` (`quadratic_cubic_impossible`), which calls
`GaussianSession1Completion.quadratic_cubic_impossible_sharipov`.

---

## 1. `QuadraticReduction/SignedSquare.lean` — exact quadratic-factor remainder equations

**Definitions.** `quinticC4..C0 s` are the coefficients `c₄,…,c₀` above.
`monicQuadratic a b = X² + aX + b`. The quotient forced by comparing the top three coefficients:

```
forcedCubic s a b = X³ + (c₄ − a)X² + (a² − a c₄ + c₃ − b)X
                    + (−a³ + a²c₄ + 2ab − a c₃ − b c₄ + c₂).
```

Remainders of the Euclidean division `P_s ÷ (X² + aX + b)`:

```
R₁(s,a,b) = b² + (−3a² + 2a c₄ − c₃) b + (a⁴ − c₄a³ + c₃a² − c₂a + c₁)
R₀(s,a,b) = (c₄ − 2a) b² + (a³ − c₄a² + c₃a − c₂) b + c₀
```

`SatisfiesQuadraticRemainders s a b :⇔ R₁ = 0 ∧ R₀ = 0`.

**Theorems (all `ring` identities in ℚ[X]).**
* `normalizedQuintic_coefficient_form`: `P_s = X⁵ + c₄X⁴ + … + c₀`.
* `normalizedQuintic_quadratic_division`: `P_s = (X²+aX+b)·forcedCubic + R₁X + R₀` for all `s,a,b`.
* `factorization_of_quadratic_remainders`: `R₁=R₀=0 ⇒ P_s = (X²+aX+b)·forcedCubic`.
* `quadratic_remainders_of_forced_factorization`: converse (compare coefficients 0 and 1).

## 2. `QuadraticReduction/Extraction.lean` — from the abstract case to remainders and the compact model

* `exists_monicQuadratic_eq`: a monic natDegree-2 polynomial is `X²+aX+b` (Mathlib `isMonicOfDegree_two_iff`).
* `monic_cubic_coefficient_form`: monic cubic `B = X³ + B₂X² + B₁X + B₀`.
* `quadraticCubicCase_forced_factorization`: `QuadraticCubicCase s ⇒ ∃ a b, P_s = (X²+aX+b)·forcedCubic s a b`.
  Proof: uniqueness of quotient/remainder (Mathlib `div_modByMonic_unique`, `mul_divByMonic_cancel_left`) since the remainder `R₁X+R₀` has degree < 2; hence the given cubic `B` *is* `forcedCubic`.
* `quadraticCubicCase_remainders`: `QuadraticCubicCase s ⇒ ∃ a b, R₁=R₀=0`.
* `IsSignedSquare b :⇔ ∃ ε, ∃ c ∈ ℚ, b = ε c²`.
* `QuadraticFactorConstantsSignedSquare s :⇔ ∀ a b, P_s = (X²+aX+b)·forcedCubic ⇒ IsSignedSquare b` (the "C012" interface, discharged in §3).
* `sharipovParameter_isSquare`: `s = (p/q)²`.
* `compact_data_of_remainders`: given `s > 0`, `R₁=R₀=0`, `s = z²`, `b = ε c²`, there are `z ≠ 0`, `k ≠ 0`, `y` with
  `s = z²`, `a = z² k y`, `b = ε z⁴ k²`, `F₁(ε;z,k,y) = 0`, `F₀(ε;z,k,y) = 0`.
  (Take `k = c/z²`, `y = a/(z²k)`; `b ≠ 0` because `R₀ = 0` with `b = 0` would give `c₀ = −s⁵ = 0`.)
* `quadraticCubicCase_to_compact` (conditional endpoint): `QuadraticCubicCase s ∧ C012 ⇒ ∃ ε z k y, z≠0, k≠0, s=z², F₁=F₀=0`.

## 3. `QuadraticReduction/C012.lean` — the signed-square theorem for the quadratic constant (Newton polygon)

**Homogeneous quintic.** `homogeneousQuinticOver p q` = `H_{p,q}(X) = X⁵ + h₄X⁴ + h₃X³ + h₂X² + h₁X + h₀` with
```
h₄ = (2q²+p²)(3q²−2p²)
h₃ = q⁸ + 10p²q⁶ + 4p⁴q⁴ − 14p⁶q² + p⁸
h₂ = −p²q²(q⁸ − 14p²q⁶ + 4p⁴q⁴ + 10p⁶q² + p⁸)
h₁ = −p⁶q⁶(q² + 2p²)(−2q² + 3p²)
h₀ = −p¹⁰q¹⁰
```
(i.e. `Q_{p,q}(t) = H_{p,q}(t²)`); `homogeneousQuintic p q ∈ ℤ[X]` is its integral version.
`normalizedQuintic_scaleRoots_eq_homogeneous`: `P_s.scaleRoots(q⁴) = H_{p,q}` (so `H_{p,q}(X) = q²⁰ P_s(X/q⁴)`).
Coefficient lemmas `homogeneousQuintic_coeff_{zero,one,two,three}`; `homogeneousQuintic_monic`, `_degree`.

**Integrality (Gauss lemma).** For a rational factor `P_s = (X²+aX+b)·forcedCubic`:
* `scaledMonicQuadratic q a b = X² + q⁴a X + q⁸b` divides `H_{p,q}` over ℚ (`scaledMonicQuadratic_dvd_map_homogeneous`).
* `exists_integral_scaled_quadratic_coefficients`: `A := q⁴a`, `B := q⁸b` are integers
  (Mathlib `Polynomial.isIntegral_coeff_of_dvd` + `IsIntegrallyClosed ℤ`).
* `integralMonicQuadratic_dvd_homogeneous`: `X² + AX + B ∣ H_{p,q}` in ℤ[X] (Mathlib `Monic.dvd_of_fraction_map_dvd_fraction_map`).
* `integral_quadratic_quotient`: the cofactor is a monic integral cubic `X³ + DX² + EX + F`.
* `integral_quadratic_factor_coefficient_equations`: the four low coefficient equations
  ```
  B F = h₀ = −p¹⁰q¹⁰,   A F + B E = h₁,   F + A E + B D = h₂,   E + A D + B = h₃.
  ```
* `integral_quadratic_constant_dvd`: `B ∣ p¹⁰q¹⁰`.

**Local valuations at a prime `r ∣ pq`, with `κ := v_r(pq)` (`padicValNat r (p*q)`):**
* `homogeneousQuintic_coeff_three_not_dvd`: `r ∤ h₃` (since `h₃ ≡ q⁸` or `p⁸ mod r` and `gcd(p,q)=1`), so `v_r(h₃) = 0`.
* `homogeneousQuintic_coeff_two_core_not_dvd`, `homogeneousQuintic_coeff_two_padicValInt`: `v_r(h₂) = 2κ` exactly.
* `homogeneousQuintic_coeff_one_pow_dvd`: `r^{6κ} ∣ h₁`.
* `padicValInt_neg_parameter_powers`: `v_r(−pⁿqⁿ) = nκ`; so `v_r(h₀) = 10κ`.

**Tropical bookkeeping.** `boundedPadicValInt r cap z` = `v_r(z)` if `z ≠ 0`, `cap` if `z = 0` (cap `= 10κ+1`).
Lemmas `boundedPadicValInt_two_term_cancellation` (if `r^T ∣ x₁x₂ + y₁y₂` then the two term valuations are equal, or both `≥ T`) and
`boundedPadicValInt_three_term_cancellation` (if `v_r(x₁x₂ + y₁y₂ + z) = T` exactly then `min ≤ T` and a minimum below `T` is attained at least twice).

`quadratic_tropical_constant_classification` (pure `omega`): with `α=v(A), β=v(B), δ=v(D), η=v(E), φ=v(F)` and hypotheses
`β+φ = 10κ`; `β=0 ∨ α+δ=0 ∨ η=0`; `min(β+δ, α+η, φ) ≤ 2κ` with the double-minimum alternative below `2κ`;
`β+η = α+φ ∨ (6κ ≤ β+η ∧ 6κ ≤ α+φ)` — conclude `β ∈ {0, 2κ, 4κ, 6κ, 8κ}`, in particular `β` even
(`quadratic_tropical_constant_even`). (This is the statement that the lower Newton polygon of `H_{p,q}` at `r` has vertices `(0,10κ),(2,2κ),(3,0)`, and a degree-2 factor must pick up an even multiple of `κ` at `X⁰`.)

* `HomogeneousQuadraticConstantsLocallyEven p q :⇔ ∀ A B, X²+AX+B ∣ H_{p,q} → ∀ prime r ∣ pq, v_r(B)` even.
  Proved by `homogeneousQuadraticConstantsLocallyEven` (assembling the four coefficient equations with the lemmas above).
* `nat_isSquare_of_even_factorization`, `int_signedSquare_of_even_natAbs_factorization`: an integer with all prime multiplicities even is `ε d²`.
* `quadraticFactorConstantsSignedSquare_of_locallyEven`: primes `r ∤ pq` do not divide `B` at all (since `B ∣ p¹⁰q¹⁰`), so all multiplicities are even, `B = ε d²`, `b = B/q⁸ = ε (d/q⁴)²`.
* **`quadraticFactorConstantsSignedSquare_sharipov`**: C012 holds for every coprime `p,q ≥ 1`.
* **`quadraticCubicCase_to_compact_sharipov`**: `QuadraticCubicCase s ⇒ ∃ ε z k y, z≠0, k≠0, s=z², F₁=F₀=0` — unconditional entrance to the compact model.

## 4. `QuadraticReduction/CompactModel.lean` — the compact (signed-square) model

Substitution `s = z²`, `a = z² k y`, `b = ε z⁴ k²` (ε = ±1). Exact scalings (`compactF1_scaling`, `compactF0_scaling`, `ring`):
`R₁(z², z²ky, εz⁴k²) = z⁴ F₁(ε;z,k,y)`, `R₀(z², z²ky, εz⁴k²) = z⁶ F₀(ε;z,k,y)` with (writing `e = ε`, `e² = 1`)

```
F₁ = e²k⁴z⁴ − 3e k⁴y²z⁴ − 4e k³yz⁶ − 2e k³yz⁴ + 12e k³yz² − e k²z⁸ + 14e k²z⁶ − 4e k²z⁴ − 10e k²z² − e k²
     + k⁴y⁴z⁴ + 2k³y³z⁶ + k³y³z⁴ − 6k³y³z² + k²y²z⁸ − 14k²y²z⁶ + 4k²y²z⁴ + 10k²y²z² + k²y²
     + kyz⁸ + 10kyz⁶ + 4kyz⁴ − 14kyz² + ky − 6z⁶ + z⁴ + 2z²                       (27 terms)

F₀ = −2e²k⁵yz⁴ − 2e²k⁴z⁶ − e²k⁴z⁴ + 6e²k⁴z² + e k⁵y³z⁴ + 2e k⁴y²z⁶ + e k⁴y²z⁴ − 6e k⁴y²z²
     + e k³yz⁸ − 14e k³yz⁶ + 4e k³yz⁴ + 10e k³yz² + e k³y + e k²z⁸ + 10e k²z⁶ + 4e k²z⁴ − 14e k²z² + e k² − z⁴   (19 terms)
```
`compact_equations_of_remainders`: for `z ≠ 0`, `R₁=R₀=0 ⇒ F₁=F₀=0`.
`square_parameter_eq_zero_iff`: `z² = 0 ⇔ z = 0` (the fibre `s = 0`).

Auxiliary "lift" polynomials (used by the Bézout certificates):
```
ℓ(ε;z,k) = compactLiftDenominator = k¹⁰z² + 6k⁶z⁴ − k⁶z² − 2k⁶ + ε(2k⁴z⁴ + k⁴z² − 6k⁴ − z²)
compactLiftMiddle   = k⁶(z⁸+10z⁶+4z⁴−14z²+1) − k²(z⁸−14z⁶+4z⁴+10z²+1)
compactLiftBoundary = 2k⁸z⁶ + k⁸z⁴ − 6k⁸z² + 6z⁶ − z⁴ − 2z²
L₁ = −z² ℓ,  L₀ = k(ε·Middle − Boundary),  compactRecoveredY = −L₀/L₁
```
(the linear subresultant `L₁ y + L₀`; only `ℓ` is used downstream).

## 5. `QuadraticReduction/ExceptionalFibers.lean` — the 71-term projection and its boundary fibres

`compactProjectionPositive S K` = `Q₊(S,K)`, degree 10 in `K`, degree 8 in `S` (71 terms):
```
Q₊(S,K) = −S⁴K¹⁰
 + S²(S⁴ − 14S³ + 4S² + 10S + 1)K⁹
 − S(2S⁶ + 21S⁵ + 18S⁴ − 85S³ − 38S² + 85S − 6)K⁸
 + (S⁸ + 8S⁷ − 82S⁶ + 272S⁵ − 38S⁴ − 384S³ + 174S² + 40S + 1)K⁷
 + (12S⁸ + 122S⁷ − 11S⁶ − 550S⁵ + 212S⁴ + 498S³ − 331S² + 34S + 12)K⁶
 + 2(19S⁸ − 232S⁷ + 305S⁶ + 202S⁵ − 582S⁴ + 202S³ + 305S² − 232S + 19)K⁵
 + (12S⁸ + 34S⁷ − 331S⁶ + 498S⁵ + 212S⁴ − 550S³ − 11S² + 122S + 12)K⁴
 + (S⁸ + 40S⁷ + 174S⁶ − 384S⁵ − 38S⁴ + 272S³ − 82S² + 8S + 1)K³
 + S(6S⁶ − 85S⁵ + 38S⁴ + 85S³ − 18S² − 21S − 2)K²
 + S²(S⁴ + 10S³ + 4S² − 14S + 1)K
 − S⁴
```
`compactProjectionNegative S K = Q₋(S,K) := −Q₊(S,−K)`.
`reciprocalExceptionalQuartic S = S⁴ − 32S³ − 62S² − 32S + 1` =: `q₄(S)`.

Boundary fibres (all `ring`):
| | positive | negative |
|---|---|---|
| `K=1` | `Q₊(S,1) = 64(S−1)⁶(S+1)²` | `Q₋(S,1) = 16(S−1)⁴·q₄(S)` |
| `K=−1` | `Q₊(S,−1) = −16(S−1)⁴·q₄(S)` | `Q₋(S,−1) = −64(S−1)⁶(S+1)²` |
| `K=0` | `Q₊(S,0) = −S⁴` | `Q₋(S,0) = S⁴` |
| `S=1` | `Q₊(1,K) = −(K−1)⁶(K+1)⁴` | `Q₋(1,K) = (K+1)⁶(K−1)⁴` |
| `S=0` | `Q₊(0,K) = K³(K²+6K+1)²` | `Q₋(0,K) = K³(K²−6K+1)²` |
| `S=−1` | `Q₊(−1,K) = −(K−1)¹⁰` | `Q₋(−1,K) = (K+1)¹⁰` |

(`q₄(1) = −124`, `q₄(−1) = 4`; the quadratic chart factors have discriminants `−3, −3, −4`.)

## 6. `QuadraticReduction/ProjectionCertificate.lean`, `ProjectionCertificateNegative.lean` — Bézout certificates replacing the resultant

Positive sign: explicit polynomials with
`projectionBezoutAPositive = k⁶z² ℓ(+;z,k) y² + k⁵ C₁(z,k) y − k⁴ A₀(z,k)` (degree 2 in `y`),
`projectionBezoutBPositive = −k⁵z² ℓ(+;z,k) y³ − k⁴ C₁ y² + k³ B₁ y + B₀` (degree 3 in `y`),
where `C₁, A₀, B₁, B₀` are explicit polynomials in `z², k²` with ~25 integer terms each (private defs `projectionBezoutC1Positive`, `A0Positive`, `B1Positive`, `B0Positive` in the file; e.g. `A₀ = k¹²z⁴ + 12k⁸z⁶ − 2k⁸z⁴ − 4k⁸z² + 4k⁶z⁶ + 2k⁶z⁴ − 12k⁶z² + 35k⁴z⁸ − 22k⁴z⁶ − 27k⁴z⁴ + 18k⁴z² + 3k⁴ + 12k²z⁸ + 4k²z⁶ − 42k²z⁴ + 4k²z² + 12k² + z⁸ − 14z⁶ + 4z⁴ + 10z² + 1`).

* `compactProjectionPositive_bezout` (`ring`): `A·F₁(+) + B·F₀(+) = Q₊(z², k²)`.
* `compactProjectionPositive_of_compact_equations`: `F₁(+)=F₀(+)=0 ⇒ Q₊(z²,k²) = 0`.
* Negative sign: `projectionBezoutANegative`, `BNegative` with the sign-twisted private polynomials; `compactProjectionNegative_bezout`: `A⁻·F₁(−) + B⁻·F₀(−) = Q₋(z², k²)`; `compactProjectionNegative_of_compact_equations`.

Paper statement: *the resultant of `F₁, F₀` w.r.t. `y` is (up to the certified cofactors) `Q_ε(z²,k²)`; every common zero lies on `Q_ε(S,K)=0` with `S=z², K=k²`.*

## 7. `QuadraticReduction/Reciprocal.lean` — Cayley / fixed-field coordinates

```
x = (S−1)/(S+1),  y = (K−1)/(K+1)          (reciprocalCayleyX, reciprocalCayleyY)
U = x/y = (S−1)(K+1)/((S+1)(K−1)),  V = xy = (S−1)(K−1)/((S+1)(K+1))
```
Identities (`field_simp; ring`, with the displayed denominators nonzero):
* `reciprocal_UV`: `UV = (S−1)²/(S+1)²`.
* `reciprocal_one_sub_UV`: `1 − UV = 4S/(S+1)²`.
* `reciprocal_V_div_U`: `V/U = (K−1)²/(K+1)²`; `reciprocal_one_sub_V_div_U`: `1 − V/U = 4K/(K+1)²`.
* `reciprocal_one_sub_U_div_V`: `1 − U/V = −4K/(K−1)²`.
* `reciprocalCayleyX_inv`, `reciprocalCayleyY_inv`: `x(1/S) = −x(S)`, `y(1/K) = −y(K)`; `reciprocalU_inv`, `reciprocalV_inv`: the simultaneous involution `(S,K) ↦ (1/S,1/K)` fixes `U` and `V` (so `(U,V)` are coordinates on the quotient).

## 8. `QuadraticReduction/Characters.lean` — square characters on the compact chart

With `S = z²`, `K = k²` (`k² ≠ 1`):
* `rat_sq_add_one_ne_zero`: `x² + 1 ≠ 0` in ℚ.
* `reciprocal_product_isSquare`: `UV = ((z²−1)/(z²+1))²`.
* `reciprocal_one_sub_product_isSquare`: `1 − UV = (2z/(z²+1))²`.
* `reciprocal_positive_third_isSquare`: `1 − V/U = (2k/(k²+1))²`.
* `reciprocal_negative_third_eq_neg_square`: `1 − U/V = −(2k/(k²−1))²`.
* `e1_two_k_h_isSquare`: on `E1` (regular locus: `X ≠ 0, 3`, `D₀ ≠ 0`, `L ≠ 0`, `g ≠ 0`), if `1 − U(X,Y)V(X,Y)` is a square then `2·((Y+2)/X)·(X+1)` is a square (witness `w/(L g)`, using `M = L·(Y+2)/X`).

## 9. `QuadraticReduction/CompactBoundary.lean` — discharging the chart denominators

* `reciprocalExceptionalQuartic_ne_zero_of_pos`: `q₄(S) ≠ 0` for `S > 0`: dividing by `S²`, a root gives `(S + 1/S − 16)² = 320`, so `((S+1/S−16)/8)² = 5`, contradicting `¬IsSquare (5:ℚ)` (`norm_num`).
* `compactProjectionPositive_K_ne_one`: `Q₊(S,K)=0, S ≠ ±1 ⇒ K ≠ 1`. `compactProjectionNegative_K_ne_one`: `Q₋(S,K)=0, S>0, S≠1 ⇒ K ≠ 1`.
* `compactProjection ε` = `Q₊` or `Q₋`; `compactProjection_of_compact_equations`: `F₁=F₀=0 ⇒ Q_ε(z²,k²)=0`.
* `compact_square_chart_denominators`: for `z,k ≠ 0`, `z² ≠ 1`, `F₁=F₀=0`: `z² ≠ 0, k² ≠ 0, z²+1 ≠ 0, z²−1 ≠ 0, k²+1 ≠ 0, k²−1 ≠ 0`.
* `compact_equations_to_reciprocalQuotientC8`: positive sign ⇒ `C8(U(z²,k²), V(z²,k²)) = 0`; negative sign ⇒ `C8(V, U) = 0` (coordinates swapped).
* `compactReciprocalU ε z k`, `compactReciprocalV ε z k`: `(U,V)` for `ε = +`, `(V,U)` for `ε = −`.
* `reciprocal_product_ne_one_of_z_ne_zero`: `UV ≠ 1` (else `4z² = 0`); `reciprocal_one_sub_product_ne_zero_of_z_ne_zero`: `1 − UV = 4z²/(z²+1)² ≠ 0`.
* `compact_common_character_facts`: `IsSquare(UV)`, `UV ≠ 1`, `IsSquare(1−UV)`, `1−UV ≠ 0` for the sign-ordered pair (symmetric under swap).

## 10. `QuadraticReduction/QuotientTransport.lean` — the curve `C8` and the map `E1 → C8`

**The quotient curve** `reciprocalQuotientC8 U V` (29 terms, degree 8):
```
C8(U,V) = 16U⁶ − 128U⁵V + 44U⁴V³ + 272U⁴V² + 32U⁴V + 64U⁴
  − 76U³V⁴ − 256U³V³ − 180U³V² − 128U³V − 32U³
  − U²V⁶ + 32U²V⁵ + 134U²V⁴ + 228U²V³ + 87U²V² + 148U²V − 44U²
  − 34UV⁵ − 80UV⁴ − 60UV³ − 164UV² + 94UV − 12U
  + 31V⁴ + 48V³ − 46V² + 12V − 1
```
* `compactProjectionPositive_to_reciprocalQuotientC8`: `256·Q₊(S,K) = (S+1)⁸(K−1)⁶(K+1)⁴·C8(U,V)`.
* `compactProjectionNegative_to_reciprocalQuotientC8`: `256·Q₋(S,K) = −(S+1)⁸(K+1)⁶(K−1)⁴·C8(V,U)`.
* `reciprocalQuotientC8_of_compactProjection{Positive,Negative}`: the implications `Q_ε = 0 ⇒ C8 = 0`.
* `reciprocalQuotientC8Homogeneous A B D`: `64 D⁸ C8(A/(2D), B/D)`; each monomial `c U^i V^j` of C8 becomes `2^{6−i} c A^i B^j D^{8−i−j}` (`reciprocalQuotientC8_homogeneous`).

**Elliptic curve** `E1 : y² = x³ − 5x + 4` (`e1Residual X Y = Y² − X³ + 5X − 4`, `E1AffinePoint` = rational affine point; defined in `CharacterDescent.lean`).

**Forward map** `E1 → C8`: `U = f₁/(2f₃)`, `V = f₂/f₃` (`quotientForwardU/V`) with
```
f₁ = 511x⁴ + 24x³y − 3430x³ − 2186x²y − 3677x² + 4524xy + 26438x − 2982y − 22214
f₂ = 535x⁴ + 24x³y − 3140x³ − 1579x²y + 1380x² + 3636xy + 9346x − 2391y − 9307
f₃ = 583x⁴ + 24x³y − 715x³ − 293x²y − 3476x² + 2857xy + 9529x − 3491y − 7107
```
* `quotientForward_pair_certificate`: computing in the quadratic algebra `ℚ[x][y]/(y² − (x³−5x+4))` (pairs `(a,b) ↔ a + b y`, `quadraticPairMul/Pow/Scale/Term`), the 29-term homogeneous C8 evaluated at `(f₁,f₂,f₃)` reduces to `(0,0)` — a `norm_num`/`ring` identity in `x` (2·10⁶ heartbeats).
* `quotientForward_homogeneous_zero`, `quotientForward_on_reciprocalQuotientC8`: for every affine `P ∈ E1(ℚ)` with `f₃(P) ≠ 0`, `C8(U(P), V(P)) = 0`.

**Two-torsion translation** `τ(X,Y) = ((X−3)/(X−1), 2Y/(X−1)²)` (`e1TransportTranslateX/Y`); `e1TransportTranslate_residual`: `e1Residual(τ(X,Y)) = 4·e1Residual(X,Y)/(X−1)⁴`.
Cleared translation identities (`ring`):
```
(X−1)⁵ f₁(τ) = −4 N_U(X,Y),   (X−1)⁵ f₂(τ) = −2 N_V(X,Y),   (X−1)⁵ f₃(τ) = −2 D₀(X,Y)
```
so `quotientForwardU_translate`: `U(τ(P)) = e1U(P) = N_U/D₀`, `quotientForwardV_translate`: `V(τ(P)) = e1V(P) = N_V/D₀` (when `X ≠ 1`, `D₀ ≠ 0`).
* `e1_on_reciprocalQuotientC8`: `C8(e1U(P), e1V(P)) = 0` for `X ≠ 1, D₀ ≠ 0`.
* `e1_quotient_and_common_character`: additionally `1 − e1U·e1V = 2 F g²` when `X ≠ 3`.

## 11. `QuadraticReduction/CharacterDescent.lean` — translated coordinates and the `(k,h)` relation

Definitions on `E1` (`X,Y` translated coordinates):
```
L = 2X + Y − 2,   M = X² + 2Y − 1,   F = (X+1) L M
N_U = 593X⁵ + 2454X⁴ + 310X³Y − 4845X³ − 706X²Y − 8891X² + 4710XY + 17492X − 4218Y − 6803
N_V = 593X⁵ + 1861X⁴ + 310X³Y − 3714X³ + 170X²Y − 9954X² + 4758XY + 16361X − 5046Y − 5147
D₀  = 593X⁵ − 201X⁴ + 903X³Y − 880X³ + 1977X²Y + 4384X² − 5779XY − 12953X + 3091Y + 9057
U = N_U/D₀,  V = N_V/D₀           (e1U, e1V)
P(X) = 2062X³ − 1055X² − 8634X + 7723,   Q(X) = 593X² + 1807X − 3758
g = (P(X) − Q(X)·Y) / ((X−3) D₀)                     (e1G)
```
`e1CommonCharacterQuotient = (X+1)·(2797181X⁷ − 703298X⁶Y − 2078205X⁶ + 2682732X⁵Y − 13991627X⁵ − 1406596X⁴Y² + 13558504X⁴Y + 61460779X⁴ − 8572408X³Y² − 60074988X³Y − 165385561X³ + 4766956X²Y² + 12031106X²Y + 162793705X² + 54325648XY² + 122421632XY + 540967X − 56490256Y² − 90958632Y − 46137239)`.

Theorems:
* `e1_X_mul_M`: `X·M = (Y+2)·L` on `E1` (difference is `−e1Residual`). `e1_M_eq_L_mul_k`: `M = L·k` with `k := (Y+2)/X` (`X ≠ 0`).
* `e1_common_character_cleared` (`ring`): `(D₀² − N_U N_V)(X−3)² − 2F(P − QY)² = e1Residual · e1CommonCharacterQuotient`.
* **`e1_common_character`**: on `E1` with `D₀ ≠ 0`, `X ≠ 3`:  `1 − UV = 2 F g² = 2(X+1) L M g²`.
* `e1_line_substitution`: `e1Residual(X, kX − 2) = −X(X² − k²X + 4k − 5)` (line through `(0,−2)` of slope `k`).
* `e1HKRelation k h = h² − (k²+2)h + (k² + 4k − 4)`; **`e1_hk_relation`**: for `X ≠ 0`, with `k = (Y+2)/X`, `h = X+1`: `h² − (k²+2)h + k² + 4k − 4 = 0`.
* `e1_hk_discriminant`: `(k²+2)² − 4(k²+4k−4) = k⁴ − 16k + 20`.
* `e1_negative_squareclass_relation`: `e1HKRelation(−2U, −v²) = 4U²v² + 4U² − 8U + v⁴ + 2v² − 4`; `e1_negative_U_discriminant`: its `U`-discriminant is `−16(v²+2)(v⁴+v²−4)`.
* `e1_positive_squareclass_relation`: `e1HKRelation(2U, v²) = −4U²v² + 4U² + 8U + v⁴ − 2v² − 4`; `e1_positive_discriminant`: `((2u²)⁴ − 16(2u²) + 20)/4 = 4u⁸ − 8u² + 5`.
* `e1_positive_octic_to_dplus`: `r² = 4u⁸ − 8u² + 5 ⇒ ∃ P ∈ D+(ℚ)` with square abscissa.

Summary for the paper: with `k = (Y+2)/X`, `h = X+1`, `M = Lk`, `F = h L² k`, so `1 − UV = 2 k h · (L g)²`; squareness of `1−UV` gives `z² = 2kh`.

## 12. `QuadraticReduction/TransportPolynomial.lean` — executable sparse polynomial checker

Sparse integer polynomials as lists of `(i, j, c)` (monomial `c Uⁱ Vʲ`) or `(i, u, v, c)` (`c xⁱ Uᵘ Vᵛ`). Executable `transportParse*`, `transportEvalUVTerms`, `transportEvalXUVTerms`, normalization (`transportNormalizeUVTerms`, descending lex order, merging like terms), `transportMulUVTerms`, `transportAddUVTerms`, `transportNegUVTerms`, `transportPowUVTerms`, and `transportSubstituteLinearXTerms d T A B` = `A^d · T(−B/A, U, V)` cleared.
Soundness lemmas (by induction): `transportEvalNormalizeUVTerms`, `transportEvalMulUVTerms`, `transportEvalAddUVTerms`, `transportEvalNegUVTerms`, `transportEvalPowUVTerms`, `transportEvalSubstituteLinearXTerms` (evaluation over ℚ commutes with each operation; the substitution lemma needs `deg_x ≤ d` and `A(U,V) ≠ 0`).
This is what allows `native_decide` equalities of term lists to be transported to identities of rational functions.

## 13. `QuadraticReduction/TransportCertificateData.lean` (generated, 406 KB) and `TransportExceptionData.lean` (generated, 48 KB)

Headers: generated by `research/lean_generation/session1_transport/generate_transport_certificates.py` (checksum `03857187…aade2b`) and `generate_exception_certificates.py` (checksum `2d74f250…965c72`). Contents (term counts):

| name | terms | meaning |
|---|---|---|
| `quotientInverseACertificateTerms` | 65 | `A(U,V)`, degree 12 in U, coefficient of `x` in the inverse linear subresultant |
| `quotientInverseBCertificateTerms` | 65 | `B(U,V)`, constant term of that subresultant |
| `quotientInverseR5CertificateTerms` | 18 | `R5(x,U,V)` |
| `quotientInverseE6CertificateTerms` | 19 | `E6(x,U)` |
| `quotientInverseR5BackCertificateTerms` | 1398 | `A⁵ R5(−B/A,U,V)` expanded (degree 61 in U) |
| `quotientInverseE6BackCertificateTerms` | 1962 | `A⁶ E6(−B/A,U)` expanded |
| `quotientInverseR5BackQuotientTerms` | 1005 | exact quotient `R5Back / C8` |
| `quotientInverseE6BackQuotientTerms` | 1485 | exact quotient `E6Back / C8` |
| `transportExceptionC8Terms` | 29 | C8 |
| `transportExceptionABezoutLeftTerms` / `RightTerms` | 214 / 219 | Bézout cofactors for `(C8, A)` |
| `transportExceptionAFactorTerms` | 51 | univariate factor for `A = 0` |
| `transportExceptionRemovedLinearTerms` | 65 | `352225·A + 576·B` |
| `transportExceptionRemovedBezoutLeftTerms` / `RightTerms` | 214 / 219 | Bézout cofactors for `(C8, 352225A+576B)` |
| `transportExceptionRemovedFactorTerms` | 51 | univariate factor for the removed fibre |

plus evaluation wrappers `quotientInverseACertificate U V`, etc.

## 14. `QuadraticReduction/QuotientInverse.lean` — inverse of `E1 → C8`

Definitions: `A = quotientInverseA U V`, `B = quotientInverseB U V` (the 65-term certificates), recovered abscissa `x = −B/A` (`quotientInverseX`). Writing `f₁ − 2U f₃ = a₁(x,U)·y + b₁(x,U)` and `f₂ − V f₃ = a₂(x,V)·y + b₂(x,V)`:
```
a₁ = (24x³ − 2186x² + 4524x − 2982) − 2U(24x³ − 293x² + 2857x − 3491)
b₁ = (511x⁴ − 3430x³ − 3677x² + 26438x − 22214) − 2U(583x⁴ − 715x³ − 3476x² + 9529x − 7107)
a₂ = (24x³ − 1579x² + 3636x − 2391) − V(24x³ − 293x² + 2857x − 3491)
b₂ = (535x⁴ − 3140x³ + 1380x² + 9346x − 9307) − V(583x⁴ − 715x³ − 3476x² + 9529x − 7107)
```
recovered ordinate `y = −b₁(x,U)/a₁(x,U)` (`quotientInverseY`).
```
R5(x,U,V) = (4U−3V+1)x⁵ + (4U−V−4)x⁴ + (−64U+34V+24)x³ + (88U−11V−72)x² + (8U−95V+87)x + (−44U+80V−36)
E6(x,U)   = (2U−1)²x⁶ + (−12U²+36U−24)x⁵ + (−88U+83)x⁴ + (20U²−20U+4)x³ + (388U−388)x² + (−12U²−568U+580)x + (−4U²+264U−260)
```
* `quotientInverse_projection_identity` (`ring`): `a₁b₂ − a₂b₁ = (x−2)(576x − 352225)·R5(x,U,V)`.
* `quotientInverse_elliptic_substitution_identity` (`ring`): `b₁² − a₁²(x³−5x+4) = −(576x − 352225)(x² − 5)·E6(x,U)`.
* `quotientInverseR5_homogeneous` / `E6_homogeneous`: `A⁵ R5(x,U,V) = R5Back(U,V)`, `A⁶ E6(x,U) = E6Back(U,V)` at `x = −B/A` (via the executable substitution; `native_decide` shows the substituted normal form equals the stored `…BackCertificateTerms`).
* `quotientInverseR5_back_divisible` / `E6_back_divisible`: `R5Back = R5Quot·C8`, `E6Back = E6Quot·C8` (`native_decide` on the sparse product).
* `quotientInverseR5_zero`, `quotientInverseE6_zero`: `C8(U,V)=0, A ≠ 0 ⇒ R5(x,U,V) = 0` and `E6(x,U) = 0`.
* `quotientInverse_first_equation`: `f₁(x,y) − 2U f₃(x,y) = 0` (needs `a₁ ≠ 0`).
* `quotientInverse_second_equation`: `f₂(x,y) − V f₃(x,y) = 0` (from `R5 = 0` and the determinant identity).
* `quotientInverse_on_E1`: `y² = x³ − 5x + 4` (from `E6 = 0`).
* **`reciprocalQuotientC8_to_E1_regular`**: `C8(U,V)=0, A≠0, a₁≠0, f₃(x,y)≠0 ⇒ ∃ P ∈ E1(ℚ)` with `U(P)=U, V(P)=V`.
  (The hypothesis `f₃ ≠ 0` is necessary: the removable base point `−4P₀` with `x = 352225/576` has `A ≠ 0`, `a₁ ≠ 0`, but `f₁=f₂=f₃=0`.)

## 15. `QuadraticReduction/TransportExceptions.lean` — closing the three inverse denominators

**Rational-root checker.** For a list of integer coefficients, `exceptionPolynomial_ne_zero_of_mod p`: if the homogenized polynomial `Σ cᵢ n^{d−i} dⁱ` has no zero `(n,d) ≠ (0,0)` over `𝔽_p` (checked by `native_decide`), the polynomial has no rational root (because `num, den` of a reduced fraction are not both `≡ 0 mod p`). Used with:
* `D₁(t) = 1331t² − 12t − 1444`, `D₂(t) = 256t³ + 48t² − 729t + 361`, `D₈(t) = 1000t⁸ − 4312t⁷ + 1720t⁶ + 7260t⁵ − 677t⁴ − 3257t³ − 983t² − 107t − 4`, `t³ − 69t² − 117t − 79`, `3t³ + t² − 19t + 16`: mod 13.
* `t⁵ + 37t⁴ − 23t³ − 206t² + 241t − 71`, and two degree-5 polynomials with 60–100-digit coefficients (`exceptionPlusQuinticCoefficients`, `exceptionLimitQuinticCoefficients`): mod 2.
* `24t³ − 293t² + 2857t − 3491` (the `y`-coefficient of `f₃`): mod 41.
* a degree-19 polynomial `S₁₉` (`exceptionSimultaneous19Coefficients`, leading coefficient 1003290624, constant 1703243972271104000000): mod 31.
* `t² ≠ 5` and `t² − t − 1 ≠ 0` over ℚ (golden ratio: `(2t−1)² = 5`).

**(i) `A = 0`.** `quotientInverseA_exception_bezout` (`native_decide` on the sparse normal form, then evaluation lemmas):
`ℒ(U,V)·C8(U,V) + ℛ(U,V)·A(U,V) = 4(U−1)⁴(U+1)⁴(2U−1)¹⁸ D₁(U) D₂(U)² D₈(U)²` =: `quotientInverseAExceptionFactor U`.
Fibres, using the admissibility hypotheses `IsSquare(UV)`, `UV ≠ 1`:
* `U = 1`: `C8(1,V) = −(V−1)⁴(V+3)²`; `V = 1` gives `UV = 1`; `V = −3` gives `UV = −3`, not a square.
* `U = −1`: `C8(−1,V) = −(V+1)³(V³ − 69V² − 117V − 79)`; `V = −1` gives `UV = 1`; the cubic has no rational root.
* `U = 1/2`: `C8(1/2,V) = −(V−1)(V⁵ + 37V⁴ − 23V³ − 206V² + 241V − 71)/4`; `V = 1` gives `UV = 1/2`, not a square; the quintic has no rational root.
* `D₁, D₂, D₈` have no rational root.
⇒ `quotientInverseA_ne_zero_of_admissible`.

**(ii) `a₁ = 0`** (`quotientInverseA1_ne_zero_of_admissible`). From `R5 = 0` and the determinant identity, `a₁ = 0 ⇒ a₂ b₁ = 0`.
* Case `a₂ = 0`: then `U = f₁ʸ/(2f₃ʸ)`, `V = f₂ʸ/f₃ʸ` where `fᵢʸ` are the `y`-coefficients (cubics in `x`; `f₃ʸ ≠ 0` by mod 41). Identity `exception_simultaneous_factor_identity`: `C8hom(f₁ʸ, f₂ʸ, f₃ʸ) = −64(x−2)³(576x − 352225)·S₁₉(x)`. `x = 2` gives `U = V = −1`, `UV = 1`; `x = 352225/576` gives `U₊ = 2507654733463/5773889467838`, `V₊ = 2739947416519/3008594206519` with `U₊V₊` not a square (`norm_num [Rat.isSquare_iff]`); `S₁₉` has no rational root.
* Case `b₁ = 0`: `exception_a1_b1_resultant_identity`: `a₁·f₃ᶜ − f₃ʸ·b₁ = (x−2)(576x − 352225)(x² − 5)(3x³ + x² − 19x + 16)` (`f₃ᶜ = 583x⁴ − 715x³ − 3476x² + 9529x − 7107`). `x = 2 ⇒ U = −1` (case above); `x = 352225/576 ⇒ U = U₊`, and `exceptionPlusFibreIdentity`: `c·C8(U₊, V) = −(3008594206519V − 2739947416519)·Quintic₊(V)` (`c` a 76-digit constant), so `V = V₊` (non-square product) or a root of `Quintic₊` (none); `x² = 5` impossible; the cubic has no rational root.

**(iii) `f₃(x,y) = 0` on the reconstructed point** (`quotientInverseF3_ne_zero_of_admissible`). Writing `f₃ = f₃ʸ y + f₃ᶜ` and using `y² = x³−5x+4`:
`exception_curve_f3_resultant_identity`: `(f₃ᶜ)² − (f₃ʸ)²(x³ − 5x + 4) = −(576x − 352225)(x² − 5)(x² − x − 1)³`, so `f₃ = 0` on `E1` forces `x = 352225/576` (`exception_curve_f3_forces_removed_x`). Then `−B/A = 352225/576`, i.e. `352225·A + 576·B = 0`. Second Bézout identity (`quotientInverseRemoved_exception_bezout`, `native_decide`):
`ℒ'·C8 + ℛ'·(352225A + 576B) = 4(U−1)⁴(U+1)⁴(2U−1)¹⁶ (5773889467838U − 2507654733463)(1316366220366073678142U − 731754020216156986855) D₁ D₂² D₈²`.
New fibres: `U = U₊` (as above) and `U_lim = 731754020216156986855/1316366220366073678142` with `exceptionLimitFibreIdentity`: `c'·C8(U_lim, V) = −(632597885616799462855V − 678770002969523258551)·Quintic_lim(V)`; `V_lim = 678770002969523258551/632597885616799462855` gives non-square `U_lim V_lim`; `Quintic_lim` has no rational root.

**Wrappers.** `reciprocalQuotientC8_admissible_denominators`: on `C8 = 0`, `IsSquare(UV)`, `UV ≠ 1`: `A ≠ 0 ∧ a₁ ≠ 0 ∧ f₃(x,y) ≠ 0`.
`reciprocalQuotientC8_to_E1_admissible`: such `(U,V)` is the image of an affine `E1` point. `compact_to_E1AffinePoint`: every compact solution (`z,k ≠ 0`, `z² ≠ 1`) is the forward image of an affine `E1` point, in the sign-ordered coordinates.

## 16. `QuadraticReduction/TransportCompletion.lean` — regular chart into the descent

* `E1AffinePoint.transportTranslate Q (X≠1)` = `τ(Q)`; `transportTranslate_X_ne_one` (`τ(Q).X ≠ 1`), `transportTranslate_involutive_X/Y` (`τ∘τ = id`).
* Private facts: `U·V` at `(3,−4)` and at `(0,−2)` is not a rational square (`norm_num`).
* **`regular_quotient_common_character_impossible`** (assumes `DPlusSquareAbscissaClassified`): for `Q ∈ E1(ℚ)` with `Q.X ≠ 1`, `f₃(Q) ≠ 0`, `IsSquare(UV)`, `UV ≠ 1`, `IsSquare(1−UV)`, `1−UV ≠ 0` — contradiction.
  Proof: `P := τ(Q)`; `D₀(P) ≠ 0` (from `f₃(Q) ≠ 0`); `U(Q) = e1U(P)`, `V(Q) = e1V(P)`.
  `P.X ≠ 0`: else `Q.X = 3`, `Q.Y = ±4`; `(3,4)` has `UV = 1`, `(3,−4)` has non-square `UV`.
  `P.X ≠ 3`: else `Q.X = 0`, `Q.Y = ±2`; `(0,2)` has `UV = 1`, `(0,−2)` non-square.
  `L(P) ≠ 0`, `g(P) ≠ 0`: else `1 − UV = 2Fg² = 0`.
  Then apply `regular_e1_common_character_impossible` (§19).

## 17. `QuadraticReduction/SquareclassDescent.lean` — exclusion of the negative square class (mod 8/16/64)

* `negAux m n = −(m² + 2n²)(m⁴ + m²n² − 4n⁴)` (`= n⁶·negativeSquareclassRhs(m/n)`).
* Finite checks (kernel `decide` in `ZMod`): for `m,n` both odd `negAux ≡ 6 (mod 8)`; `m` odd, `n` even: `≡ 3 or 7 (mod 8)`; `m ≡ 0 (mod 4)`, `n` odd: `≡ 8 (mod 16)`; `m ≡ 2 (mod 4)`, `n` odd: `≡ 32 (mod 64)`. None is a square mod 8/16/64 respectively. `m,n` both even contradicts coprimality.
* `negAux_not_isSquare_of_coprime`: `¬IsSquare(negAux m n)` for coprime `m,n`.
* `negativeSquareclassRhs v = −(v²+2)(v⁴+v²−4)`; `negativeSquareclassRhs_not_isSquare` (clear `den⁶`, Mathlib `Rat.isSquare_intCast_iff`).
* `negativeSquareclassRhs_isSquare_of_relation`: if `e1HKRelation(−2U, −v²) = 0` then `negativeSquareclassRhs v = (2((v²+1)U − 1))²` (completing the square: `negRhs = (2((v²+1)U−1))² − (v²+1)·e1HKRelation(−2U,−v²)`).
* **`e1_negative_squareclass_impossible`**: `e1HKRelation(−2U, −v²) ≠ 0` for all rational `U, v`.

## 18. `QuadraticReduction/ValuationDescent.lean` — `k = 2εu²`, `h = εv²`

Setting: `k, h ≠ 0`, `z² = 2kh`, `h² − (k²+2)h + (k²+4k−4) = 0`. Write `α = v_p(k)`, `β = v_p(h)`, `γ = v_p(z)`.
* `quadratic_constant_ne_zero`: `k² + 4k − 4 ≠ 0` (else `(k+2)² = 8`).
* `valuation_three_terms_no_unique_min`: in `a + b + c = 0` (all nonzero) no term has strictly smallest valuation (Mathlib `padicValRat.lt_add_of_lt`).
* Odd `p`: if `α > 0` then `v(k²+2) = v(k²+4k−4) = 0`, term valuations `2β, β, 0` ⇒ `β = 0`; `2γ = α + β = α`. If `α < 0`: `v(k²+2) = v(k²+4k−4) = 2α`, term valuations `2β, 2α+β, 2α` ⇒ `β ∈ {0, 2α}`; `2γ = α + β` ⇒ `α` even. `α = 0` trivial. **`odd_prime_k_valuation_even`**: `v_p(k)` is even for every odd prime `p`.
* `p = 2`: `2γ = 1 + α + β`. If `α < 0`, same term analysis ⇒ `β ∈ {0, 2α}` ⇒ `α` odd (`two_negative_k_valuation_odd`). If `α ≥ 0`: discriminant `k⁴ − 16k + 20` must be a rational square (`hk_discriminant_num_isSquare`: `(2h − (k²+2))² = k⁴ − 16k + 20`), i.e. with `k = m/n` reduced, `hkDiscriminantNumerator m n = m⁴ − 16mn³ + 20n⁴` is an integer square. `α = 0` (`m,n` odd): `≡ 5 (mod 8)`, not a square. `α ≥ 2` (`4 ∣ m`, `n` odd): `≡ 20 (mod 32)`, not a square (`decide` in `ZMod 8`, `ZMod 32`). Hence `α = 1`. **`two_k_valuation_odd`**: `v_2(k)` is odd.
* `rat_signed_two_square_of_valuations`: odd `v_2`, even `v_p` (odd `p`) ⇒ `k = 2εu²`, `u ≠ 0` (via `N = |num|·den`, `N/2` a perfect square by `nat_isSquare_of_even_factorization`; `u = d/den`).
* **`e1_hk_signed_squareclasses`**: `∃ ε, u, v ≠ 0` with `k = 2εu²`, `h = εv²` (`v = z/(2u)`, using `z² = 2kh = 4εu²h`).
* **`e1_hk_to_dplus_square_abscissa`**: positive class: with `k = 2u²`, `h = v²` the relation gives `(v² − 2u⁴ − 1)² = 4u⁸ − 8u² + 5` (so `(u, r := v² − 2u⁴ − 1)` is a rational point on the octic), hence a `D+` point with square abscissa; negative class: `k = −2u²`, `h = −v²` contradicts `e1_negative_squareclass_impossible (u²) v`.

## 19. `QuadraticReduction/Completion.lean` — the regular-locus contradiction

* **`e1_hk_to_octic`**: `k,h ≠ 0`, `z² = 2kh`, relation ⇒ `∃ Q ∈ Octic(ℚ)` with `k = 2Q.u²` (same case split as §18).
* **`regular_e1_common_character_impossible`** (assumes `DPlusSquareAbscissaClassified`): for `P ∈ E1(ℚ)` with `X ≠ 0`, `D₀ ≠ 0`, `X ≠ 3`, `L ≠ 0`, `g ≠ 0`, `IsSquare(1−UV)`, `1−UV ≠ 0` — contradiction.
  Proof: `z² = 2kh` from `e1_two_k_h_isSquare` with `k = (Y+2)/X`, `h = X+1`; `k,h ≠ 0` since `1−UV = 2hL²k g² ≠ 0`; relation from `e1_hk_relation`; get octic `Q` with `k = 2Q.u²`; by `octic_classified_of_dplus_classified`, `Q.u = ±1`, so `k = 2`; then `h² − 6h + 8 = 0`, `h ∈ {2, 4}`. `h = 4 ⇒ X = 3` (excluded); `h = 2 ⇒ X = 1`, `k = 2 ⇒ Y = 0`, but `D₀(1,0) = 593 − 201 − 880 + 4384 − 12953 + 9057 = 0`, contradicting `D₀ ≠ 0`.

## 20. `DPlus/Basic.lean` — the genus-2 curve `D+` and the octic cover

```
D+ : R² = 4a⁵ − 8a² + 5a          (dplusRhs)
Octic: r² = 4u⁸ − 8u² + 5          (octicRhs)
```
`DPlusAffinePoint`, `OcticPoint` (rational affine points); `HasSquareAbscissa P :⇔ ∃ u, P.a = u²`.
`dplus_pullback_identity`: `dplusRhs(u²) = u²·octicRhs(u)`; `OcticPoint.toDPlus : (u, r) ↦ (u², ur)` lands on `D+` with square abscissa.
Known points: `dplusZero = (0,0)`, `dplusOnePlus = (1,1)`, `dplusOneMinus = (1,−1)`.
Infinity chart: `infinityRelation t w :⇔ w = t²(1 − 2w³ + (5/4)w⁴)`; the truncation `w = t² − 2t⁸ + (5/4)t¹⁰` satisfies it up to an explicit `t¹⁴·(…)` residual (`infinity_series_residual_order`, `ring`). (Not used by the front end.)

## 21. `DPlus/GlobalBridge.lean` — the global interface and its equivalence with the octic statement

* `DPlusSquareAbscissaClassified :⇔ ∀ P ∈ D+(ℚ)` affine with square abscissa, `P ∈ {(0,0), (1,1), (1,−1)}`.
* `OcticRationalPointsClassified :⇔ ∀ P ∈ Octic(ℚ)`, `(u, r) ∈ {(1,1), (1,−1), (−1,1), (−1,−1)}`.
* `five_not_rational_square`.
* `dplus_eq_zero_of_abscissa_eq_zero`: `a = 0 ⇒ P = (0,0)`.
* `DPlusAffinePoint.toOcticOfSquare`: `a = u² ≠ 0 ⇒ (u, R/u)` is an octic point, with `toOcticOfSquare_toDPlus` a section.
* `OcticPoint.toDPlus_ne_zero`: an octic point never maps to `(0,0)` (would need `r² = 5`).
* `octic_classified_of_dplus_classified` and `dplus_classified_of_octic_classified`; **`dplus_classified_iff_octic_classified`**: the two interfaces are equivalent. (Fibre `a = 0` handled by `dplus_eq_zero_of_abscissa_eq_zero`; fibres `a = 1` by `u = ±1`, `R = ur`.)

## 22. `QuadraticReduction/GaussianCompletion.lean` — assembling the branch given the octic classification

* `compact_to_E1AffinePoint_regular`: for a compact solution (`z,k ≠ 0`, `z² ≠ 1`, `F₁=F₀=0`), there is `P ∈ E1(ℚ)` with `U(P) = compactReciprocalU`, `V(P) = compactReciprocalV`, and `f₃(P) ≠ 0`.
* `quotient_inverse_point_X_ne_one`: a regular point with `UV ≠ 1` has `X ≠ 1` (the fibre `X = 1` is `(1,0)`, where `U·V = 1`).
* **`quadratic_cubic_impossible_sharipov_of_octic_classified`**: `OcticRationalPointsClassified → ¬QuadraticCubicCase(sharipovParameter p q)` for `p,q ≥ 1`, coprime, `p ≠ q`.
  Chain: `quadraticCubicCase_to_compact_sharipov` → `z² ≠ 1` from `s ≠ 1` → `compact_to_E1AffinePoint_regular` → `compact_common_character_facts` transported along `U(P), V(P)` → `X ≠ 1` → `regular_quotient_common_character_impossible` with `dplus_classified_of_octic_classified`.

## 23. `QuadraticReduction/GaussianClassification.lean` — from the two Gaussian elliptic conclusions to the octic classification

Objects from `GaussianCover.lean`/`GaussianSplit.lean` (outside scope, summarized): `GaussianRat = ℚ(i)`; `q(u) = (2u⁴ − 1) + i(2u² − 2)`; covers `C₀ : v² = q(u)` (`GaussianCoverZeroPoint`) and `C₁ : w² = −i·q(u)` (`GaussianCoverOnePoint`), `u ∈ ℚ`, `v,w ∈ ℚ(i)`; elliptic quotients `E₀ : Y² = X³ + 2iX² − (2+4i)X` with point `P₀ = (2,2)`, and `E₁ : Y² = X³ + 2X² + (2+4i)X` with 2-torsion `T = (0,0)`; maps `C₀ → E₀` (`toE0`, with `x = 2u²`), `C₁ → E₁` (`toE1`, `x = −2i u²`). `octic_to_gaussian_cover`: every rational octic point lifts to `C₀` (even reduced denominator of `u`) or `C₁` (odd), with the same `u`, because `4u⁸ − 8u² + 5 = (2u⁴−1)² + (2u²−2)² = N(q(u))` splits over ℚ(i).

* `GaussianCoverZeroClassified :⇔ ∀ C ∈ C₀(ℚ), C.toE0 ∈ {P₀, −P₀}`.
* `GaussianCoverOneEllipticClassified :⇔ ∀ C ∈ C₁(ℚ), C.toE1 ∈ {O, T}`.
* `gaussianCoverOne_toE1_ne_zero` (affine points are not `O`), `gaussianCoverOne_toE1_ne_torsion` (`x = 0 ⇒ u = 0 ⇒ w² = −2 + i ⇒ N(w)² = 5`, impossible) ⇒ `gaussianCoverOne_empty`: `C₁(ℚ) = ∅`.
* `gaussianCoverZero_u_sq_eq_one`: `toE0 = ±P₀ ⇒ 2u² = 2 ⇒ u² = 1`.
* **`octic_classified_of_gaussian_covers`**: the two conclusions imply `OcticRationalPointsClassified` (`u = ±1 ⇒ r² = 1`).

`GaussianSession1Completion.lean` (outside scope) proves `GaussianCoverZeroClassified` and uses `GaussianActualTorsion.gaussianCoverOneEllipticClassified`, yielding `octicRationalPointsClassified` and the unconditional `quadratic_cubic_impossible_sharipov`.

---

## (b) Logical flow: `QuadraticCubicCase s` ⟹ rational octic point with `u ≠ ±1` ⟹ contradiction

1. **Extraction** (`Extraction`, `SignedSquare`): `P_s = (X²+aX+b)·forcedCubic`, i.e. `R₁(s,a,b) = R₀(s,a,b) = 0`.
2. **C012** (`C012`): `b = ε c²`. Scale to `H_{p,q}`: `A = q⁴a, B = q⁸b ∈ ℤ`, `X²+AX+B ∣ H_{p,q}`; Newton polygon at each `r ∣ pq` (`v_r(h₀)=10κ, v_r(h₂)=2κ, v_r(h₃)=0, v_r(h₁) ≥ 6κ`) gives `v_r(B) ∈ {0,2κ,…,8κ}` even; primes `r ∤ pq` do not divide `B`; so `B = ε d²`.
3. **Compact model** (`CompactModel`): `s = z²`, `a = z²ky`, `b = εz⁴k²`, `z,k ≠ 0`; `F₁(ε;z,k,y) = F₀(ε;z,k,y) = 0`.
4. **Projection** (`ProjectionCertificate(Negative)`): `Q_ε(z², k²) = 0` via the Bézout identity.
5. **Chart denominators** (`CompactBoundary`, `ExceptionalFibers`): `S = z² ∉ {0, −1, 1}` (`s ≠ 1` iff `p ≠ q`; `z² + 1 > 0`), `K = k² ∉ {0, −1}`, and `K ≠ 1` because `Q₊(S,1) = 64(S−1)⁶(S+1)² ≠ 0`, `Q₋(S,1) = 16(S−1)⁴q₄(S) ≠ 0` (`q₄` has no positive rational root: `√5`).
6. **Quotient** (`Reciprocal`, `QuotientTransport`): `(U,V)` (swapped for `ε = −`) satisfies `C8(U,V) = 0`, `256Q_ε = ±(S+1)⁸(K∓1)⁶(K±1)⁴ C8`.
7. **Characters** (`Characters`, `CompactBoundary`): `UV = ((z²−1)/(z²+1))²` is a square, `≠ 1`; `1 − UV = (2z/(z²+1))²` is a nonzero square.
8. **Inverse transport** (`QuotientInverse`, `TransportExceptions`, `TransportCertificateData`, `TransportExceptionData`): `x = −B/A`, `y = −b₁/a₁` give `P ∈ E1(ℚ)` with `U(P) = U`, `V(P) = V`, `f₃(P) ≠ 0`. Exceptional fibres closed on the admissible locus `{C8 = 0, UV square, UV ≠ 1}`:
   * `A = 0` ⇒ `U ∈ {1, −1, 1/2}` or root of `D₁,D₂,D₈` — each excluded (§15(i)).
   * `a₁ = 0` ⇒ `a₂ = 0` (then `x = 2` or `x = 352225/576` or root of `S₁₉`) or `b₁ = 0` (then `x = 2`, `x = 352225/576`, `x² = 5`, or root of a cubic) — each excluded (§15(ii)).
   * `f₃(x,y) = 0` on `E1` ⇒ `x = 352225/576` (`x² = 5`, `x² − x − 1 = 0` impossible) ⇒ `352225A + 576B = 0` ⇒ `U ∈ {1, −1, 1/2, U₊, U_lim}` or root of `D₁,D₂,D₈` — each excluded (§15(iii)).
9. **Fibre `X = 1`** (`GaussianCompletion.quotient_inverse_point_X_ne_one`): `(1,0)` has `UV = 1`.
10. **Translation** (`TransportCompletion`): `P' = τ(P)`; `D₀(P') ≠ 0`; `U(P) = e1U(P')`, `V(P) = e1V(P')`. Fibres `P'.X = 0` (i.e. `P ∈ {(3,±4)}`) and `P'.X = 3` (`P ∈ {(0,±2)}`) excluded: `UV = 1` at `(3,4)`, `(0,2)`; `UV` non-square at `(3,−4)`, `(0,−2)`. `L(P') ≠ 0`, `g(P') ≠ 0` from `1 − UV ≠ 0`.
11. **Common character** (`CharacterDescent`, `Characters`): `1 − UV = 2(X+1)LM g² = 2kh·(Lg)²` with `k = (Y+2)/X`, `h = X+1`; hence `z'² = 2kh`, `k,h ≠ 0`, and `h² − (k²+2)h + k² + 4k − 4 = 0`.
12. **Valuation descent** (`ValuationDescent`, `SquareclassDescent`): `k = 2εu²`, `h = εv²`. `ε = −` impossible (mod 8/16/64). `ε = +`: `r := v² − 2u⁴ − 1` satisfies `r² = 4u⁸ − 8u² + 5` — **a rational point `(u, r)` on the octic with `k = 2u²`**.
13. **Octic classification** (`GlobalBridge`, `Completion`): `OcticRationalPointsClassified ⇒ u = ±1 ⇒ k = 2 ⇒ h ∈ {2,4} ⇒ X ∈ {1, 3}`; `X = 3` excluded in step 10; `X = 1 ⇒ Y = 0 ⇒ D₀ = 0`, contradiction. So the octic point produced in step 12 necessarily has `u ≠ ±1`, contradicting the classification.
14. **Discharge** (`GaussianClassification`, `GaussianSession1Completion`): `OcticRationalPointsClassified` follows from `GaussianCoverZeroClassified` and `GaussianCoverOneEllipticClassified`, both proved unconditionally in the Gaussian back end.

## (c) Nature of each fact

**`native_decide` certificates (executable checks on integer term lists):**
`QuotientInverse`: `quotientInverseR5CertificateTerms_explicit`, `E6CertificateTerms_explicit`, `quotientInverseR5_x_degree`, `E6_x_degree`, `quotientInverseR5_sparse_back`, `E6_sparse_back` (substitution `x = −B/A` normal form = stored Back list), `reciprocalQuotientC8CertificateTerms_explicit`, `quotientInverseR5_sparse_division`, `E6_sparse_division` (`Back = Quot · C8` as sparse products).
`TransportExceptions`: `exceptionMod13_nonzero`, `exceptionMod2_nonzero`, `exceptionF3YCoefficientMod41_nonzero`, `exceptionSimultaneous19Mod31_nonzero` (no projective zeros over `𝔽_p`); `exceptionC8Terms_explicit`; `exceptionAFactorTerms_product`, `exceptionRemovedFactorTerms_product` (stored factor list = product of small factors); `exceptionA_sparse_bezout`, `exceptionRemoved_sparse_bezout` (the two Bézout identities); `exceptionRemovedLinearTerms_construct` (`= 352225A + 576B`).
The bridge from lists to ℚ-identities is the soundness lemmas of `TransportPolynomial`.

**Kernel `decide` (finite enumeration in `ZMod n`):** `SquareclassDescent` (`ZMod 8`, `ZMod 16`, `ZMod 64` values of `negAux` by parity class, and non-square residues); `ValuationDescent` (`hk_discriminant_odd_odd_not_square` in `ZMod 8`, `hk_discriminant_four_odd_not_square` in `ZMod 32`).

**`norm_num` numerics:** non-squareness of specific rationals (`Rat.isSquare_iff`): `5`, `8`, `−3`, `1/2`, `U₊V₊`, `U_lim V_lim`, `U·V` at `(3,−4)`, `(0,−2)`; `D₀(1,0) = 0`; the product values at `(3,4)`, `(0,2)`, `(1,0)` equal `1`.

**`ring`/`field_simp` polynomial identities (kernel-checked normalization):** everything in `SignedSquare`, `CompactModel`, both `ProjectionCertificate` files, `ExceptionalFibers`, `Reciprocal`, `Characters`, the `Q_ε ↔ C8` clearing identities and the forward-map pair certificate in `QuotientTransport` (the latter as a `norm_num`+`ring` identity in the quadratic algebra), all identities in `CharacterDescent`, the `R5`/`E6` factor identities and resultant-type identities in `QuotientInverse`/`TransportExceptions`, the completing-the-square identities in `SquareclassDescent`/`ValuationDescent`, `DPlus/Basic`.

**Mathlib theorems used substantively:** polynomial division uniqueness (`div_modByMonic_unique`, `mul_divByMonic_cancel_left`, `isMonicOfDegree_two_iff`); `scaleRoots`, `Polynomial.isIntegral_coeff_of_dvd`, `IsIntegrallyClosed.isIntegral_iff` (ℤ), `Monic.dvd_of_fraction_map_dvd_fraction_map`, `Monic.of_mul_monic_left`, `natDegree_mul`; `padicValInt`/`padicValNat`/`padicValRat` API (`padicValInt_dvd_iff`, `padicValRat.add_eq_of_lt`, `padicValRat.min_le_padicValRat_add`, `padicValRat.lt_add_of_lt`, `dvd_iff_padicValNat_ne_zero`, `Nat.pow_dvd_iff_le_padicValNat`); `Nat.factorization` (`prod_factorization_pow_eq_self`, `factorization_mul`, `factorization_div`, `factorization_def`); `Rat.num_div_den`, `Rat.reduced`, `Rat.isSquare_intCast_iff`, `Rat.isSquare_iff`; `CharP.intCast_eq_zero_iff` for `ZMod p`; `Int.even_or_odd`, `odd_iff_exists_bit1`; `Nat.Prime.dvd_mul`, `dvd_of_dvd_pow`, `Nat.Coprime`. Lean `omega` closes all the integer/valuation arithmetic (notably the tropical classification).

## (d) Interfaces and how they are discharged

| Interface (`def … : Prop`) | Where used | Discharged by |
|---|---|---|
| `QuadraticFactorConstantsSignedSquare s` (C012) | `Extraction.quadraticCubicCase_to_compact` | `C012.quadraticFactorConstantsSignedSquare_sharipov` (unconditional for coprime `p,q ≥ 1`) |
| `HomogeneousQuadraticConstantsLocallyEven p q` | `C012.quadraticFactorConstantsSignedSquare_of_locallyEven` | `C012.homogeneousQuadraticConstantsLocallyEven` (Newton polygon) |
| `DPlusSquareAbscissaClassified` | `Completion.regular_e1_common_character_impossible`, `TransportCompletion.regular_quotient_common_character_impossible` | `GlobalBridge.dplus_classified_of_octic_classified` from `OcticRationalPointsClassified` (equivalence `dplus_classified_iff_octic_classified`) |
| `OcticRationalPointsClassified` | `GaussianCompletion.quadratic_cubic_impossible_sharipov_of_octic_classified` | `GaussianClassification.octic_classified_of_gaussian_covers` + `GaussianSession1Completion.octicRationalPointsClassified` |
| `GaussianCoverZeroClassified` (`C₀ → E₀` lands in `{±P₀}`) | `GaussianClassification` | `GaussianSession1Completion.gaussianCoverZeroClassified` (rank-one argument in the Gaussian back end, outside scope) |
| `GaussianCoverOneEllipticClassified` (`C₁ → E₁` lands in `{O, T}`) | `GaussianClassification` | `GaussianActualTorsion.gaussianCoverOneEllipticClassified` (rank zero, torsion `{O,T}`; outside scope) |

The hypotheses `hA`, `ha1`, `hF3` of `reciprocalQuotientC8_to_E1_regular` are internal interfaces of the inverse transport, discharged by `reciprocalQuotientC8_admissible_denominators` on the admissible locus. The compact-chart hypotheses `z ≠ 0`, `k ≠ 0`, `z² ≠ 1` come from `s > 0`, `b ≠ 0`, `s ≠ 1`.

The final theorem in scope is
`quadratic_cubic_impossible_sharipov_of_octic_classified : OcticRationalPointsClassified → ∀ p q, 0 < p → 0 < q → Coprime p q → p ≠ q → ¬QuadraticCubicCase (sharipovParameter p q)`,
made unconditional in `GaussianSession1Completion.quadratic_cubic_impossible_sharipov` and consumed by `Main.quadratic_cubic_impossible`.
