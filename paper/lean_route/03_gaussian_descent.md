# The Gaussian route for `r² = 4u⁸ − 8u² + 5`: global part

Source: `lean/Cuboid2/QuadraticReduction/Gaussian*.lean` (repository `cuboid-2`).
Every statement below is quoted with the Lean theorem name that proves it, in the
form `File.lean : theorem_name`. Notation: `K = ℚ(i)`, `𝒪 = ℤ[i]`,
`λ = 1+i`, `π = 1+2i`, `ρ = 1+4i`, `Kˣ/Kˣ²` the squareclass group.

The Lean model of `K` is `GaussianRat := QuadraticAlgebra ℚ (-1) 0` (basis `1, i`,
`gaussianI = i`); `𝒪` is Mathlib's `GaussianInt = Zsqrtd (-1)`.

---

## 0. The octic curve and the target

`DPlus/Basic.lean`: `octicRhs u = 4u⁸ − 8u² + 5`; an `OcticPoint` is a pair
`(u, r) ∈ ℚ²` with `r² = 4u⁸ − 8u² + 5`.

The global Gaussian route proves two elliptic-curve statements over `K`:

* `E₀(K) ≅ ℤ × ℤ/2` (`GaussianActualTorsion.lean : gaussianE0_equiv`), and
* every point of `E₁(K)` is `O` or `(0,0)`
  (`GaussianActualTorsion.lean : gaussianE1_point_classified`), packaged as
  `GaussianActualTorsion.lean : gaussianCoverOneEllipticClassified`.

These feed the (non-global) elliptic-Chabauty completion in
`GaussianSession1Completion.lean : octicRationalPointsClassified`.

---

## 1. Norm factorization over `ℚ(i)` — `GaussianCover.lean`

Define the Gaussian quartic
```
q(u) := (2u⁴ − 1) + i·(2u² − 2) ∈ K            (gaussianQuartic)
```
Then, with `N(a+bi) = a² + b²` (`gaussianNorm`),
```
N(q(u)) = (2u⁴ − 1)² + (2u² − 2)² = 4u⁸ − 8u² + 5      (gaussianQuartic_norm)
q(u) · q̄(u) = 4u⁸ − 8u² + 5                            (gaussianQuartic_mul_conj)
```
(`q̄` = complex conjugate, `gaussianConj`). So the octic is `r² = q(u)·q̄(u)`.

## 2. The two quartic covers over `ℚ(i)` — `GaussianCover.lean`, `GaussianSplit.lean`

Two curves (as Lean structures with a rational `u` and a Gaussian second coordinate):
```
C₀ : v² = q(u)          v ∈ K, u ∈ ℚ      (GaussianCoverZeroPoint)
C₁ : w² = −i·q(u)       w ∈ K, u ∈ ℚ      (GaussianCoverOnePoint)
```
**Pythagorean split** (`GaussianSplit.lean : octic_to_gaussian_cover`):
every rational point `(u, r)` of the octic lifts to a point of `C₀` (if the reduced
denominator of `u` is odd) or of `C₁` (if it is even), with the same `u`.

Proof, entirely elementary. Write `u = m/n` in lowest terms, `n > 0`, and put
```
A = 2m⁴ − n⁴,   B = 2n²(m² − n²)        (gaussianSplitA, gaussianSplitB)
```
Then `n⁸(4u⁸ − 8u² + 5) = A² + B²`, so `R := r·n⁴` is an integer (a rational whose
square is an integer is an integer, `rat_isInt_of_sq_eq_int`) and `(A, B, R)` is a
Pythagorean triple (`octic_denominator_pythagorean`).

* `n` odd: `gcd(A,B) = 1` (`gaussianSplit_coprime_of_odd`), `A` is odd, so by the
  classification of primitive triples (Mathlib `PythagoreanTriple.coprime_classification`)
  `A = c² − d²`, `B = 2cd` for integers `c, d` (`octic_odd_square_split`; the other
  orientation `A = 2cd` is excluded by parity). Hence `q(u) = (A + iB)/n⁴ = ((c+di)/n²)²`,
  i.e. `v = (c + di)/n²` gives a point of `C₀`.
* `n = 2N` even: then `m` is odd, `A = 2A'`, `B = 2B'` with
  `A' = m⁴ − 8N⁴`, `B' = (2N)²(m² − (2N)²)` (`gaussianSplitEvenA/B`), `R = 2R'`,
  `gcd(A',B') = 1` (`gaussianSplitEven_coprime`), `A'` odd, so `A' = c² − d²`,
  `B' = 2cd` (`octic_even_square_split`). Then `A + iB = 2(c+di)²` and, since
  `(1−i)² = −2i`, `−i·q(u) = ((1−i)(c+di)/n²)²`; explicitly
  `w = ((c+d) + (d−c)i)/n²` gives a point of `C₁`.

## 3. The elliptic quotients — `GaussianCover.lean`

```
E₀ : Y² = X³ + 2i·X² − (2+4i)·X          (gaussianE0;  a₂ = 2i,  a₄ = −2−4i)
E₁ : Y² = X³ + 2·X²  + (2+4i)·X          (gaussianE1;  a₂ = 2,   a₄ = 2+4i)
```
Coefficients verified from the source: `gaussianE0 = {a₁=0, a₂=2i, a₃=0, a₄=−2−4i, a₆=0}`,
`gaussianE1 = {a₁=0, a₂=2, a₃=0, a₄=2+4i, a₆=0}`.

Discriminants (`native_decide` on the exact `QuadraticAlgebra` values):
```
Δ(E₀) = −4864 − 2048i,   Δ(E₁) = 4864 + 2048i      (gaussianE0/E1_discriminant_ne_zero)
```
(consistent with the general formula `Δ = 16B²(A² − 4B)`, §4).

Maps to the elliptic curves:
```
C₀ → E₀ :  (u, v) ↦ (X, Y) = (2u², 2uv)              (GaussianCoverZeroPoint.toE0)
C₁ → E₁ :  (u, w) ↦ (X, Y) = (−2i·u², −2i·u·w)       (GaussianCoverOnePoint.toE1)
```
Check: `Y² = 4u²·q(u) = 4u²(2u⁴ − 1 + i(2u² − 2))` equals `X³ + 2iX² − (2+4i)X` at
`X = 2u²`; and `Y² = −4u²w² = 4i·u²·q(u)` equals `X³ + 2X² + (2+4i)X` at `X = −2iu²`.
Both images are affine points (never `O`).

Visible points:
```
P = (2, 2) ∈ E₀(K)      (gaussianE0P)   — image of (u, v) = (1, 1) ∈ C₀
T = (0, 0) ∈ E₀(K)      (gaussianE0T)
T = (0, 0) ∈ E₁(K)      (gaussianE1T)
```

---

## 4. The generic 2-isogeny — `GaussianDescent.lean`

For `A, B ∈ K` with `B ≠ 0`, `A² − 4B ≠ 0`:
```
E(A,B)  : y² = x(x² + Ax + B)                          (curve)
E'(A,B) : Y² = X(X² − 2A·X + (A² − 4B)) = E(−2A, A² − 4B)   (dualCurve)
Δ(E)  = 16 B² (A² − 4B)                                (curve_discriminant)
Δ(E') = 256 B (A² − 4B)²                               (dualCurve_discriminant)
```
Rational 2-torsion points `T = (0,0) ∈ E`, `T' = (0,0) ∈ E'` (`torsion`, `dualTorsion`).

The two degree-2 maps are **total** functions on Mathlib's affine point type:
```
φ : E → E',  O ↦ O,  (0,0) ↦ O,  (x,y) ↦ ( y²/x² ,  y(B − x²)/x² )               (phi)
φ̂ : E' → E, O ↦ O,  (0,0) ↦ O,  (X,Y) ↦ ( Y²/(4X²) ,  Y((A² − 4B) − X²)/(8X²) )  (phiHat)
```
Properties (all proved on the actual group law, all exceptional branches included):
```
φ̂ ∘ φ = [2] on E(K)         (phiHat_phi)
φ ∘ φ̂ = [2] on E'(K)        (phi_phiHat)
φ(P) = O ⇔ P ∈ {O, T}       (phi_eq_zero_iff)
φ̂(Q) = O ⇔ Q ∈ {O, T'}      (phiHat_eq_zero_iff)
φ(−P) = −φ(P)               (phi_neg)
φ(T + P) = φ(P)             (phi_torsion_add)
φ̂(T' + Q) = φ̂(Q)            (GaussianDualTranslation.lean : phiHat_dualTorsion_add)
```
(`φ`, `φ̂` are not packaged as `AddMonoidHom`s; only the identities above are used.)

## 5. Kummer (squareclass) maps — `GaussianDescent.lean`

`SquareClass := Kˣ / (Kˣ)²` (Mathlib quotient of `GaussianRatˣ` by the range of squaring);
`squareClassOf x` for `x ≠ 0`. Facts: `[x] = 1 ⇔ x` is a square (`squareClassOf_eq_one_iff`),
`[x] = [y] ⇔ x = y z²` for some `z ≠ 0` (`squareClassOf_eq_iff`), every class has order ≤ 2
(`squareClass_mul_self`).

```
α  : E(K)  → Kˣ/Kˣ²,  O ↦ 1,  (0,0) ↦ [B],         (x,y) ↦ [x]       (alpha)
α' : E'(K) → Kˣ/Kˣ²,  O ↦ 1,  (0,0) ↦ [A² − 4B],   (X,Y) ↦ [X]       (alphaDual)
```
* `α` and `α'` are group homomorphisms (`alpha_add`, `alphaDual_add`; packaged as
  `alphaHom`, `alphaDualHom` into `Additive SquareClass`). The proof of `alpha_add` uses the
  identity `x₁x₂x₃ = (y₁ − ℓx₁)²` for the three abscissae of collinear points (`curve_addX_product`).
* Exactness (constructive, both directions):
  ```
  α(P) = 1  ⇔  P ∈ φ̂(E'(K))        (alpha_eq_one_iff_phiHat_image)
  α'(Q) = 1 ⇔  Q ∈ φ(E(K))          (alphaDual_eq_one_iff_phi_image)
  ```
  Explicit preimages: if `x = z²` with `(x,y) ∈ E`, put `X = A + 2x − 2y/z`, `Y = 2zX`;
  then `(X,Y) ∈ E'` and `φ̂(X,Y) = (x,y)`. If `B = s²`, `(A + 2s, 0) ∈ E'` maps to `(0,0)`.
  Dually: if `X = z²`, `x = (X − A − Y/z)/2`, `y = z x`; if `A² − 4B = s²`, `x = (s − A)/2`, `y = 0`.

## 6. Specialization — `GaussianDescent.lean`, `GaussianPrimes.lean`

```
E₀ = E(A₀,B₀),  A₀ = 2i,  B₀ = −2 − 4i          (E0A, E0B, gaussianE0_eq_curve)
E₁ = E(A₁,B₁),  A₁ = 2,   B₁ = 2 + 4i           (E1A, E1B, gaussianE1_eq_curve)
E₀' : Y² = X³ − 4i·X² + (4 + 16i)·X             (gaussianE0Dual)   A₀² − 4B₀ = 4 + 16i
E₁' : Y² = X³ − 4·X²  − (4 + 16i)·X             (gaussianE1Dual)   A₁² − 4B₁ = −4 − 16i
```
The specialized maps: `gaussianE0Phi`, `gaussianE0PhiHat`, `gaussianE1Phi`, `gaussianE1PhiHat`.

**Gaussian primes** (`GaussianPrimes.lean`):
```
λ = 1 + i   N = 2    (gaussianLambdaInt, gaussianLambdaInt_prime)  — ramified above 2
π = 1 + 2i  N = 5    (gaussianPiInt,     gaussianPiInt_prime)      — above 5
ρ = 1 + 4i  N = 17   (gaussianRhoInt,    gaussianRhoInt_prime)     — above 17
```
Primality via "prime norm ⇒ prime" (`prime_of_normNatAbs_prime`); pairwise non-associate by norms
(`lambda_not_associated_pi`, `lambda_not_associated_rho`, `pi_not_associated_rho`).

**Factorizations of the four `B`'s** (`decide` in `𝒪`):
```
B₀        = −2 − 4i  =  i · λ² · π          (e0BInt_factorization)
B₁        =  2 + 4i  = −i · λ² · π          (e1BInt_factorization)
A₀² − 4B₀ =  4 + 16i = −λ⁴ · ρ              (e0DualBInt_factorization)
A₁² − 4B₁ = −4 − 16i =  λ⁴ · ρ              (e1DualBInt_factorization)
```
**Units mod squares**: `𝒪ˣ = {±1, ±i}`; since `−1 = i²`, every unit is `z²` or `i·z²`
(`unit_eq_square_or_i_mul_square`). So the unit part of a squareclass is `1` or `i`.

Visible classes (`GaussianDescent.lean`):
```
α(P)  = [2]        = [i]      since 2 = i(1−i)²          (alpha_gaussianE0P)
α(T)  = [B₀]       = [iπ]     since B₀ = iπ·(1+i)²       (alpha_gaussianE0T)
α(P+T)= [i]·[iπ]   = [π]                                  (alpha_gaussianE0P_add_T)
α(T)  = [B₁]       = [iπ]  on E₁, since B₁ = iπ·(1−i)²   (alpha_gaussianE1T)
α'(T')= [4+16i]    = [ρ]   on E₀', since 4+16i = ρ·2²    (alphaDual_gaussianE0T)
α'(T')= [−4−16i]   = [ρ]   on E₁', since −4−16i = ρ·(2i)² (alphaDual_gaussianE1T)
```
Nontriviality/distinctness of `1, [i], [π], [iπ], [ρ], [iρ]` is proved via norms
(`N(π)=5`, `N(ρ)=17` are not rational squares; `i` is not a square in `K` by an explicit
`a²−b² = 0, 2ab = 1` argument): `classI_ne_one`, `classPi_ne_one`, …, `classRho_ne_classIRho`.

## 7. Global support: the raw eight-class lists — `GaussianFraction/Support/UFD/Range.lean`

* `GaussianFraction.lean`: `K` is the fraction field of `𝒪` (`gaussianRatIsFractionRing`), with
  reduced numerator/denominator `IsFractionRing.num/den`.
* `GaussianSupport.lean`: for each prime `p ∈ 𝒪` the additive valuation `v_p` on `K`
  (`gaussianPrimeOrder`, built from Mathlib `multiplicity` and `extendToLocalization`).
  **Even-valuation lemma** (`curve_abscissa_order_even`): if `y² = x(x² + Ax + B)`, `x ≠ 0`,
  `v(A) ≥ 0`, `v(B) = 0`, then `v(x)` is even. (If `v(x) < 0`: `v(x²+Ax+B) = 2v(x)`, so
  `2v(y) = 3v(x)`; if `v(x) > 0`: `v(x²+Ax+B) = 0`, so `2v(y) = v(x)`.) Consequently
  `mult_p(num(x)·den(x))` is even for every prime `p ∤ B` (`curve_abscissa_num_mul_den_even`).
* `GaussianUFD.lean : exists_unit_mul_square_of_even_multiplicity_off_two_primes`: if `r ∈ 𝒪∖0`
  has even multiplicity at every prime not associated to `L` or `P`, then
  `r·L^{e_L}·P^{e_P} = u·s²` with `e_L, e_P ∈ {0,1}`, `u ∈ 𝒪ˣ`.
* `GaussianRange.lean : curve_abscissa_squareClass_supported_on_two_primes`: for a point with
  `x ≠ 0` on `y² = x(x²+Ax+B)`, `A, B ∈ 𝒪`, all prime divisors of `B` among `{L, P}`:
  `[x] = [g·L^{e_L}·P^{e_P}]` with `g ∈ {1, i}`, `e_L, e_P ∈ {0,1}`.

**Raw candidate lists** (8 classes each):
```
E₀, E₁  (B supported on λ, π):  [x] ∈ {1, i, λ, iλ, π, iπ, λπ, iλπ}   (curve_abscissa_pi_raw_cases)
E₀', E₁'(B supported on λ, ρ):  [x] ∈ {1, i, λ, iλ, ρ, iρ, λρ, iλρ}   (curve_abscissa_rho_raw_cases)
```
(named `classLambda, classILambda, classLambdaPi, classILambdaPi, classLambdaRho, classILambdaRho`
in `GaussianRange`, `classI, classPi, classIPi, classRho, classIRho` in `GaussianDescent`).
Note: the descent is over the PID `ℤ[i]`; no class-group term appears.

## 8. The λ-local obstruction: homogeneous spaces and finite certificates

### 8a. Bridge — `GaussianObstructionBridge.lean`
If `α(x,y) = [d]` on `y² = x(x² + Ax + B)` with `A, B, d ∈ 𝒪`, `B = d·e`, then writing
`x = d z²`, `z = U/V` with `U, V ∈ 𝒪` coprime (`IsFractionRing.num_den_reduced`), and
`W := (y/(dz))·V²`, one gets the **homogeneous space**
```
W² = d·U⁴ + A·U²V² + e·V⁴,   U, V ∈ 𝒪 coprime,   W ∈ 𝒪
```
(`fieldHomogeneousSpace_of_squareClass` gives `N² = d z⁴ + A z² + B/d` with `N = y/(dz)`;
`integralHomogeneousSpace_of_squareClass` clears denominators and uses integral closedness of `𝒪`
(`IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow`) to make `W` integral.)

**λ-primitivity**: `λ ∣ z ⇔ z.re + z.im` is even (`gaussianLambdaInt_dvd_iff_even`); coprime
`U, V` are not both divisible by `λ` (`not_both_gaussianLambdaInt_dvd_of_isRelPrime`).

Reduction mod an even `n` (`gaussianResidue n : 𝒪 → (ℤ/n)[i]`, as pairs of canonical residues)
is a ring map (`gaussianResidue_add/mul/sq/fourth`), preserves λ-primitivity
(`lambdaPrimitive_gaussianResidue`), and hence any integral coprime solution reduces to a solution
found by the exhaustive checker (`hasPrimitiveHomogeneousSpaceSolution_of_integral`). Therefore:

`squareClass_ne_of_localObstruction`: if the finite checker returns `false` for `(n, A, d, e)`,
then no affine point with `x ≠ 0` has `α = [d]`.

### 8b. The finite checker — `GaussianFinite.lean`
```
hasPrimitiveHomogeneousSpaceSolution n A d e :=
  ∃ U, V ∈ (ℤ/n)[i] (all n² × n² pairs), not both with even (re+im),
     such that d U⁴ + A U²V² + e V⁴ ∈ { z² : z ∈ (ℤ/n)[i] }   (mod n)
```
Since `n` is a power of 2 and `2 = −i λ²`, "mod 4" = "mod λ⁴", "mod 8" = "mod λ⁶",
"mod 16" = "mod λ⁸", "mod 32" = "mod λ¹⁰": all obstructions are **λ-adic (2-adic)**.

### 8c. The 22 obstruction rows (`GaussianExactRanges.lean` ↔ `GaussianFinite.lean`)
Each row: curve, excluded class `d`, exact `e = B/d ∈ 𝒪`, modulus `n`, and the residue
triple `(A mod n, d mod n, e mod n)` fed to `native_decide`.

| curve | `A` | `B` | `d` | `e = B/d` | `n` | residues `(A, d, e)` | Lean certificate |
|---|---|---|---|---|---|---|---|
| E₀ | 2i | −2−4i | λ = 1+i | −3−i | 4 | (0,2),(1,1),(1,3) | `e0_lambda_local_obstruction` |
| E₀ | | | iλ = −1+i | −1+3i | 4 | (0,2),(3,1),(3,3) | `e0_iLambda_local_obstruction` |
| E₀ | | | λπ = −1+3i | −1+i | 4 | (0,2),(3,3),(3,1) | `e0_lambdaPi_local_obstruction` |
| E₀ | | | iλπ = −3−i | 1+i | 4 | (0,2),(1,3),(1,1) | `e0_iLambdaPi_local_obstruction` |
| E₀' | −4i | 4+16i | λ | 10+6i | 4 | (0,0),(1,1),(2,2) | `e0Dual_lambda_local_obstruction` |
| E₀' | | | iλ | 6−10i | 4 | (0,0),(3,1),(2,2) | `e0Dual_iLambda_local_obstruction` |
| E₀' | | | λρ = −3+5i | 2−2i | 4 | (0,0),(1,1),(2,2) | `e0Dual_lambdaRho_local_obstruction` |
| E₀' | | | iλρ = −5−3i | −2−2i | 4 | (0,0),(3,1),(2,2) | `e0Dual_iLambdaRho_local_obstruction` |
| E₀' | | | i | 16−4i | 16 | (0,12),(0,1),(0,12) | `e0Dual_i_local_obstruction` |
| E₀' | | | iρ = −4+i | −4i | 16 | (0,12),(12,1),(0,12) | `e0Dual_iRho_local_obstruction` |
| E₁ | 2 | 2+4i | λ | 3+i | 4 | (2,0),(1,1),(3,1) | `e1_lambda_local_obstruction` |
| E₁ | | | iλ | 1−3i | 4 | (2,0),(3,1),(1,1) | `e1_iLambda_local_obstruction` |
| E₁ | | | λπ | 1−i | 4 | (2,0),(3,3),(1,3) | `e1_lambdaPi_local_obstruction` |
| E₁ | | | iλπ | −1−i | 4 | (2,0),(1,3),(3,3) | `e1_iLambdaPi_local_obstruction` |
| E₁ | | | i | 4−2i | 8 | (2,0),(0,1),(4,6) | `e1_i_local_obstruction` |
| E₁ | | | π = 1+2i | 2 | 4 | (2,0),(1,2),(2,0) | `e1_pi_local_obstruction` |
| E₁' | −4 | −4−16i | λ | −10−6i | 4 | (0,0),(1,1),(2,2) | `e1Dual_lambda_local_obstruction` |
| E₁' | | | iλ | −6+10i | 4 | (0,0),(3,1),(2,2) | `e1Dual_iLambda_local_obstruction` |
| E₁' | | | λρ | −2+2i | 4 | (0,0),(1,1),(2,2) | `e1Dual_lambdaRho_local_obstruction` |
| E₁' | | | iλρ | 2+2i | 4 | (0,0),(3,1),(2,2) | `e1Dual_iLambdaRho_local_obstruction` |
| E₁' | | | i | −16+4i | 32 | (28,0),(0,1),(16,4) | `e1Dual_i_local_obstruction` |
| E₁' | | | iρ | 4i | 32 | (28,0),(28,1),(0,4) | `e1Dual_iRho_local_obstruction` |

(The four E₀'/E₁' rows with `A ≡ 0 mod 4` and `e ≡ 2+2i` are literally the same finite computation;
the sixteen `λ`-rows at modulus 4 say: no λ-primitive `U,V` makes `dU⁴ + AU²V² + eV⁴` a square in
`(ℤ/4)[i]` when `v_λ(d)` is odd.) The `E₀` classes `1, i, π, iπ` and the `E₁`/dual classes
`1, iπ` / `1, ρ` are **not** obstructed — and are realized by the visible points.

## 9. Exact ranges — `GaussianExactRanges.lean`

Pointwise (`gaussianE0_alpha_classified` etc.) and as sets:
```
α(E₀(K))   = {1, [i], [π], [iπ]}   realized by O, P, P+T, T    (gaussianE0_alpha_range,     |·| = 4)
α'(E₀'(K)) = {1, [ρ]}               realized by O, T'           (gaussianE0_alphaDual_range, |·| = 2)
α(E₁(K))   = {1, [iπ]}              realized by O, T            (gaussianE1_alpha_range,     |·| = 2)
α'(E₁'(K)) = {1, [ρ]}               realized by O, T'           (gaussianE1_alphaDual_range, |·| = 2)
```
Cardinalities: `gaussianE0_alphaHom_range_card = 4`, `gaussianE0_alphaDualHom_range_card = 2`,
`gaussianE1_alphaHom_range_card = 2`, `gaussianE1_alphaDualHom_range_card = 2`; the ranges are
`Finite` (instances `gaussianE*_alpha(Dual)Hom_range_finite`).
Since every surviving class is hit by a rational point, the images of `α, α'` are computed exactly
(the φ-Selmer group equals the image; no Sha[φ] enters).

## 10. Weak Mordell–Weil and finite generation

### 10a. `ker α = 2E(K)` — `GaussianWeakMW.lean`
`alpha_eq_one_iff_two_smul_of_dual_classification`: if `α'(Q) ∈ {1, α'(T')}` for all `Q ∈ E'(K)`
then `α(P) = 1 ⇔ P ∈ 2E(K)`. Proof: `α(P) = 1 ⇒ P = φ̂(Q)`; if `α'(Q) = 1` then `Q = φ(U)`,
`P = φ̂φ(U) = 2U`; otherwise `α'(Q − T') = 1`, `Q − T' = φ(U)`, and
`P = φ̂(T' + (Q − T')) = φ̂(Q − T') = 2U` by `phiHat_dualTorsion_add`. Converse:
`α(2U) = α(φ̂(φ(U))) = 1`. Hence
```
2E(K) = ker(α : E(K) → Kˣ/Kˣ²)     (gaussianE0/E1_two_range_eq_alpha_ker in GaussianMordellWeil.lean)
[E(K) : 2E(K)] = |α(E(K))|        (AddSubgroup.index_ker)
```
In particular `[E(K):2E(K)]` is finite (`finiteIndex_two_of_finite_alpha_and_dual_classification`).

### 10b. Heights — `GaussianHeight.lean`
Naive height `h(P) := logHeight(P.xRep)`, where `xRep(x,y) = [x : 1]`, `xRep(O) = [1 : 0]`
(`naiveHeight`; `h(O) = 0`, `h(x,y) = logHeight₁(x)`, `h ≥ 0`).
* Geometric identity (`addSubMap_sym2x_projective`): Mathlib's quadratic-form map
  `W.addSubMap : ℙ² → ℙ²` sends the symmetric pair `sym2x(P,Q)` to `sym2x(P+Q, P−Q)`, in all
  cases (infinity, vertical, tangent, generic; the generic scaling factor is `(x₁ − x₂)²`).
* Parallelogram law up to a constant (`exists_naiveHeight_parallelogram`):
  `|h(P+Q) + h(P−Q) − 2h(P) − 2h(Q)| ≤ C`, from Mathlib's
  `W.abs_logHeight_addSubMap_sub_two_mul_logHeight_le` and `Height.abs_logHeight_sym2_sub_le`.
* Northcott (`instNorthcottNaiveHeight`): `{P : h(P) ≤ B}` finite, from
  `NumberField.finite_setOfPred_logHeight₁_le` plus "an `x` has at most the two preimages `±P`".
* **Mathlib descent theorem used**: `AddCommGroup.fg_of_descent'` (Mathlib
  `GroupTheory/Descent`), applied in `fg_of_finiteIndex_two`: finite index of `2E(K)` + height
  with the two properties ⇒ `E(K)` finitely generated.

### 10c. Conclusion — `GaussianMordellWeil.lean`
```
E₀(K), E₁(K) finitely generated       (gaussianE0_fg, gaussianE1_fg)
[E₀(K) : 2E₀(K)] = 4                  (gaussianE0_doubling_index)
[E₁(K) : 2E₁(K)] = 2                  (gaussianE1_doubling_index)
```
(`GaussianGlobal.lean` contains an alternative generic assembly — product of the two isogeny
cokernels, `finiteIndex_two_of_gaussian_descent`, `fg_of_gaussian_descent` — and generic
structure-theorem helpers; the main chain uses `GaussianWeakMW` as above.)

## 11. Ranks — `GaussianArithmetic.lean`, `GaussianRankArithmetic.lean`

Structure theorem (Mathlib `AddCommGroup.equiv_free_prod_directSum_zmod`):
`E(K) ≅ ℤⁿ × D`, `D` finite. Then (`doubling_index_free_prod_finite`,
`doubling_index_eq_pow_mul_kernel_card_of_equiv`)
```
[E(K) : 2E(K)] = 2ⁿ · |E(K)[2]|
```
With `|E(K)[2]| = 2` (§12, `doubling_ker_card_eq_two_of_classified`):
```
E₀: 4 = 2ⁿ·2 ⇒ n = 1     (rank_one_structure_of_fg;  gaussianE0_freeRank = 1)
E₁: 2 = 2ⁿ·2 ⇒ n = 0     (rank_zero_structure_of_fg; gaussianE1_freeRank = 0)
```
`gaussianE0_rankOneStructure_of_fg_and_index : E₀(K) ≅ ℤ × ⊕ ZMod(pᵢ^eᵢ)`,
`gaussianE1_rankZeroStructure_of_fg_and_index : E₁(K) ≅ ⊕ ZMod(pᵢ^eᵢ)` (finite summand not yet
identified; odd torsion is excluded separately, §13–14).

**The "correction factor"** (`GaussianArithmetic.lean : dualKernel_card_mul_doubling_index`):
for any pair `φ, φ̂` with `ker α = im φ̂`, `ker α' = im φ`, `φ̂φ = [2]`,
```
|α'(ker φ̂)| · [E : 2E] = |im α| · |im α'|
```
where `α'(ker φ̂) = {1, α'(T')}` has order 2 here (as `α'(T') = [ρ] ≠ 1`). Numerically:
`E₀`: `2·[E₀:2E₀] = 4·2` ⇒ 4; `E₁`: `2·[E₁:2E₁] = 2·2` ⇒ 2
(`doubling_index_eq_four_of_kummer_cards`, `doubling_index_eq_two_of_kummer_cards`). The docstring
notes that the naive product `|im α|·|im α'|` would overcount by 2. **These theorems are proved but
not consumed on the main path**: `GaussianMordellWeil` obtains the indices directly from
`2E(K) = ker α` (§10a), which is the special case of the formula in which `α'(E'(K)) = α'(ker φ̂)`.

## 12. Two-torsion — `GaussianTwoTorsion.lean`

`E(K)[2] = {O, (0,0)}` for both curves (`gaussianE0_two_torsion_classified`,
`gaussianE1_two_torsion_classified`). Proof: a point with `2P = 0` has `y = 0`, so
`x(x² + Ax + B) = 0`; a root of `x² + Ax + B` gives `(2x + A)² = A² − 4B`, but
```
N(A₀² − 4B₀) = N(4 + 16i) = 272,   N(A₁² − 4B₁) = N(−4 − 16i) = 272 = 16·17,
```
not a rational square, whereas `N(z²) = N(z)²` (`no_gaussian_square_of_norm_272`,
`gaussianE0/E1_quadratic_ne_zero`). Also `2T = 0`, `T ≠ 0`
(`GaussianRankArithmetic.lean : two_nsmul_gaussianE0T, gaussianE0T_ne_zero`, same for E₁).

## 13. Three-torsion at the inert prime 11 — `GaussianThreeTorsion.lean`

For `y² = x(x² + Ax + B)` the 3-division polynomial is
```
ψ₃(x) = 3x⁴ + 4A·x³ + 6B·x² − B²          (threeDivisionValue)
```
(`b₂ = 4A, b₄ = 2B, b₆ = 0, b₈ = −B²`). If `3P = 0`, `P = (x,y) ≠ O`, then `2P = −P`, so
`x(2P) = x`, which after clearing `4y²` is `ψ₃(x) = 0`
(`threeDivision_eq_zero_of_three_nsmul_eq_zero`).
`11 ≡ 3 mod 4` is inert, so `𝒪/11 = 𝔽₁₁(i) = 𝔽₁₂₁` (`GaussianResidue11`, `residueHom`,
`residueHom_eq_zero_iff`). Exhaustive `native_decide` over all 121 residues:
`ψ₃` has no root in `𝔽₁₂₁` for `(A,B) = (2i, −2−4i)` and `(2, 2+4i)`
(`e0_threeDivision_no_root`, `e1_threeDivision_no_root`). A root `x = U/V ∈ K` in lowest terms
would reduce to a root (if `11 | V` then `3U⁴ ≡ 0` forces `11 | U`, contradiction)
(`no_threeDivision_root_of_residue`). Hence
```
3P = 0 ⇔ P = 0 on E₀(K) and E₁(K)     (gaussianE0/E1_three_nsmul_eq_zero_iff)
```

## 14. Torsion normal form and actual torsion

### 14a. `GaussianTorsionNormalForm.lean`
If every torsion point is killed by 6 (`hSix`), then torsion `⊆ {O, T}`
(`eq_zero_or_eq_twoTorsion_of_six_nsmul`: `3·(2P) = 0 ⇒ 2P = 0 ⇒ P ∈ {O,T}`), and the finite
summand of the structure theorem is `ZMod 2` (`finiteEquivZModTwo`, `rankOneEquivZModTwo`,
`rankZeroEquivZModTwo`):
```
gaussianE0_equiv_of_torsion_six : hSix → E₀(K) ≅ ℤ × ℤ/2
gaussianE1_equiv_of_torsion_six : hSix → E₁(K) ≅ ℤ/2
gaussianE1_point_classified_of_torsion_two : (torsion killed by 2) → ∀ P ∈ E₁(K), P = O ∨ P = T
```

### 14b. `GaussianActualTorsion.lean` — the six-torsion bound at the split prime 37
`37 = 1² + 6²` splits; `6² ≡ 31² ≡ −1 (mod 37)` (`GaussianP37.lean : splitRoots`). The two embeddings
`K → ℚ₃₇` (`i ↦ 6`, "plus"; `i ↦ 31`, "minus") base-change `E₀, E₁` to integral models over `ℤ₃₇`
with good reduction. Reductions mod 37 (`e0Coefficients p r = (2r, −2 − 4r)`, `e1Coefficients p r = (2, 2 + 4r)`):
```
E₀ ⊗ (i↦6)  : y² = x³ + 12x² + 11x  over 𝔽₃₇ : 48 points, exponent 12, ord(2,2) = 12   (GaussianP37 : plusGroupRow)
E₀ ⊗ (i↦31) : y² = x³ + 25x² + 22x  over 𝔽₃₇ : 42 points, cyclic (gen (5,3)), ord(2,2)=6 (GaussianP37 : minusGroupRow)
E₁ ⊗ (i↦6)  : y² = x³ + 2x²  + 26x  over 𝔽₃₇ : 28 points, killed by 28   (GaussianFiniteExponent : e1Plus_all_twentyEight)
E₁ ⊗ (i↦31) : y² = x³ + 2x²  + 15x  over 𝔽₃₇ : 34 points, killed by 34   (GaussianFiniteExponent : e1Minus_all_thirtyFour)
```
Ingredients (files outside the requested list, quoted for completeness):
* the reduction map `E(ℚ₃₇) → E(𝔽₃₇) ∪ {∞}` is a group homomorphism onto the exhaustive finite
  point list (`GaussianSplit37ReductionActual : reduceE0Plus_add`, `reduceE0Plus_mem_finitePoints`, …);
* its kernel `infinityKernel` (the formal group `Ê(37ℤ₃₇)`, parameter `t = −x/y`, `w = −1/y`,
  `w = t³ + A t² w + B t w²`) is torsion-free
  (`GaussianFormalKernelTorsion : infinityKernel_nsmul_right_injective`);
* base change `E(K) → E(ℚ₃₇)` is injective (`GaussianLocalMapInjective : mapE0PointPlusLocalHom_injective`).

Then for torsion `P ∈ E₀(K)`: `red(12P) = 12·red(P) = ∞`, so `12P ∈ Ê`, torsion, hence `12P = 0`
(`gaussianE0_torsion_twelve`); likewise `42P = 0` (`gaussianE0_torsion_fortyTwo`); `gcd = 6`
(`gaussianE0_torsion_six`). For `E₁`: `28P = 0`, `34P = 0`, so `2P = 0` (`gaussianE1_torsion_two`).

### 14c. Final group structures
```
E₀(ℚ(i)) ≅ ℤ × ℤ/2,  torsion = {O, (0,0)}        (gaussianE0_equiv)
E₁(ℚ(i)) ≅ ℤ/2 = {O, (0,0)}                       (gaussianE1_equiv_of_torsion_six + gaussianE1_point_classified)
∀ C ∈ C₁(ℚ): C.toE1 ∈ {O, (0,0)}                  (gaussianCoverOneEllipticClassified)
```
The visible point `P = (2,2)` is of infinite order (it is not `O` or `T`, and torsion is `{O,T}`);
the isomorphism `gaussianE0_equiv` does not by itself say `P` is a generator — primitivity of `P`
(index coprime to 7, etc.) is handled in the non-global files
(`GaussianIndexIndependent`, `GaussianP29PolynomialRootBridge`, `GaussianCoverZeroRowCompletion`).

---

## 15. Logical flow

### `gaussianE0_equiv : E₀(K) ≅ ℤ × ℤ/2`
```
gaussianE0_equiv  (GaussianActualTorsion)
 ├─ gaussianE0_equiv_of_torsion_six  (GaussianTorsionNormalForm)
 │   ├─ gaussianE0_rankOneStructure_of_fg_and_index  (GaussianRankArithmetic)
 │   │   ├─ gaussianE0_fg  (GaussianMordellWeil)
 │   │   │   └─ fg_of_finite_alpha_and_dual_classification  (GaussianWeakMW)
 │   │   │       ├─ Finite (alphaHom E0).range   ← gaussianE0_alphaHom_range_card = 4  (GaussianExactRanges)
 │   │   │       ├─ dual two-class: gaussianE0_alphaDual_classified + alphaDual_gaussianE0T
 │   │   │       ├─ alpha_eq_one_iff_phiHat_image, alphaDual_eq_one_iff_phi_image, phiHat_phi  (GaussianDescent)
 │   │   │       ├─ phiHat_dualTorsion_add  (GaussianDualTranslation)
 │   │   │       └─ fg_of_finiteIndex_two  (GaussianHeight)  ← Mathlib AddCommGroup.fg_of_descent'
 │   │   ├─ gaussianE0_doubling_index = 4  (GaussianMordellWeil)
 │   │   │   ← 2E = ker α  (alpha_eq_one_iff_two_smul_of_dual_classification) + index_ker + range card 4
 │   │   └─ gaussianE0_two_torsion_classified  (GaussianTwoTorsion)  → |E[2]| = 2
 │   │       └─ rank_one_structure_of_fg  (GaussianArithmetic): 4 = 2ⁿ·2 ⇒ n = 1
 │   ├─ rankOneEquivZModTwo  with  gaussianE0_torsion_classified_of_six
 │   │   ├─ gaussianE0_two_torsion_classified  (GaussianTwoTorsion, norm 272)
 │   │   └─ gaussianE0_three_nsmul_eq_zero_iff  (GaussianThreeTorsion, inert 11)
 └─ gaussianE0_torsion_six  (GaussianActualTorsion)
     ├─ gaussianE0_torsion_twelve   ← plus_all_twelve (GaussianFiniteExponent), reduceE0Plus_add, infinityKernel torsion-free, base-change injective
     └─ gaussianE0_torsion_fortyTwo ← minus_all_fortyTwo, …

ExactRanges (gaussianE0_alpha_classified, gaussianE0_alphaDual_classified)
 ├─ curve_abscissa_pi_raw_cases / curve_abscissa_rho_raw_cases  (GaussianRange)
 │   ├─ curve_abscissa_squareClass_supported_on_two_primes  (GaussianRange)
 │   │   ├─ curve_abscissa_num_mul_den_even  (GaussianSupport)
 │   │   ├─ exists_unit_mul_square_of_even_multiplicity_off_two_primes  (GaussianUFD)
 │   │   └─ unit_eq_square_or_i_mul_square, *_prime, *_factorization  (GaussianPrimes)
 │   └─ IsFractionRing GaussianInt GaussianRat  (GaussianFraction)
 └─ e0_ne_class*  ← squareClass_ne_of_localObstruction (GaussianObstructionBridge) ← native_decide rows (GaussianFinite)
```

### `gaussianCoverOneEllipticClassified`
```
gaussianCoverOneEllipticClassified  (GaussianActualTorsion)
 └─ gaussianE1_point_classified
     └─ gaussianE1_point_classified_of_torsion_two  (GaussianTorsionNormalForm)
         ├─ gaussianE1_equiv_of_torsion_six  → E₁(K) ≅ ℤ/2, so every point is torsion
         │   ├─ gaussianE1_rankZeroStructure_of_fg_and_index  ← gaussianE1_fg, gaussianE1_doubling_index = 2, E₁[2] = {O,T}
         │   └─ gaussianE1_torsion_classified_of_six  ← two-torsion (272) + three-torsion (11)
         └─ gaussianE1_torsion_two  ← e1Plus_all_twentyEight, e1Minus_all_thirtyFour (gcd(28,34) = 2)
```

---

## 16. Catalogue of `native_decide` certificates (what finite computation each is)

`GaussianCover.lean` (2): exact evaluation of `Δ(E₀) = −4864 − 2048i` and `Δ(E₁) = 4864 + 2048i`
in `QuadraticAlgebra ℚ (−1) 0`.

`GaussianFinite.lean` (28):
* 22 rows `hasPrimitiveHomogeneousSpaceSolution n A d e = false` (table in §8c). Each enumerates all
  `n⁴` pairs `(U, V) ∈ ((ℤ/n)[i])²` (`n ∈ {4, 8, 16, 32}`, i.e. 256 / 4096 / 65536 / 1048576 pairs),
  discards pairs with both `U.re+U.im` and `V.re+V.im` even, computes
  `dU⁴ + AU²V² + eV⁴ ∈ (ℤ/n)[i]`, and tests membership in the precomputed list of squares
  `{z² : z ∈ (ℤ/n)[i]}` (duplicates removed).
* `e0TorsionRows13`: `#E₀(𝔽₁₃)` for `i ↦ 5` is 12 and for `i ↦ 8` is 18 (`5² = 25 ≡ −1`).
  `e0TorsionRows29`: for `i ↦ 12`: 28 points; `i ↦ 17`: 38 points. `e1TorsionRows13`: 16 and 10.
  `e1TorsionRows29`: 32 and 22. (Point counts by brute force over all `(x,y) ∈ 𝔽_p²`, plus `∞`.
  These are consumed by `GaussianTorsionReduction.lean`, not by the 37-based main chain.)
* `indexRow29`: on `E₀ ⊗ (i↦12)` over `𝔽₂₉`: 28 points, `ord(2,2) = 14`, `7·(2,2) = (0,0)`, `14·(2,2) = ∞`.
  `indexRow157`: on `E₀ ⊗ (i↦28)` over `𝔽₁₅₇` (`28² ≡ −1`): 148 points, `ord(2,2) = 74`,
  `37·(2,2) = (92, 0)`, `74·(2,2) = ∞`. (Order via repeated addition with the explicit affine group law
  `finiteAdd`; search bound `4p + 20`. Used for the index/saturation part, not for §1–14.)

`GaussianThreeTorsion.lean` (6): `x² ≠ −1` for all `x ∈ 𝔽₁₁` (so `𝔽₁₁(i)` is a field);
`residueI² = −1` (two coordinates); `ψ₃ ≠ 0` on all 121 elements of `𝔽₁₁(i)` for `E₀` and for `E₁`;
`3 ≠ 0` and `11 = 0` in the residue field.

`GaussianFiniteExponent.lean` (4, used by `GaussianActualTorsion`): for the four `𝔽₃₇` fibres,
enumerate all points and check `12·Q = ∞` (E₀, i↦6), `42·Q = ∞` (E₀, i↦31), `28·Q = ∞` (E₁, i↦6,
28 points), `34·Q = ∞` (E₁, i↦31, 34 points), by repeated `finiteAdd`.

`GaussianP37.lean` (13): `6² ≡ 31² ≡ 36 mod 37`; plus/minus group rows (point counts 48/42,
exponents 12/42, orders of `(2,2)` and `(5,3)`); lists of multiples of `(2,2)`; paired-`x` rows;
quartic non-square disks; formal-parameter traces mod `37²` (these belong to the Chabauty part).

`decide` (not `native_decide`) is used for the four `B`-factorizations in `𝒪` and for each `B = d·e`
identity in `GaussianExactRanges`.

---

## 17. Where the Lean proof deviates from the textbook 2-isogeny descent

1. **Total isogeny maps, no rational-map convention.** `φ`, `φ̂` are defined by cases on Mathlib's
   affine point type, sending `O` and `(0,0)` to `O`; `φ̂` carries the normalization `1/4`, `1/8`
   so that `φ̂∘φ = [2]` holds literally (`phiHat_phi`), including the tangent/vertical branches.
   Homomorphicity of `φ, φ̂` is never needed: only `φ̂φ = [2]`, `φ(T+P) = φ(P)`, `φ̂(T'+Q) = φ̂(Q)`.
2. **Exactness is constructive** with explicit preimage formulas (§5), rather than via the
   cohomological Kummer sequence.
3. **Weak Mordell–Weil via `2E(K) = ker α`.** Because the dual image is exactly `{1, α'(T')}`,
   the proof identifies `ker α` with `2E(K)` directly and gets `[E:2E] = |im α|`. The textbook
   formula `[E:2E] = |im α|·|im α'| / |α'(ker φ̂)|` is proved in generality in
   `GaussianArithmetic.lean : dualKernel_card_mul_doubling_index` (the "correction factor"
   `|α'(ker φ̂)| = 2` here) but is not on the main path.
4. **Local solubility by exhaustive residue tables at powers of λ only.** No Hensel lifting or
   `ℚ₂`-computation; obstructions are found modulo `λ⁴, λ⁶, λ⁸, λ¹⁰` (`n = 4, 8, 16, 32`) with the
   λ-primitivity side condition. No odd-prime local conditions are needed: everything the UFD
   argument leaves is either λ-obstructed or globally realized.
5. **Squareclass group is the honest `Kˣ/Kˣ²`** (units quotient), and class inequalities are
   proved via norms (`N(π)=5`, `N(ρ)=17` non-squares; `i` not a square) rather than via
   a fixed basis of `K(S,2)`.
6. **Finite generation via Mathlib's abstract descent** (`AddCommGroup.fg_of_descent'`) with the
   naive `x`-height; the parallelogram law comes from Mathlib's `addSubMap` bound plus the
   identity `addSubMap(sym2x(P,Q)) = sym2x(P+Q, P−Q)`. No canonical height is constructed.
7. **Rank from the structure theorem:** `[E:2E] = 2ⁿ·|E[2]|` is derived from
   `AddCommGroup.equiv_free_prod_directSum_zmod`; odd torsion is deliberately left in the finite
   summand until §13–14.
8. **Torsion**: not via Nagell–Lutz / Lutz–Nagell over `ℤ[i]` and not via "prime-to-`p` torsion
   injects mod `p`" abstractly; instead, at the split prime 37, *all* torsion is pushed into the
   formal group by the finite exponent of the special fibre and killed by torsion-freeness of
   `Ê(37ℤ₃₇)`. Combined with the elementary 2-torsion (norm 272) and 3-torsion (inert 11,
   `𝔽₁₂₁` table) arguments to get exactly `{O, T}`.
9. Everything is over the PID `ℤ[i]`, so the "class group" term of the general descent is absent
   and the `S`-unit group mod squares is just `{1, i} × ⟨λ⟩ × ⟨π or ρ⟩`.

---

## 18. Fifteen-line summary of the descent

1. `4u⁸ − 8u² + 5 = N(q(u))`, `q(u) = (2u⁴−1) + i(2u²−2)`; clearing `u = m/n` gives a Pythagorean triple.
2. By primitive-triple classification, `q(u)` or `−i·q(u)` is a square in `ℚ(i)` (odd/even denominator).
3. Hence `(u,r)` lifts to `C₀: v² = q(u)` or `C₁: w² = −i q(u)`, mapping to `E₀: y² = x³+2ix²−(2+4i)x` via `(2u², 2uv)` or `E₁: y² = x³+2x²+(2+4i)x` via `(−2iu², −2iuw)`.
4. Both are `y² = x(x²+Ax+B)` with 2-torsion `T = (0,0)`; duals `E₀': X³−4iX²+(4+16i)X`, `E₁': X³−4X²−(4+16i)X`.
5. `φ(x,y) = (y²/x², y(B−x²)/x²)`, `φ̂(X,Y) = (Y²/4X², Y(A²−4B−X²)/8X²)`, `φ̂φ = [2]`, kernels `{O,T}`, `{O,T'}`.
6. Kummer maps `α(x,y) = [x]`, `α(T) = [B]`, `α'(T') = [A²−4B]`; `ker α = φ̂(E')`, `ker α' = φ(E)`.
7. `B₀ = iλ²π`, `B₁ = −iλ²π`, `A²−4B = ∓λ⁴ρ` with `λ = 1+i, π = 1+2i, ρ = 1+4i`; units mod squares `{1, i}`.
8. Valuation parity in the UFD `ℤ[i]` leaves 8 classes `{1,i}·{1,λ}·{1,π or ρ}` per curve.
9. Substituting `x = dz²` yields `W² = dU⁴ + AU²V² + (B/d)V⁴` with `U,V` coprime; exhaustive tables mod `4, 8, 16, 32` (λ-adic) exclude 4, 6, 6, 6 classes.
10. Survivors are all visible: `α(E₀) = {1,[i],[π],[iπ]}` (from `O, P=(2,2), P+T, T`), `α'(E₀') = {1,[ρ]}`, `α(E₁) = {1,[iπ]}`, `α'(E₁') = {1,[ρ]}`.
11. Since `α'(E') = {1, α'(T')}` and `φ̂(T') = O`, `ker α = 2E(K)`, so `[E₀:2E₀] = 4`, `[E₁:2E₁] = 2`; finite index + naive `x`-height + Mathlib `fg_of_descent'` give finite generation.
12. `E(K)[2] = {O,T}` because `N(A²−4B) = 272` is not a square; then `2ⁿ·2 = [E:2E]` gives rank 1 for `E₀`, rank 0 for `E₁`.
13. `ψ₃ = 3x⁴+4Ax³+6Bx²−B²` has no root in `𝔽₁₁(i)` (11 inert), so `E(K)[3] = 0`.
14. At the split prime 37 the two reductions of `E₀` have exponents 12 and 42 (of `E₁`: 28, 34); the formal group is torsion-free, so torsion is killed by 6 (resp. 2), hence torsion `= {O,T}`.
15. Therefore `E₀(ℚ(i)) ≅ ℤ × ℤ/2` (`gaussianE0_equiv`) and `E₁(ℚ(i)) = {O,(0,0)}`, so every `C₁`-point maps to `O` or `(0,0)` (`gaussianCoverOneEllipticClassified`).
