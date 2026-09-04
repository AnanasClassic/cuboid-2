# The linear–quartic ("1+4") branch: mathematical content of `lean/Cuboid2/LinearQuartic/`

Source files (all under `/Users/vlad/projects/cuboid-2/lean/Cuboid2/`):
`Polynomial.lean`, `LinearQuartic/Basic.lean`, `RootMap.lean`, `DirectSquareReduction.lean`,
`FermatAuxiliary.lean`, `SharipovCompletion.lean`, `SignedSquareCovers.lean`,
`SharipovImpossibility.lean`, `KnownPoints.lean`, `ClassificationBridge.lean`.

Target theorem (`SharipovImpossibility.lean`):

> **`linear_quartic_impossible_sharipov`.** Let $p,q\in\mathbb N$, $p,q>0$, $\gcd(p,q)=1$, $p\ne q$, and $s=(p/q)^2$.
> Then the normalized quintic $P_s(x)$ has **no rational root**, i.e. $\neg\,\mathrm{LinearQuarticCase}(s)$ where
> $\mathrm{LinearQuarticCase}(s) :\Leftrightarrow \exists r\in\mathbb Q,\ P_s(r)=0$ (definition in `Factorization.lean`).

It is consumed verbatim by `Main.lean` (`theorem linear_quartic_impossible := linear_quartic_impossible_sharipov`).
None of the nine files contains `sorry`, `axiom`, or `native_decide`. The only finite-certificate tactic is `decide`
(three lemmas over $\mathbb Z/3$ in `SignedSquareCovers.lean`).

Notation: $\mathrm{IsSquare}(x)$ means $\exists k,\ x=k\cdot k$ (Mathlib `IsSquare`).
$\varepsilon\in\{+1,-1\}$ is a `PhysicalSign` (`ε.value`), an inductive type with constructors `positive`, `negative` of values $1$, $-1$.

---

## 0. `Polynomial.lean` — the objects being studied

**Definitions.**

* `normalizedQuintic s` (= $P_s$), over any commutative ring $R$, $s\in R$:
  $$P_s(x)=x^5+(2+s)(3-2s)\,x^4+(1+10s+4s^2-14s^3+s^4)\,x^3-s(1-14s+4s^2+10s^3+s^4)\,x^2-s^3(1+2s)(3s-2)\,x-s^5 .$$
  (`normalizedQuinticLower s` is everything except $x^5$.)

* `sharipovPolynomialOver p q` (= $Q_{p,q}$), over any commutative ring, $p,q\in R$:
  $$Q_{p,q}(t)=t^{10}+(2q^2+p^2)(3q^2-2p^2)\,t^8+(q^8+10p^2q^6+4p^4q^4-14p^6q^2+p^8)\,t^6$$
  $$\qquad-p^2q^2(q^8-14p^2q^6+4p^4q^4+10p^6q^2+p^8)\,t^4-p^6q^6(q^2+2p^2)(3p^2-2q^2)\,t^2-p^{10}q^{10}.$$
  `sharipovPolynomial p q : ℤ[X]` and `sharipovPolynomialQ p q : ℚ[X]` are its specializations to $p,q\in\mathbb N$.

* `sharipovParameter p q` $:= s=(p/q)^2\in\mathbb Q$.

**Theorems** (all by `simp`/`field_simp`/degree lemmas; no arithmetic input):

* `normalizedQuintic_monic`, `normalizedQuintic_degree` ($\deg P_s=5$, monic); `sharipovPolynomialOver_monic`, `sharipovPolynomialOver_degree` ($\deg Q=10$).
* `sharipovPolynomial_coeff_zero`: constant term of $Q_{p,q}$ is $-p^{10}q^{10}$.
* `sharipovPolynomial_irreducible_iff_rational`: Gauss-lemma transfer $\mathbb Z[X]\leftrightarrow\mathbb Q[X]$ (Mathlib `Monic.irreducible_iff_irreducible_map_fraction_map`).
* **`eval_sharipov_scaling`** (over any field, $q\ne0$):
  $$Q_{p,q}(t)=q^{20}\,P_{(p/q)^2}\!\left(\frac{t^2}{q^4}\right).$$
  `eval_sharipovPolynomialQ_scaling` is the same for $p,q\in\mathbb N$, $q>0$, $s=$ `sharipovParameter p q`.

Thus a rational root $r$ of $P_s$ (a "linear factor" of $P_s$) is the object the 1+4 branch must exclude.

---

## 1. `Basic.lean` — the genus-two curve

**Definitions.**

* `linearQuarticCurveRhs t` $:= f(t)=t^5+21t^4+26t^3+10t^2+5t+1$ (over any commutative ring).
* `LinearQuarticAffinePoint`: a structure $(t,w)\in\mathbb Q^2$ with $w^2=f(t)$ (field `onCurve`). The curve is
  $$\mathcal C:\ w^2=t^5+21t^4+26t^3+10t^2+5t+1 .$$
* Five explicit affine points (each checked by `norm_num`): `linearQuarticNegOne` $=(-1,0)$, `linearQuarticZeroPlus` $=(0,1)$, `linearQuarticZeroMinus` $=(0,-1)$, `linearQuarticOnePlus` $=(1,8)$, `linearQuarticOneMinus` $=(1,-8)$.

**Theorem.** `linearQuarticCurveRhs_factorization` (`ring`):
$$f(t)=(t+1)\,g(t),\qquad g(t):=t^4+20t^3+6t^2+4t+1 .$$

*Used in the final chain:* only `linearQuarticCurveRhs` and `LinearQuarticAffinePoint` (with `onCurve`). The five named points and the factorization are not used by `linear_quartic_impossible_sharipov` (legacy Chabauty interface, §3.2/§9).

---

## 2. `RootMap.lean` — from a rational root of $P_s$ to a rational point of $\mathcal C$

All statements are for $s,y,U,V,t\in\mathbb Q$. Everything in this file is a polynomial/rational-function identity proved by `simp`+`field_simp`+`ring`, except where noted.

### 2.1 Scaled root equation

* `linearQuarticRootEquation s y` $:= R(s,y)$, where
  $$R(s,y)=s^2y^5+(-2s^3-s^2+6s)\,y^4+(s^4-14s^3+4s^2+10s+1)\,y^3+(-s^4-10s^3-4s^2+14s-1)\,y^2+(-6s^3+s^2+2s)\,y-s^2 .$$
* `eval_normalizedQuintic_mul_eq_rootEquation`: $P_s(sy)=s^3\,R(s,y)$.
* `linearQuarticRootEquation_eq_zero_of_isRoot`: if $s\ne0$ and $P_s(r)=0$ then $R(s,r/s)=0$.
* `linearQuarticRootEquation_right_ne_zero`: if $s\ne0$ and $R(s,y)=0$ then $y\ne0$ (because $R(s,0)=-s^2$).
* `linearQuarticRootEquation_neg_one`: $R(s,-1)=-2(s-1)^4$.

### 2.2 Reciprocal coordinates

* `linearQuarticReciprocal x` $:= x+x^{-1}$. Write $U=s+s^{-1}$, $V=y+y^{-1}$.
* `linearQuarticReciprocalQuotient U V` $:= Q(U,V)$, where
  $$Q(U,V)=U^4V-2U^4+4U^3V^2-8U^3V-10U^2V^3-108U^2V^2-192U^2V-128U^2+4UV^4-8UV^3+V^5-2V^4+64V^3+384V^2+768V+512 .$$
* `linearQuarticRootEquationMate s y` $:= M(s,y)$, where
  $$M(s,y)=s^2y^5+(6s^3-s^2-2s)\,y^4+(s^4+10s^3+4s^2-14s+1)\,y^3+(-s^4+14s^3-4s^2-10s-1)\,y^2+(2s^3+s^2-6s)\,y-s^2 .$$
  (Remark for the paper, not stated in Lean: $M(s,y)=s^4R(1/s,y)=-y^5R(s,1/y)$; $Q$ is the quotient of $R$ by the involutions $s\mapsto1/s$, $y\mapsto1/y$.)
* **`linearQuartic_reciprocalQuotient_identity`** ($s,y\ne0$):
  $$s^4y^5\,Q\!\left(s+\tfrac1s,\ y+\tfrac1y\right)=R(s,y)\,M(s,y).$$
* `linearQuartic_reciprocalQuotient_eq_zero`: $R(s,y)=0$, $s,y\ne0$ $\Rightarrow$ $Q(U,V)=0$.
* `linearQuartic_reciprocal_sq_sub_four`: $(x+x^{-1})^2-4=(x-x^{-1})^2$ ($x\ne0$).
* `linearQuartic_reciprocal_sub_two`: $x+x^{-1}-2=(x-1)^2/x$. `linearQuartic_reciprocal_add_two`: $x+x^{-1}+2=(x+1)^2/x$.
* `linearQuartic_reciprocal_ne_two`: $x\ne0$, $x\ne1\Rightarrow x+x^{-1}\ne2$.

### 2.3 The inverse slope $t$ and the parametrization $U(t),V(t)$

* `linearQuarticSlope U V` $:= t=\dfrac{V+2}{U-2}$.
* `linearQuarticSlope_cross`: $(U-2)t=V+2$ for $U\ne2$.
* `linearQuarticSlope_reciprocal` ($s,y\ne0$, $s\ne1$):
  $$t=\frac{s\,(y+1)^2}{y\,(s-1)^2}.$$
* Rational functions $U(t)=N_U(t)/D_U(t)$, $V(t)=N_V(t)/D_V(t)$ with
  $$N_U(t)=2\,(t^5+6t^4+30t^3+16t^2+9t+2),\qquad D_U(t)=t\,(t-1)^2\,(t^2+6t+1),$$
  $$N_V(t)=2\,(t^4+36t^3+22t^2+4t+1),\qquad D_V(t)=(t-1)^2\,(t^2+6t+1)$$
  (`linearQuarticUNumerator`, `linearQuarticUDenominator`, `linearQuarticVNumerator`, `linearQuarticVDenominator`).
* **`linearQuartic_inverseSlope_U`** ($U\ne2$, $t=(V+2)/(U-2)$): $(U-2)^4\,\bigl(N_U(t)-U\,D_U(t)\bigr)=-Q(U,V)$.
* **`linearQuartic_inverseSlope_V`** (same): $(U-2)^4\,\bigl(N_V(t)-V\,D_V(t)\bigr)=-Q(U,V)$.
  So on $Q(U,V)=0$ one has $U=U(t)$, $V=V(t)$: the curve $Q=0$ is rational, parametrized by $t$.
* **`linearQuartic_V_square_identity`**: $N_V(t)^2-4D_V(t)^2=256\,t^2\,f(t)$.
* `linearQuartic_remainingDenominator_ne_zero`: $t^2+6t+1\ne0$ for $t\in\mathbb Q$ (else $(t+3)^2=8$; `nlinarith` + `norm_num` for $\neg\mathrm{IsSquare}(8:\mathbb Q)$).
* **`linearQuartic_curve_identity_of_V`** ($y\ne0$, $t\ne0$, $N_V(t)=(y+y^{-1})D_V(t)$):
  $$\left(\frac{(y-y^{-1})\,D_V(t)}{16\,t}\right)^2=f(t).$$
  Proof: $(y-y^{-1})^2D_V^2=((y+y^{-1})^2-4)D_V^2=N_V^2-4D_V^2=256t^2f(t)$.
* `linearQuartic_rootSlope_ne_zero` ($s\ne0,1$, $y\ne0$, $R(s,y)=0$): $t\ne0$. (If $t=0$ then $V=-2$, so $(y+1)^2=0$, $y=-1$, and $R(s,-1)=-2(s-1)^4=0$ forces $s=1$.)

### 2.4 The map

**`normalizedRootToLinearQuartic`** (a `def` producing a `LinearQuarticAffinePoint`): given $s>0$, $s\ne1$, $P_s(r)=0$, put
$$y=r/s,\quad U=s+s^{-1},\quad V=y+y^{-1},\quad t=\frac{V+2}{U-2},\quad w=\frac{(y-y^{-1})\,D_V(t)}{16\,t}.$$
Then $(t,w)\in\mathcal C(\mathbb Q)$. `normalizedRootToLinearQuartic_t` records $t=$ `linearQuarticSlope (s+s⁻¹) (r/s+(r/s)⁻¹)` (by `rfl`).

Chain inside the def: `linearQuarticRootEquation_eq_zero_of_isRoot` → `linearQuarticRootEquation_right_ne_zero` → `linearQuartic_reciprocal_ne_two` → `linearQuartic_reciprocalQuotient_eq_zero` → `linearQuartic_inverseSlope_V` (gives $N_V(t)=V D_V(t)$) → `linearQuartic_rootSlope_ne_zero` → `linearQuartic_curve_identity_of_V`.

---

## 3. `ClassificationBridge.lean` — the $U$-cross identity and the three special abscissas

(Imports `Factorization`, `KnownPoints`, `RootMap`. Only §3.1 is used by the final proof; §3.2 is legacy.)

### 3.1 Used by the final chain

* `linearQuartic_reciprocal_eq_two`: $s\ne0$, $s+s^{-1}=2\Rightarrow s=1$. `linearQuartic_reciprocal_eq_neg_two`: $s\ne0$, $s+s^{-1}=-2\Rightarrow s=-1$ (`field_simp`, `nlinarith [sq_nonneg (s+1)]`).
* **`normalizedRootToLinearQuartic_U_cross`** ($s>0$, $s\ne1$, $P_s(r)=0$, $t$ the abscissa of the constructed point):
  $$N_U(t)=(s+s^{-1})\,D_U(t).$$
  Proof: `linearQuartic_inverseSlope_U` with $Q(U,V)=0$ and $U\ne2$.
* `linearQuartic_U_lift_at_neg_one`: $s\ne0$ and $N_U(-1)=(s+s^{-1})D_U(-1)$ $\Rightarrow s=-1$. (Numerically $N_U(-1)=-32$, $D_U(-1)=16$, so $s+s^{-1}=-2$; `norm_num`, `linarith`.)
* `linearQuartic_no_U_lift_at_zero`: $N_U(0)=U\cdot D_U(0)$ is impossible ($N_U(0)=4$, $D_U(0)=0$; `norm_num`).
* `linearQuartic_no_U_lift_at_one`: $N_U(1)=U\cdot D_U(1)$ is impossible ($N_U(1)=128$, $D_U(1)=0$; `norm_num`).

So $t=0$ and $t=1$ are genuine poles of $U(t)$, and $t=-1$ would force $s=-1$.

### 3.2 Legacy (conditional on an unproved Chabauty classification)

* `linearQuartic_affine_abscissa_of_classification`: **assuming** `LinearQuarticRationalPointClassification` (§9), every affine rational point of $\mathcal C$ has $t\in\{-1,0,1\}$.
* `linearQuarticCase_impossible_of_point_classification`: **assuming** the same classification, $\neg\mathrm{LinearQuarticCase}(s)$ for all $s>0$, $s\ne1$.

Both take the classification as an explicit hypothesis `hclass`; neither is used by `linear_quartic_impossible_sharipov`.

---

## 4. `DirectSquareReduction.lean` — the square character of $t(t+1)(t^2+6t+1)$

(Imports `ClassificationBridge`. All proofs: `ring`, `field_simp`, `nlinarith`, `positivity`.)

* `linearQuarticDirectH t` $:= h(t)=t^2+6t+1$.
* **`linearQuartic_U_plus_two_factor`**: $N_U(t)+2D_U(t)=4\,(t+1)^5$.
* `linearQuartic_U_minus_two_factor`: $N_U(t)-2D_U(t)=4\,g(t)=4(t^4+20t^3+6t^2+4t+1)$. (Not used in the chain; it explains $U(t)^2-4=16(t+1)^4 f(t)/D_U(t)^2$, i.e. why $\mathcal C$ appears.)
* **`linearQuartic_squareParameter_character`**: if $s=z^2$ with $z\ne0$, $t\ne1$, and $N_U(t)=(s+s^{-1})D_U(t)$, then
  $$\mathrm{IsSquare}\bigl(t\,(t+1)\,(t^2+6t+1)\bigr).$$
  Proof: $s+s^{-1}+2=\left(\frac{s+1}{z}\right)^2$; multiplying the cross identity by $D_U$: $\left(\frac{s+1}{z}\right)^2 t(t-1)^2h(t)=N_U+2D_U=4(t+1)^5$; hence
  $$t(t+1)h(t)=\left(\frac{2z(t+1)^3}{(s+1)(t-1)}\right)^2 .$$
* **`linearQuartic_positiveSlope_genusTwo`**: $t=u^2\ne0$ and $\mathrm{IsSquare}(t(t+1)h(t))$ $\Rightarrow$ $\mathrm{IsSquare}\bigl((u^2+1)(u^4+6u^2+1)\bigr)$ (witness $k/u$; $t(t+1)h(t)=u^2(u^2+1)(u^4+6u^2+1)$).
* **`linearQuartic_negativeSlope_genusTwo`**: $t=-u^2\ne0$ and $\mathrm{IsSquare}(t(t+1)h(t))$ $\Rightarrow$ $\mathrm{IsSquare}\bigl((u^2-1)(u^4-6u^2+1)\bigr)$ ($t(t+1)h(t)=u^2(u^2-1)(u^4-6u^2+1)$).
* `linearQuartic_positiveSlope_sextic_identity`: $(u^2+1)(u^4+6u^2+1)=u^6+7u^4+7u^2+1$; `linearQuartic_negativeSlope_sextic_identity`: $(u^2-1)(u^4-6u^2+1)=u^6-7u^4+7u^2-1$ (documentary, `ring`).

The two **signed-square covers** are thus
$$\mathcal D_+:\ v^2=(u^2+1)(u^4+6u^2+1),\qquad \mathcal D_-:\ v^2=(u^2-1)(u^4-6u^2+1).$$

---

## 5. `SharipovCompletion.lean` — every rational root of $P_{(p/q)^2}$ is a signed square (Newton polygon)

(Imports `DirectSquareReduction` and `QuadraticReduction.C012`.) Objects imported from `C012.lean` (outside the branch; quoted so the argument is reproducible):

* `homogeneousQuintic p q` $:=H_{p,q}(X)\in\mathbb Z[X]$,
  $$H_{p,q}(X)=X^5+c_4X^4+c_3X^3+c_2X^2+c_1X+c_0,$$
  $$c_4=(2q^2+p^2)(3q^2-2p^2),\quad c_3=q^8+10p^2q^6+4p^4q^4-14p^6q^2+p^8,$$
  $$c_2=-p^2q^2\,(q^8-14p^2q^6+4p^4q^4+10p^6q^2+p^8),\quad c_1=-p^6q^6(q^2+2p^2)(3p^2-2q^2),\quad c_0=-p^{10}q^{10}.$$
  Note $Q_{p,q}(t)=H_{p,q}(t^2)$ coefficientwise, and `normalizedQuintic_scaleRoots_eq_homogeneous`: $H_{p,q}(X)=q^{20}P_s(X/q^4)$, $s=(p/q)^2$ ($H$ is the `scaleRoots` of $P_s$ by $q^4$).
* Valuations at a prime $\ell\mid pq$, $\gcd(p,q)=1$, $k:=v_\ell(pq)\ge1$ (`homogeneousQuintic_coeff_three_not_dvd`/`_padicValInt`, `_coeff_two_padicValInt`, `_coeff_two_ne_zero`, `_coeff_one_pow_dvd`, `padicValInt_neg_parameter_powers`):
  $$v_\ell(c_3)=0,\qquad v_\ell(c_2)=2k,\qquad v_\ell(c_1)\ge 6k,\qquad v_\ell(c_0)=10k .$$
* `int_signedSquare_of_even_natAbs_factorization`: $B\in\mathbb Z\setminus\{0\}$ with all prime multiplicities of $|B|$ even $\Rightarrow$ $B=\varepsilon d^2$, $\varepsilon\in\{\pm1\}$, $d\in\mathbb Z$.

Theorems in this file:

* `exists_integral_scaled_linear_root` ($q>0$, $P_s(r)=0$): $B:=q^4r\in\mathbb Z$ and $H_{p,q}(B)=0$. (Mathlib `scaleRoots_eval₂_eq_zero`, `Polynomial.isIntegral_coeff_of_dvd` with $X-B\mid H$, $H$ monic, `IsIntegrallyClosed.isIntegral_iff` for $\mathbb Z$.)
* `integral_linear_root_dvd_parameter_power`: $H_{p,q}(B)=0\Rightarrow B\mid p^{10}q^{10}$.
* `padicValInt_pow`, `pow_dvd_of_le_padicValInt`, `not_pow_dvd_of_padicValInt_lt`: $v(z^n)=n\,v(z)$; $n\le v_\ell(z)\Rightarrow\ell^n\mid z$; $v_\ell(z)<n$, $z\ne0\Rightarrow\ell^n\nmid z$ (Mathlib `padicValInt_dvd_iff`, `padicValNat.pow`).
* `four_term_unique_low_impossible`: $\ell^n\nmid a$, $\ell^n\mid b,c,d$ $\Rightarrow a+b+c+d\ne0$.
* **`integral_linear_root_factorization_even`** ($p,q>0$ coprime, $B\ne0$, $H_{p,q}(B)=0$, $\ell$ prime, $\ell\mid pq$): $v_\ell(B)$ is even. Proof: let $\beta=v_\ell(B)$, $k=v_\ell(pq)$, and
  $$0=H(B)=\underbrace{B^3(B^2+c_4B+c_3)}_{L}+\underbrace{c_2B^2}_{M}+\underbrace{c_1B}_{N}+\underbrace{c_0}_{C}.$$
  If $\beta=0$ done. If $\beta>0$ then $\ell\mid B$, $B^2+c_4B+c_3\equiv c_3\not\equiv0\pmod\ell$, so $v(L)=3\beta$, $v(M)=2k+2\beta$, $v(N)\ge6k+\beta$, $v(C)=10k$. Then
  - $\beta<2k$: $v(L)=3\beta$ is the unique minimum — contradiction;
  - $2k<\beta<4k$: $v(M)=2k+2\beta$ is the unique minimum — contradiction;
  - $\beta>4k$: $v(C)=10k$ is the unique minimum — contradiction.
  Hence $\beta\in\{0,2k,4k\}$ (Newton polygon of $H$ at $\ell$: slopes $0,0,2k,4k,4k$), all even. Case splits by `omega`.
* **`normalizedQuintic_root_signedSquare_sharipov`** ($p,q>0$ coprime, $P_{(p/q)^2}(r)=0$):
  $$\exists\,\varepsilon\in\{\pm1\},\ u\in\mathbb Q:\quad r=\varepsilon u^2 .$$
  Proof: $B=q^4r\ne0$ (as $P_s(0)=-s^5\ne0$); for $\ell\mid pq$ apply the previous theorem; for $\ell\nmid pq$, $B\mid p^{10}q^{10}$ gives $\ell\nmid B$; so $B=\varepsilon d^2$, $r=\varepsilon(d/q^2)^2$.

---

## 6. `FermatAuxiliary.lean` — $a^4-b^4=c^2$ and $x^4+y^4=2z^2$

(Imports only Mathlib `NumberTheory.FLT.Four`, `Data.Rat.Sqrt`.)

* `Fermat4Sub a b c` $:\Leftrightarrow a\ne0\wedge b\ne0\wedge c\ne0\wedge a^4-b^4=c^2$ ($a,b,c\in\mathbb Z$).
* `Fermat4Sub.mul`: $k\ne0\Rightarrow$ $\mathrm{Fermat4Sub}(a,b,c)\iff\mathrm{Fermat4Sub}(ka,kb,k^2c)$.
* `Fermat4Sub.Minimal a b c`: solution with $|a|$ minimal. `exists_minimal` (Mathlib `Nat.find`), `neg_first_of_minimal`, `exists_pos_minimal` (may assume $a>0$).
* `coprime_of_minimal`: minimal $\Rightarrow\gcd(a,b)=1$ (a common prime $\pi$ gives $\pi^2\mid c$ and a smaller solution by `mul`).
* `squareLeg_coprime`: $\gcd(a,b)=1\Rightarrow\gcd(b^2,c)=1$.
* **`Fermat4Sub.not_minimal`**: a minimal solution with $a>0$ is contradictory. $(b^2)^2+c^2=(a^2)^2$ is a primitive Pythagorean triple (Mathlib `PythagoreanTriple.even_odd_of_coprime`, `PythagoreanTriple.coprime_classification'`).
  - *$b^2$ odd:* $b^2=m^2-n^2$, $c=2mn$, $a^2=m^2+n^2$, $m>0$, $n\ne0$. Then $m^4-n^4=(m^2+n^2)(m^2-n^2)=a^2b^2=(ab)^2$: a solution with $0<m<a$.
  - *$b^2$ even:* $c=m^2-n^2$, $b^2=2mn$, $a^2=m^2+n^2$, $m,n>0$ coprime of opposite parity. Parametrize $(m,n,a)$ again: ($m$ even) $n=r^2-s^2$, $m=2rs$, $a=r^2+s^2$; ($m$ odd) $m=r^2-s^2$, $n=2rs$, $a=r^2+s^2$; $r,s>0$ coprime, $r^2-s^2>0$. Then $b=2b_0$ and $b_0^2=r\,s\,(r^2-s^2)$ with pairwise coprime positive factors, so (Mathlib `Int.sq_of_isCoprime`, three times) $r=r_0^2$, $s=s_0^2$, $r^2-s^2=t_0^2$. Then $r_0^4-s_0^4=t_0^2$ with $|r_0|\le r_0^2=r<r^2+s^2=a$ (Mathlib `Int.natAbs_le_self_sq`). Contradiction.
* **`not_fermat_4_sub`**: $a,b,c\in\mathbb Z\setminus\{0\}\Rightarrow a^4-b^4\ne c^2$.
* `rat_two_not_square`: $\neg\mathrm{IsSquare}(2:\mathbb Q)$ (`Rat.isSquare_intCast_iff`; then $2\mid a$, $4\mid 2$).
* **`fourth_add_fourth_eq_two_square`**: $x,y,z\in\mathbb Z$, $x^4+y^4=2z^2\Rightarrow x^2=y^2$. Proof: $x=0$ (or $y=0$) makes $2=(y^2/z)^2$ a rational square; otherwise with $d=z^2-y^4$ the identity
  $$z^4-(xy)^4-(z^2-y^4)^2=y^4\bigl(2z^2-x^4-y^4\bigr)=0$$
  gives $z^4-(xy)^4=d^2$; $d=0$ iff $x^4=y^4$ iff $x^2=y^2$; otherwise `not_fermat_4_sub` on $(z,xy,d)$.

Mathlib inputs: `PythagoreanTriple.coprime_classification'`, `PythagoreanTriple.even_odd_of_coprime`, `Int.sq_of_isCoprime`, `Int.isCoprime_iff_gcd_eq_one`, `IsCoprime.*`, `Nat.find`, `Int.natAbs_le_self_sq`, `Int.Prime.dvd_pow'`, `Rat.isSquare_intCast_iff`. Nonlinear steps by `nlinarith`; identities by `ring`.

---

## 7. `SignedSquareCovers.lean` — rational points on $\mathcal D_+$ and on $\mathcal D_-\times\mathcal C$

(Imports `DirectSquareReduction`, `FermatAuxiliary`, `SharipovCompletion`.)

### 7.1 Positive cover $\mathcal D_+:\ v^2=(u^2+1)(u^4+6u^2+1)$

Write $u=m/n$ in lowest terms ($m=$ `u.num`, $n=$ `u.den`, $\gcd(m,n)=1$, $n>0$).

* `positiveCoverA m n` $:=A=m^2+n^2$; `positiveCoverB m n` $:=B=m^4+6m^2n^2+n^4$.
* `positiveCoverB_eq_A_sq_add`: $B=A^2+4(mn)^2$. `positiveCover_fourth_identity`: $(m+n)^4+(m-n)^4=2B$.
* `positiveCoverA_coprime_mul`: $\gcd(A,mn)=1$ (Mathlib `Int.isCoprime_of_sq_sum'`).
* `positiveCover_coprime_of_A_odd`: $A$ odd $\Rightarrow\gcd(A,B)=1$.
* `positiveCover_halves_coprime`: $m,n$ odd, $A=2A_0$, $B=2B_0$ $\Rightarrow\gcd(A_0,B_0)=1$ ($A_0$ odd, $B_0=2(mn)^2+2A_0^2$).
* **`positiveSlope_cover_classification`**: $\mathrm{IsSquare}\bigl((u^2+1)(u^4+6u^2+1)\bigr)$ $\Rightarrow$ $u=0$ or $u^2=1$.
  Proof: $(u^2+1)(u^4+6u^2+1)\,n^6=AB$, so $AB=K^2$ in $\mathbb Z$ (`Rat.isSquare_intCast_iff`), $A,B>0$.
  - $m,n$ both even: contradicts coprimality.
  - opposite parity: $A$ odd, $\gcd(A,B)=1$, so $B=Y^2$ (`Int.sq_of_isCoprime`, sign fixed by $B>0$); $(m+n)^4+(m-n)^4=2Y^2$; `fourth_add_fourth_eq_two_square` gives $(m+n)^2=(m-n)^2$, so $mn=0$, $m=0$, $u=0$.
  - both odd: $A=2A_0$, $B=2B_0$, $4A_0B_0=K^2$, $K=2K_0$, $A_0B_0=K_0^2$, $\gcd(A_0,B_0)=1$, $B_0=Y^2$, so $(m+n)^4+(m-n)^4=2B=(2Y)^2$. If $m\pm n\ne0$, Mathlib **`not_fermat_42`** ($a,b\ne0\Rightarrow a^4+b^4\ne c^2$) gives a contradiction; else $m=\mp n$, $u^2=1$.

### 7.2 Negative branch: $\mathcal D_-$ together with $\mathcal C$ at $t=-u^2$

* `negativeCoverDelta m n` $:=\delta=m^2-n^2$; `negativeCoverD m n` $:=D=m^4-6m^2n^2+n^4$;
  `negativeCurveG m n` $:=G=m^8-20m^6n^2+6m^4n^4-4m^2n^6+n^8$ (all over any commutative ring).
  With $u=m/n$: $(u^2-1)(u^4-6u^2+1)\,n^6=\delta D$ and $(1-u^2)(u^8-20u^6+6u^4-4u^2+1)\,n^{10}=\delta\cdot(-G)$.
* Finite certificates over $\mathbb F_3=$ `ZMod 3`, each by `decide`:
  - **`negativeCovers_mod_three_delta`**: $m,n,K,L\in\mathbb F_3$, $(m,n)\ne(0,0)$, $\delta D=K^2$, $-\delta G=L^2$ $\Rightarrow\delta=0$. (Hand check: $\delta\ne0$ forces exactly one of $m,n$ to vanish; $m=0$: $\delta D=-1$ non-square; $n=0$: $-\delta G=-1$ non-square.)
  - **`negativeCovers_mod_three_unit_impossible`**: $m,n,e\ne0$ in $\mathbb F_3$: $eD=K^2$ and $e(-G)=L^2$ are contradictory. (Hand check: $m^2=n^2=1$, $D\equiv-4\equiv2$, $-G\equiv16\equiv1$; $2e$ and $e$ cannot both be squares with $e\ne0$.)
  - `negativeCover_factors_mod_three_ne_zero`: $m,n\ne0$ in $\mathbb F_3\Rightarrow D\ne0$, $G\ne0$.
* **`negativeSlope_cover_pair_classification`**: for $u\in\mathbb Q$,
  $$\mathrm{IsSquare}\bigl((u^2-1)(u^4-6u^2+1)\bigr)\ \wedge\ \mathrm{IsSquare}\bigl((1-u^2)(u^8-20u^6+6u^4-4u^2+1)\bigr)\ \Longrightarrow\ u^2=1 .$$
  Proof: $\delta D=K^2$, $\delta(-G)=L^2$ in $\mathbb Z$. If $\delta=0$, $m^2=n^2$. Otherwise the first `decide` lemma (mod 3) gives $3\mid\delta$; coprimality forces $m,n\not\equiv0\pmod3$, hence $3\nmid D,G$; so $v_3(\delta)=2v_3(K)=2v_3(L)=:2j$. Write $\delta=3^{2j}e$, $3\nmid e$, $K=3^jK_0$, $L=3^jL_0$; cancel: $eD=K_0^2$, $e(-G)=L_0^2$; reduce mod 3 and apply the second `decide` lemma. (Uses `padicValInt.mul`, `padicValInt_dvd`, `pow_dvd_of_le_padicValInt`, `not_pow_dvd_of_padicValInt_lt`, `ZMod.intCast_zmod_eq_zero_iff_dvd`, `Int.Prime.dvd_pow'`.)

---

## 8. `SharipovImpossibility.lean` — assembly

* **`normalizedRootToLinearQuartic_signedSquare_t`**: if $s=z^2$ ($z\ne0$), $s>0$, $s\ne1$, $P_s(r)=0$, $r=\varepsilon u^2$, then the abscissa of the constructed point is $t=\varepsilon v^2$ with
  $$v=\frac{z^2\,(r/s+1)}{u\,(s-1)} .$$
  (From $t=\dfrac{s(y+1)^2}{y(s-1)^2}$, $y=r/s=\varepsilon u^2/z^2$, $1/y=\varepsilon z^2/u^2$: $t=\varepsilon\bigl(z^2(y+1)/(u(s-1))\bigr)^2$; `cases ε`, `field_simp`.)

* **`linear_quartic_impossible_sharipov`** ($p,q>0$, $\gcd(p,q)=1$, $p\ne q$): $\neg\mathrm{LinearQuarticCase}((p/q)^2)$. Given a rational root $r$:
  1. $s=(p/q)^2>0$, $s\ne1$ (`sharipovParameter_pos`, `sharipovParameter_ne_one`, `Factorization.lean`), $z=p/q\ne0$, $s=z^2$.
  2. $r=\varepsilon u^2$ (`normalizedQuintic_root_signedSquare_sharipov`, §5).
  3. Build $(t,w)\in\mathcal C(\mathbb Q)$ (`normalizedRootToLinearQuartic`, §2.4) and $N_U(t)=(s+s^{-1})D_U(t)$ (`normalizedRootToLinearQuartic_U_cross`, §3.1).
  4. $t\ne0$, $t\ne1$ (`linearQuartic_no_U_lift_at_zero`, `_at_one`).
  5. $\mathrm{IsSquare}(t(t+1)(t^2+6t+1))$ (`linearQuartic_squareParameter_character`, §4).
  6. $t=\varepsilon v^2$ (`normalizedRootToLinearQuartic_signedSquare_t`).
  7. **Case $\varepsilon=+1$**, $t=v^2$: `linearQuartic_positiveSlope_genusTwo` puts $v$ on $\mathcal D_+$; `positiveSlope_cover_classification` gives $v=0$ ($t=0$, contradicts 4) or $v^2=1$ ($t=1$, contradicts 4).
  8. **Case $\varepsilon=-1$**, $t=-v^2$: `linearQuartic_negativeSlope_genusTwo` gives $\mathrm{IsSquare}((v^2-1)(v^4-6v^2+1))$; from $w^2=f(-v^2)$ and the `ring` identity
     $$f(-v^2)=(1-v^2)(v^8-20v^6+6v^4-4v^2+1)$$
     the second square follows; `negativeSlope_cover_pair_classification` yields $v^2=1$, so $t=-1$; `linearQuartic_U_lift_at_neg_one` gives $s=-1$, contradicting $s>0$ (`linarith`).

---

## 9. `KnownPoints.lean` — legacy Chabauty interface (not used by the final theorem)

* `LinearQuarticRationalPoint` $:=$ `infinity` $\mid$ `affine (P : LinearQuarticAffinePoint)`: rational points of the odd-degree projective model of $\mathcal C$ (one point at infinity).
* `knownLinearQuarticRationalPoints` $:=[\infty,(-1,0),(0,1),(0,-1),(1,8),(1,-8)]$.
* `LinearQuarticRationalPointClassification : Prop` $:=$ "every rational point of $\mathcal C$ lies in this six-element list" — a **`def` of a proposition, never proved** in the repository (the statement $\#\mathcal C(\mathbb Q)=6$ one would obtain by Chabauty–Coleman).
* `mem_knownLinearQuarticRationalPoints_iff`: membership unfolds to six equalities (`simp`).

Its only consumer is §3.2. The Sharipov-specialized proof of §8 avoids this assumption entirely: because $s$ is a square, "all rational points of $\mathcal C$" is replaced by the covers $\mathcal D_\pm$, handled by Fermat descent and a mod-3 obstruction.

---

## 10. Dependency graph ending in `linear_quartic_impossible_sharipov`

```
Polynomial.lean: normalizedQuintic, sharipovParameter
Factorization.lean (outside branch): LinearQuarticCase, sharipovParameter_pos, sharipovParameter_ne_one
C012.lean (outside branch): homogeneousQuintic + coefficient valuations, PhysicalSign,
                            int_signedSquare_of_even_natAbs_factorization,
                            normalizedQuintic_scaleRoots_eq_homogeneous, map_homogeneousQuintic

Basic.lean ─ linearQuarticCurveRhs, LinearQuarticAffinePoint
   └─ RootMap.lean ─ R(s,y), Q(U,V), M(s,y), slope t, U(t), V(t), curve identity,
        normalizedRootToLinearQuartic, linearQuarticSlope_reciprocal
        ├─ ClassificationBridge.lean (§3.1 only) ─ normalizedRootToLinearQuartic_U_cross,
        │      linearQuartic_U_lift_at_neg_one, linearQuartic_no_U_lift_at_zero/_at_one
        │      └─ DirectSquareReduction.lean ─ N_U+2D_U=4(t+1)^5,
        │             linearQuartic_squareParameter_character,
        │             linearQuartic_positiveSlope_genusTwo, linearQuartic_negativeSlope_genusTwo
        │             ├─ SharipovCompletion.lean ─ Newton polygon,
        │             │      normalizedQuintic_root_signedSquare_sharipov,
        │             │      padicValInt helpers (reused in SignedSquareCovers)
        │             └─ SignedSquareCovers.lean (imports FermatAuxiliary + SharipovCompletion)
        │                    positiveSlope_cover_classification  [fourth_add_fourth_eq_two_square, not_fermat_42]
        │                    negativeSlope_cover_pair_classification [3 × decide over ZMod 3]
        └─ FermatAuxiliary.lean ─ not_fermat_4_sub, fourth_add_fourth_eq_two_square, rat_two_not_square

SharipovImpossibility.lean ─ normalizedRootToLinearQuartic_signedSquare_t,
                             linear_quartic_impossible_sharipov  ──▶ Main.lean (linear_quartic_impossible)
```

**Needed files:** `Polynomial`, `Basic`, `RootMap`, `ClassificationBridge` (§3.1 theorems only, but the file — hence `KnownPoints` — is in the import chain), `DirectSquareReduction`, `FermatAuxiliary`, `SharipovCompletion`, `SignedSquareCovers`, `SharipovImpossibility`; plus external `Factorization.lean` and `QuadraticReduction/C012.lean`.

**Legacy / not used by the final theorem:** `KnownPoints.lean` (entirely); `ClassificationBridge.lean` §3.2 (`linearQuartic_affine_abscissa_of_classification`, `linearQuarticCase_impossible_of_point_classification`, both assuming the unproved `LinearQuarticRationalPointClassification`); the five named points and `linearQuarticCurveRhs_factorization` in `Basic.lean`; `linearQuartic_U_minus_two_factor` and the two `*_sextic_identity` lemmas in `DirectSquareReduction.lean`. (`DescentCertificates`, `DescentCompletion`, `FiniteCounts`, `LocalP5` in the same directory were not read; they are not imported by `SharipovImpossibility.lean`.)

---

## 11. Proof-method classification

| Kind | Where |
|---|---|
| **`decide` (finite certificates)** | `negativeCovers_mod_three_delta` ($3^4$ cases), `negativeCovers_mod_three_unit_impossible` ($3^5$ cases), `negativeCover_factors_mod_three_ne_zero` ($3^2$ cases) — `SignedSquareCovers.lean`, over `ZMod 3`. No `native_decide` anywhere. |
| **`norm_num` numerics** | five curve points (`Basic`); $N_U,D_U$ at $t\in\{-1,0,1\}$ (`ClassificationBridge`); $\neg\mathrm{IsSquare}(8:\mathbb Q)$ (`RootMap`); $\neg\mathrm{IsCoprime}(2,2)$, $\neg\mathrm{IsCoprime}(3,3)$, $4\nmid2$. |
| **`ring` / `field_simp` / `simp` identities** | every formula of §1, §2, §4: $P_s(sy)=s^3R$; $s^4y^5Q(U,V)=RM$; $(x\pm x^{-1})$ identities; `linearQuartic_inverseSlope_U/V`; $N_V^2-4D_V^2=256t^2f$; $N_U\pm2D_U$ factorizations; square-character witness; signed-square witness $v$; $f(-v^2)$ factorization; $(m+n)^4+(m-n)^4=2B$; $B=A^2+4(mn)^2$; the $d$-identity in `fourth_add_fourth_eq_two_square`; the $Q_{p,q}$ scaling identity in `Polynomial.lean`. |
| **`nlinarith` / `linarith` / `positivity` / `omega`** | $(t+3)^2=8$; $s+s^{-1}=-2\Rightarrow s=-1$; positivity/parity bookkeeping in the Fermat descent; all valuation case splits of the Newton-polygon theorem (`omega`). |
| **Mathlib theorems (named)** | `not_fermat_42` ($a^4+b^4\ne c^2$, `Mathlib.NumberTheory.FLT.Four`); `PythagoreanTriple.coprime_classification'`, `PythagoreanTriple.even_odd_of_coprime`; `Int.sq_of_isCoprime`; `Int.isCoprime_of_sq_sum'`; `Int.isCoprime_two_right`; `Rat.isSquare_intCast_iff`; `Int.natAbs_le_self_sq`; `Int.Prime.dvd_pow'`; `Nat.find`/`Nat.find_min'`; `Polynomial.isIntegral_coeff_of_dvd`, `IsIntegrallyClosed.isIntegral_iff`, `scaleRoots_eval₂_eq_zero`, `dvd_iff_isRoot`, `Monic.irreducible_iff_irreducible_map_fraction_map`; `padicValInt.mul`, `padicValInt.eq_zero_of_not_dvd`, `padicValInt_dvd_iff`, `padicValInt_dvd`, `padicValNat.pow`, `one_le_padicValNat_of_dvd`; `Nat.factorization_eq_zero_iff`, `Nat.Prime.not_coprime_iff_dvd`; `ZMod.intCast_zmod_eq_zero_iff_dvd`. |
| **Own descent (not in Mathlib)** | `not_fermat_4_sub` ($a^4-b^4\ne c^2$) by infinite descent on $\lvert a\rvert$ through two Pythagorean parametrizations; `fourth_add_fourth_eq_two_square` ($x^4+y^4=2z^2\Rightarrow x^2=y^2$) reduced to it. |
| **Own $p$-adic argument** | `integral_linear_root_factorization_even` (Newton polygon at each $\ell\mid pq$: $v_\ell(B)\in\{0,2k,4k\}$). |

---

## 12. Ten-line summary of the branch's proof strategy

1. A rational root $r$ of $P_s$, $s=(p/q)^2$, scales to an integer root $B=q^4r$ of the monic $H_{p,q}(X)=q^{20}P_s(X/q^4)$ (= Sharipov's $Q_{p,q}$ in $X=t^2$), with $B\mid p^{10}q^{10}$.
2. Newton polygon at each prime $\ell\mid pq$ ($v(c_3)=0$, $v(c_2)=2k$, $v(c_1)\ge6k$, $v(c_0)=10k$, $k=v_\ell(pq)$) forces $v_\ell(B)\in\{0,2k,4k\}$; hence $r=\varepsilon u^2$ is a signed rational square.
3. Put $y=r/s$, $U=s+1/s$, $V=y+1/y$; then $Q(U,V)=0$ for an explicit quintic $Q$ (identity $s^4y^5Q=R(s,y)M(s,y)$).
4. The slope $t=(V+2)/(U-2)=s(y+1)^2/(y(s-1)^2)$ inverts a rational parametrization $U=N_U/D_U$, $V=N_V/D_V$ of $Q=0$, and $N_V^2-4D_V^2=256t^2f(t)$ puts $(t,w)$ on the genus-2 curve $\mathcal C: w^2=f(t)=t^5+21t^4+26t^3+10t^2+5t+1$.
5. Since $s$ is a square and $N_U+2D_U=4(t+1)^5$, the cross identity $N_U(t)=U\,D_U(t)$ makes $t(t+1)(t^2+6t+1)$ a square; since $r$ is a signed square, $t=\varepsilon v^2$.
6. $\varepsilon=+1$: $v$ is a rational point on $\mathcal D_+: (u^2+1)(u^4+6u^2+1)=\square$; clearing denominators, $(m+n)^4+(m-n)^4\in\{2\square,\square\}$ by parity, excluded by `fourth_add_fourth_eq_two_square` (via the self-proved $a^4-b^4\ne c^2$) and Mathlib `not_fermat_42`, leaving $v\in\{0,\pm1\}$.
7. $\varepsilon=-1$: $v$ lies simultaneously on $\mathcal D_-: (u^2-1)(u^4-6u^2+1)=\square$ and on $f(-u^2)=(1-u^2)(u^8-20u^6+6u^4-4u^2+1)=\square$; a mod-3 computation (`decide`) plus a 3-adic cancellation forces $u^2=1$.
8. The surviving abscissas $t\in\{0,1,-1\}$ are impossible: $t=0,1$ are poles of $U(t)$ ($D_U=0$, $N_U\ne0$), and $t=-1$ forces $s+1/s=-2$, i.e. $s=-1<0$.
9. Hence no rational root exists (`linear_quartic_impossible_sharipov`); the unproved six-point Chabauty classification of $\mathcal C(\mathbb Q)$ (`KnownPoints`, `ClassificationBridge` §3.2) is bypassed entirely.
10. All algebraic steps are `ring`/`field_simp` identities; the only external arithmetic inputs are Mathlib's Pythagorean-triple classification, `Int.sq_of_isCoprime`, `not_fermat_42`, and three `decide` certificates over $\mathbb F_3$.
