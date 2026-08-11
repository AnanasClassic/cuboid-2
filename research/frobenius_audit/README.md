# Independent Frobenius/Burnside audit

This directory gives an exact good-prime Frobenius fingerprint for the
reciprocal quotient $E=C/\langle\tau\rangle$.  Here $C$ is the
normalization of the degree-ten two-root cover and

$$
 \tau(s,\{r_1,r_2\})=(s^{-1},\{r_1^{-1},r_2^{-1}\}).
$$

It is a point-counting certificate, not an identification of $E$ with a
particular Weierstrass model.  In particular, matching these traces against a
database would not by itself prove an isomorphism or an isogeny, and the data
make no assertion about the Mordell--Weil rank.

## Why the count is exact

For a smooth curve with an involution in odd characteristic, a
Frobenius-stable orbit count gives

$$
 \#E(\mathbf F_p)=\frac{\#\operatorname{Fix}(F\mid C)
 +\#\operatorname{Fix}(F\tau\mid C)}2.
$$

For a generic rational value of $s$, a point of $C(\mathbf F_p)$ is a
Frobenius-stable two-subset of the roots of $P_s$.  If $n_1$ roots lie in
$\mathbf F_p$ and $n_2$ irreducible quadratic factors occur, the number is
$\binom{n_1}{2}+n_2$.  The production count obtains root counts exactly as
degrees of polynomial gcds with $X^p-X$ and $X^{p^2}-X$.  It independently
checks every generic rational fibre using factor degrees in SymPy.

For $F\tau$, the base condition is $s^{p+1}=1$.  Its action on roots is

$$
 g(r)=1/r^p.
$$

Every fixed two-subset consists either of two fixed roots or one two-cycle of
$g$.  Fixed roots are counted by the degree of the gcd with $X^{p+1}-1$.
At the small primes the script also checks the formula by direct enumeration
of every root and every two-subset in $\mathbf F_{p^2}$.

The normalization fibres omitted by the generic formula are treated as
follows.

| Fibre | Normalization calculation |
|---|---|
| $s=0,\infty$ | Root valuations $0,0,1,2,2$, with inertia swapping the last two roots.  The fibre has 7 rational points if 32 is a square, and 3 otherwise. |
| $s=1$ | One rational branch near $+1$; the four branches near $-1$ are controlled by $c^4-8c^2-12c-4$. |
| $s=-1$ | A 5-cycle has two orbits on two-subsets.  Frobenius fixes both for $p\equiv\pm1\pmod5$, and exchanges them otherwise. |
| $H_6(s)=0$ | A transposition collision gives one point from the double pair, three mixed inertia orbits, and the two-subsets of the remaining cubic. |

The same inertia-orbit calculation is used in the $F\tau$ count.  At a root
of $H_6$ in the norm-one torus, the unique double root is checked directly
to be fixed by $g$.

## Good primes

The discriminants and collision values used by the script are

$$
\begin{aligned}
\operatorname{disc}(H_6)&=-120976582094426834375000000,\\
\operatorname{disc}(c^4-8c^2-12c-4)&=-11008,\\
H_6(1)&=-86,\qquad H_6(-1)=-6250.
\end{aligned}
$$

For a conservative good-reduction certificate, the script also inverts 120,
the order of $S_5$: the splitting-field group of a quintic is a subgroup of
$S_5$.  The resulting excluded set is

$$
 \{2,3,5,17,43,47\}.
$$

This is a sufficient excluded set, not a claim that every listed prime is a
prime of actual bad reduction.  In particular, this audit deliberately makes
no good-reduction claim at 3.  Outside this set the branch sections
$0,\infty,\pm1$ and the six roots of
$H_6$ remain disjoint and separable.  The local forms used in the repository
are tame: a transposition at a simple $H_6$-root, the valuation pattern at
zero (and reciprocally infinity), four distinct slopes at $s=1$, and
$y^5+64(s+1)$ at $s=-1$.  Thus the normalized cover and its odd-characteristic
involution quotient have smooth reduction at the primes counted here.

## Reproduction

From the repository root:

```bash
SYMPY_GROUND_TYPES=python .venv/bin/python \
  research/frobenius_audit/frobenius_burnside.py
SYMPY_GROUND_TYPES=python .venv/bin/python -m pytest -q \
  tests/test_frobenius_audit.py
```

The first command recreates `frobenius_fingerprint.json`, including the full
fibre-by-fibre breakdown and a SHA-256 digest of the canonical payload.

For the nineteen certified good primes at most 97 the traces are

```text
p   :  7, 11, 13, 19, 23, 29, 31, 37, 41, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97
a_p : -2, -4,  2, -4, -6,  8,  2,  4, -2, -6, -4,  4, -4,  6, -6, 10, 12,-10,-10
```

## Exact offline check of the 544.c candidate

The fingerprint matches, at every certified prime above, both

$$
E_1:y^2=x^3-5x+4,
\qquad
E_2:v^2=u^3+5u+18.
$$

The check is a direct Legendre-symbol point count on each model, not a database
query.  After the shifts $X=x-1$ and $U=u+2$, the models become

$$
Y^2=X^3+3X^2-2X,
\qquad
V^2=U^3-6U^2+17U.
$$

An exact rational 2-isogeny and its dual are

$$
\phi(X,Y)=\left(\frac{Y^2}{X^2},
 \frac{Y(-2-X^2)}{X^2}\right),
$$

$$
\widehat\phi(U,V)=\left(\frac{V^2}{4U^2},
 \frac{V(17-U^2)}{8U^2}\right).
$$

Symbolic reduction modulo the two curve equations verifies both maps and the
identities $\widehat\phi\phi=[2]$ and $\phi\widehat\phi=[2]$.  It also checks
$\phi(0,2)=(2,-6)$ in the unshifted short coordinates.

This establishes that the two displayed candidate models are 2-isogenous and
share the certified fingerprint.  It does **not** identify the abstract
reciprocal quotient with class 544.c.  The rank-one value and any generators
reported by LMFDB are external candidate metadata only; they cannot be used
for the quotient until an exact birational map or another identification proof
is supplied.

Reproduce this separate certificate with:

```bash
SYMPY_GROUND_TYPES=python .venv/bin/python \
  research/frobenius_audit/candidate_544c_check.py
```
