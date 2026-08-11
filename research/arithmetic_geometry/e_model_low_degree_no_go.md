# Low-degree transport no-go theorems for `H(q,A)`

Status: **exactly proved, but not a normalization**.

The replay script
`research/arithmetic_geometry/e_model_low_degree_no_go.py` reads the frozen
plane model from `artifacts/genus4_quotient.json` and verifies every
factorization and identity below over `QQ`.  Its frozen output is
`e_model_low_degree_no_go.json`.

These results narrow Priority A.  They do not identify the normalization of
`H=0` with either candidate curve in class `544.c`, and they do not classify
the rational points of `H` or of a square-character cover.

## 1. The suggested shifted-monomial family stops at degree twelve

Write

```text
C = A-c,                  r = (q-q0)C.
```

The coefficient of `q^8` in `H` is

```text
(A-2)^6*(361*A^4 - 5272*A^3 + 16504*A^2 - 19168*A + 7696).
```

The quartic factor is irreducible over `QQ`; its discriminant is

```text
-45088768000000000000.
```

In `C^8 H(q0+r/C,C+c)`, the coefficient of `r^8` at `C=0` is the displayed
leading coefficient evaluated at `A=c`.  Consequently a rational shift can
have a positive common power of `C` only when `c=2`.

Keep `q0` indeterminate and set `c=2`.  Exact coefficient inspection gives

```text
C^8 H(q0+r/C,C+2) = C^6 J_q0(r,C).
```

The common factor is exactly `C^6`.  As a polynomial in `r,C` over
`ZZ[q0]`, every monomial of `J_q0` has total `r,C`-degree at most twelve,
while

```text
coeff_(r^8 C^4)(J_q0) = 361.
```

Thus **every rational specialization of `q0` has total degree exactly
twelve**.  In particular, `q0=0` gives the proposed `r=qC` model with 78
terms, while `q0=-2` gives a sparser 63-term model, but neither is a cubic or
quartic.

Scope: this rules out only the family `C=A-c, r=(q-q0)C`.  A different
nonlinear transformation or a genuine Riemann--Roch construction is not
excluded.

## 2. Rational singularities do not supply a low-degree line pencil

Put

```text
J(r,C) = C^2 H(r/C,C+2),
```

where the right side is understood after exact cancellation and is the
irreducible degree-twelve polynomial above for `q0=0`.

For an affine singularity, its `r`-coordinate must be a common root of the
three resultants obtained from

```text
(J,J_r), (J,J_C), (J_r,J_C)
```

by eliminating `C`.  The exact gcd factors into two linear factors, three
irreducible quadratics, and one irreducible degree-fifteen factor.  The only
rational candidate values are `r=0,-4`.  Taking the scheme gcd in `C` and
checking the tangent cones gives exactly

| point `(r,C)` | multiplicity | tangent cone | line-pencil degree |
|---|---:|---|---:|
| `(0,0)` | 2 | `2^40*(u+2v)^2` | 10 |
| `(-4,-2)` | 3 | `-805306368*v*(u-18v)^2` | 9 |

For the ordinary total-degree projective closure, the degree-twelve form at
infinity is

```text
C^4*(11770112*C^8 + 13505536*C^7*r + 6601472*C^6*r^2
     + 2725632*C^5*r^3 + 1377376*C^4*r^4 + 529088*C^3*r^5
     + 106800*C^2*r^6 + 10384*C*r^7 + 361*r^8).
```

The octic is irreducible.  Hence the only rational point at infinity is
`[r:C:Z]=[1:0:0]`.  It has multiplicity four and irreducible tangent cone

```text
361*c^4 - 2384*c^3*z - 6464*c^2*z^2 - 4864*c*z^3 - 1024*z^4.
```

Projection by lines through it has degree `12-4=8`.  Therefore every line
pencil based at a rational singular point has degree at least eight; none
reveals a degree-two or degree-three map.

Scope: this is a theorem about line pencils through rational singularities,
not about higher-degree adjoint pencils with nonrational or infinitely-near
base conditions.

## 3. The denominator `C=0` hides no rational normalization point

The inverse `q=r/C` is undefined at `C=0`, so this boundary must not simply be
discarded.  Exact specialization gives

```text
J(r,0) = -1024*r^2*S6(r),
```

where

```text
S6(r) = r^6 - 128*r^5 + 1024*r^4 + 327680*r^3
        - 1048576*r^2 - 134217728*r - 1073741824
```

is irreducible over `QQ`.  Its six points are the finite-chart branches with
`A -> 2` and `q -> infinity`.  The other four points above `q=infinity` occur
over `[1:0:0]` and are separated by the irreducible tangent quartic displayed
above.

At `(r,C)=(0,0)`, put `v=A-2` and perform the repeated-edge substitution

```text
q = -2 + v^5*(-1/4096 + v*y).
```

The first nonzero coefficient is

```text
v^12 * 4096*(2^28*y^2 - 147456*y + 19).
```

The inner quadratic has discriminant `5*2^28`.  Its two simple roots account
for the two index-five branches above `q=-2`, and both have residue field
containing `QQ(sqrt(5))`.  Thus neither is rational.  Combining these two
calculations, the `C=0` and projective boundary contains no rational point of
the normalization.

## 4. The function `q` cannot factor through a degree-two quotient

The exact fibre at `q=6` is

```text
H(6,A) = 65536*(7*A-6)
  *(7*A^3 - 114*A^2 + 500*A - 88)
  *(4769*A^6 - 79372*A^5 + 331260*A^4 - 458400*A^3
    + 230640*A^2 - 30912*A + 3136).
```

The cubic and sextic are irreducible over `QQ`.  Therefore the normalization
has exactly one rational point in this fibre,

```text
P = (q,A) = (6,6/7).
```

It is smooth and unramified for `q`, since

```text
H_A(P) = 137438953472000000/823543 != 0.
```

Suppose `q=R(x)` for a degree-two map `x:E -> P^1` defined over `QQ`.  Its
deck involution is defined over `QQ`.  Because `P` is unramified for `q`, it
cannot be fixed by that involution: ramification of `x` would force
ramification of `q`.  The involution would therefore produce a distinct
rational point with the same `q`-value, contradicting the fibre
factorization.  Hence

> **`q` does not factor through any degree-two genus-zero quotient defined
> over `QQ`.**

In particular, an eventual identification with `E1` or `E2` cannot express
`q` solely as a rational function of a degree-two elliptic `x`-coordinate.
This does not rule out a birational transport using both elliptic
coordinates.

## 5. Exact passport of the normalized `q`-map

This last calculation uses the local inertia forms already audited in
`src/geometry_audit.py`: a five-cycle at `s=-1`, a transposition at
`s=0,infinity`, transpositions at the six simple roots of `H6(s)`, and the
fixed-point quotient at `s=1`.  The new certificate independently checks the
induced permutations on the ten two-element subsets.

Writing `U=s+1/s`, reciprocality gives

```text
H6(s)/s^3 = U^3 + 15*U^2 - 1588*U + 3022.
```

Under `U=2*(q+6)/(q-2)`, the three reciprocal collision pairs become the
roots of the irreducible cubic

```text
43*q^3 + 11870*q^2 - 50684*q + 51496.
```

The degree-ten passport is therefore

| branch value | partition |
|---|---|
| `q=-2` | `5^2` |
| `q=2` | `2^3 1^4` |
| `q=infinity` | `1^10` |
| each root of the collision cubic | `2^3 1^4` |

The ramification contribution is

```text
2*(5-1) + 4*3*(2-1) = 20.
```

Riemann--Hurwitz for a degree-ten map to `P^1` gives genus one.  The passport
also shows that this `q`-map is not a three-branch-point/Belyi shortcut.

This passport deduction does not identify the resulting genus-one curve with
either candidate Weierstrass model.
