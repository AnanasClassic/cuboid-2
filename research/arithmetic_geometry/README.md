# Reciprocal quotient of the square-parameter pullback

This directory contains an exact construction of the most useful low-genus
quotient currently known for the quadratic--cubic obstruction.

Run

```bash
.venv/bin/python research/arithmetic_geometry/derive_genus4_quotient.py
```

The script regenerates `artifacts/genus4_quotient.json` using exact rational
polynomial arithmetic.  The JSON file contains sparse coefficients for every
model and for the generic inverse map.

## Starting curve and involution

Let `D(x)=x^2+a*x+b`.  The exact remainder conditions are

```text
R1(s,a,b) = 0,
R0(s,a,b) = 0.
```

The identity

```text
P_s(x) = -s^5*x^5*P_{1/s}(1/x)
```

induces

```text
tau(s,a,b) = (1/s, a/b, 1/b).
```

After `s=z^2`, use the lift

```text
tau_+(z,a,b) = (1/z, a/b, 1/b).
```

Put

```text
T = (z-1)/(z+1),
B = (b-1)/(b+1),
A = 2*a/(b+1).
```

Then `tau_+(T,B,A)=(-T,-B,A)`.  In particular,

```text
X = T^2
```

is an invariant.

## Exact genus-four model

Substitution in `R1,R0`, clearing only the displayed coordinate
denominators, and eliminating `B` gives

```text
Res_B(H1,H0) = 2^14*(T-1)^40*T^4*A^6*G(T^2,A).
```

The desired factor `G(X,A)` is irreducible over `Q`, has bidegree `(16,10)`,
and has 187 nonzero terms.  Its coefficients are stored in the artifact.
The normalization of `G=0` is the genus-four quotient

```text
D4 = C_sq/<tau_+>.
```

The forward map is

```text
X = ((z-1)/(z+1))^2,
A = 2*a/(b+1).
```

For a generic point of `G=0`, choose `T` with `T^2=X`.  The penultimate
subresultant is linear:

```text
Q1(T,A)*B + Q0(T,A).
```

Thus the generic inverse is

```text
B = -Q0/Q1,
z = (1+T)/(1-T),
b = (1+B)/(1-B),
a = A/(1-B).
```

Both choices of `T` produce the same `tau_+` orbit.  The exact sparse
polynomials `Q0,Q1` are included in the artifact.

This is a birational inverse, not a claim that the displayed singular plane
model is smooth.  At a zero of `Q1`, recover the fiber by computing
`gcd_B(H1,H0)` directly.  A complete rational-point computation must retain
these exceptional normalization branches.

## Bielliptic structure

The model is palindromic:

```text
G(X,A) = X^16*G(1/X,A).
```

The residual involution is `X -> 1/X`.  Set

```text
q = X + 1/X.
```

There is an exact irreducible polynomial `H(q,A)` of bidegree `(8,10)` and
99 terms such that

```text
G(X,A) = X^8*H(X+1/X,A).
```

The normalization of `H=0` is the reciprocal elliptic quotient `E`.  Hence
`D4` is bielliptic and

```text
Jac(D4)  ~  E x Prym(D4/E)
```

over `Q`, up to isogeny; the Prym factor has dimension three.

For

```text
U = s + 1/s,
v = z + 1/z,
```

the maps are

```text
U = 2*(q+6)/(q-2),
v^2 = U+2 = 4*(q+2)/(q-2).
```

Thus determining `D4(Q)` is exactly a square-value problem for the rational
function `U+2` on `E`, including the points above its zeros and poles.

The two special fibers are

```text
H(-2,A) = 2^16*(A-2)^10,
H( 2,A) = 2^27*A^3*(A-6)*(A^2-12*A+4)^3.
```

On the normalization, `U+2` has odd order at two points above `q=-2` and
four points above `q=2`.  Therefore the double cover has six branch points,
and Riemann--Hurwitz gives genus four.

## Character/Kummer ramification obstruction

The exact odd-divisor audit for the literal basis

```text
q+2, q-2, epsilon*V
```

has nonzero branch degrees `6,14,8,12,10,6,8` for its seven nontrivial
characters.  Thus no nontrivial product is an unramified square class.  This
is a theorem on the normalization of `H` and does not assume the open
transport to the candidate elliptic curve.

The negative-b character table uses the chosen basis
`(q+2,q-2,2-W)`.  Its exact relation to the physical basis is

```text
[-V] = [q+2] + [2-W].
```

Thus the full cover is unchanged, but literal `-V` is character `101`, not
`001`, in the chosen negative table.  The proof, including the invariant
square root and the conditional obstruction to identifying a character with
the unramified `E1` 2-isogeny Kummer class, is in
`notes/reciprocal_signed_square_covers.md`.  It is reproduced by
`character_kummer_obstruction.py`.

## Coordinate exceptions

- `z=-1` is outside the `T` chart, but has `s=1`, already excluded.
- `T=1` is `z=infinity`, not an affine cuboid parameter.
- `b=-1` is outside the `B,A` chart.  Eliminating `a` at `b=-1` gives
  `(s-1)^4` times a degree-16 polynomial whose coefficients are all strictly
  positive.  Hence for real `s>0` this exception occurs only at `s=1`.
- `Q1=0` is the finite exceptional locus of the displayed birational inverse;
  use the exact gcd in `B` there.

## Low-degree transport no-gos

The exact certificate `e_model_low_degree_no_go.py` proves that the proposed
family `C=A-c, r=(q-q0)C` cannot directly expose a cubic or quartic: only
`c=2` has a common `C`-factor, and the primitive equation has total degree
12 for every rational `q0`.  Its rational-singularity line pencils have
degree at least 8.  Independently, the unique unramified rational point above
`q=6` proves that `q` cannot factor through any rationally defined
degree-2 quotient.  The note `e_model_low_degree_no_go.md` also records the
complete rational boundary audit and exact degree-10 `q`-passport.

These are scoped no-go theorems, not a normalization or an obstruction to a
birational map using both elliptic coordinates.

## Current arithmetic status

The direct normalization of the displayed `H(q,A)=0` model remains open in
the narrow sense of C025.  It is no longer a blocker.  Starting instead from
the lossless compact signed-square locus C035 gives a smaller simultaneous
reciprocal quotient `C8(U,V)=0`.  The exact certificates

```text
../compact_signed_square/reciprocal_quotient/derive.py
low_degree_transport.py
```

identify its admissible normalization birationally with

```text
E1: y^2=x^3-5*x+4.
```

Both physical signs reach the same `C8`, and their common required square
characters are `UV` and `1-UV`.  The transport includes both rational maps,
their exact function-field identities, and a complete classification of
every rational denominator or projective exception.

After translation by the 2-torsion point, `product_character_simplification.py`
proves the scalar-sensitive identity

```text
1-UV = 2*(X+1)*L*M*g^2.
```

The valuation theorem in `product_squareclass_valuation.py` reduces every
nonexceptional simultaneous square point to a point with square abscissa on

```text
R^2=4*a^5-8*a^2+5*a.
```

The exact 2-descent, index-independent `7/23` Mordell--Weil sieve, and `p=7`
formal-log certificate prove that the only square-abscissa points are
`infinity`, `(0,0)`, and `(1,+/-1)`.  The lift table makes all four
inadmissible.  Therefore the `2+3` locus is empty and C010 is proved.  See
`product_genus2_square_abscissa.md` and
`../../notes/quadratic_cubic_completion.md` for the complete argument.
