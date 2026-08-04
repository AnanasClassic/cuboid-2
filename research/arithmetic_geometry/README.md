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

## Coordinate exceptions

- `z=-1` is outside the `T` chart, but has `s=1`, already excluded.
- `T=1` is `z=infinity`, not an affine cuboid parameter.
- `b=-1` is outside the `B,A` chart.  Eliminating `a` at `b=-1` gives
  `(s-1)^4` times a degree-16 polynomial whose coefficients are all strictly
  positive.  Hence for real `s>0` this exception occurs only at `s=1`.
- `Q1=0` is the finite exceptional locus of the displayed birational inverse;
  use the exact gcd in `B` there.

## Current arithmetic status

No Weierstrass normalization, Mordell--Weil rank bound, or complete set of
rational points is claimed here.  The smooth rational point

```text
(q,A) = (6,6/7)
```

lies on the elliptic plane model and has `U=6`; it does not lift to `D4(Q)`
because `U+2=8` is not a rational square.  A search is not a completeness
argument.  The next rigorous step is to normalize `H`, convert it to a
Weierstrass model, compute `E(Q)` with a certified rank bound, and solve the
square-value condition by descent or elliptic Chabauty.
