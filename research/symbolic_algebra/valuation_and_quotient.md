# Valuation theorem and explicit reciprocal quotient

This note records two exact restrictions on a hypothetical quadratic factor.
They do not by themselves finish the second cuboid conjecture, but they replace
the raw genus-17 square pullback by explicit lower-dimensional covers and add
global arithmetic information not visible in the plane obstruction alone.

## 1. The constant coefficient is a signed square

Put `X=t^2` and write the monic integral quintic

\[
H_{p,q}(X)=Q_{p,q}(t).
\]

If the normalized quintic has a rational quadratic divisor, Gauss's lemma and
the scaling `X=q^4x` give an integral factorization

\[
H_{p,q}(X)=(X^2+AX+B)(X^3+CX^2+DX+E),
\qquad BE=-p^{10}q^{10}.
\]

Fix a prime `ell | pq`, and put `m=v_ell(pq)`.  Coprimality means that exactly
one of `p,q` has valuation `m`.  For the coefficients `h_i` of `X^i`, the lower
Newton polygon has vertices

\[
(0,10m),\quad(2,2m),\quad(3,0),\quad(5,0).
\]

Indeed `v(h_0)=10m`, `v(h_2)=2m`, `v(h_3)=v(h_5)=0`, while the points for
`h_1,h_4` lie on or above the displayed lower hull.  This remains true at 2
and at 3; the exceptional extra divisibility only moves a non-vertex upward.
The root-valuation multiset in an algebraic closure is therefore

\[
\{4m,4m,2m,0,0\}.
\]

The roots of the quadratic factor form a two-element submultiset, hence

\[
v_\ell(B)\in\{0,2m,4m,6m,8m\}.
\]

Every value is even.  Since `B | p^10 q^10`, no other prime divides `B`, and
therefore

\[
\boxed{B=\varepsilon d^2,\qquad \varepsilon\in\{+1,-1\}.}
\]

In normalized coordinates `b=B/q^8`, so `b` is likewise a signed rational
square.

### A refinement when 2 is a nonsquare

Let `ell` be odd, divide `p`, and satisfy `(2/ell)=-1`.  The residual polynomial
of the slope-zero length-two face is

\[
Y^2+6q^4Y+q^8,
\]

whose discriminant is `32q^8`, a nonsquare.  The two unit roots consequently
form an irreducible quadratic local factor.  A global quadratic factor either
is this factor or uses two roots of positive valuation.  Thus

\[
v_\ell(B)/v_\ell(p)\in\{0,6,8\}.
\]

If instead `ell | q`, apply the exact reciprocal transformation to the swapped
polynomial.  Its quadratic constant is `B'=p^8q^8/B`, giving

\[
v_\ell(B)/v_\ell(q)\in\{0,2,8\}.
\]

These restrictions hold for every odd prime `ell=3 or 5 mod 8` in the indicated
part of the primitive pair.

## 2. A clean reciprocal invariant

The exact reciprocal identity induces

\[
(s,a,b)\longmapsto(1/s,a/b,1/b)
\]

on quadratic factors.  Two particularly simple invariants are

\[
U=s+1/s,\qquad V=a^2/b.
\]

For `a,V != 0`, substitute `b=a^2/V` directly into `R_1=R_0=0`, multiply each
equation by `V^2`, and call the resulting polynomials `g_1,g_0`.  Exact
elimination gives

\[
\operatorname{Res}_a(g_1,g_0)
=s^{20}V^8G(s+1/s,V),
\]

where `G(U,V)` is irreducible over `Q`, has bidegree `(12,10)`, total degree
14, and 97 nonzero terms.  The script exports all coefficients in canonical
machine-readable form.  This is an explicit singular plane model of the
reciprocal quotient whose normalization has genus one in the independent
ramification calculation.

The exceptional value `V=0` means `a=0` and must not be inferred from the
cleared resultant.  Direct substitution gives

\[
F(s,0)=4s^4(s-1)^4
(s^4+12s^3+26s^2+12s+1)
(3s^4-36s^3-82s^2-36s+3).
\]

The first quartic is positive for `s>0`; the second has no rational root by the
rational-root theorem.  Thus `a=0` has no admissible rational parameter.

## 3. Square-parameter conditions on the quotient

For an admissible parameter `s=z^2`,

\[
U+2=(z+z^{-1})^2,\qquad U-2=(z-z^{-1})^2.
\]

The signed-square theorem for `b` gives

\[
V=a^2/b=\varepsilon y^2
\]

for a nonzero rational `y` and `epsilon in {+1,-1}`.  Hence every genuine
quadratic factor maps to a rational point of `G=0` satisfying all three square
conditions

\[
U-2=Y_-^2,\qquad U+2=Y_+^2,\qquad V=\pm Y_V^2.
\]

This is a concrete reduction to two explicit covering problems over the
genus-one quotient.  It is only a necessary obstruction: a rational point on
`G` need not lift to rational `s,a,b`.  Therefore quotient points cannot be
reported as counterexamples without reconstructing and checking the factor.

Reproduce the exact quotient with

```bash
python research/symbolic_algebra/reciprocal_square_quotient.py \
  --output /tmp/reciprocal-square-quotient.json
```
