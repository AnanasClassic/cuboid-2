# Independent symbolic-algebra workstream

## Exact quadratic-factor reduction

Write

\[
P_s(x)=x^5+c_4x^4+c_3x^3+c_2x^2+c_1x+c_0
\]

and let `D=x^2+a*x+b`.  Reduction by `D` uses

\[
\begin{aligned}
x^2&=-ax-b,\\
x^3&=(a^2-b)x+ab,\\
x^4&=(-a^3+2ab)x+(-a^2b+b^2),\\
x^5&=(a^4-3a^2b+b^2)x+(a^3b-2ab^2).
\end{aligned}
\]

Consequently the remainder is `R1*x+R0`, with both `R1` and `R0`
quadratic in `b`.  The exact combination

\[
E=R_0-(c_4-2a)R_1=Lb+C
\]

is linear.  If `L != 0`, the equations are equivalent to

\[
b=-C/L,\qquad
F(s,a):=C^2-U_1CL+U_0L^2=0,
\]

where `R1=b^2+U1*b+U0`.  This is a two-way equivalence: from `F=0`
and `L != 0`, substitution gives `R1=F/L^2=0`, while `E=0` gives
`R0=0`.  Thus the obstruction curve is not being used as a one-way
resultant.

The forbidden division locus is completely controlled over `Q`.  Exact
elimination gives

\[
\operatorname{Res}_a(C,L)
=64(s-1)^3(s+1)^3H(s),
\]

where `deg(H)=21`.  The leading coefficient of `H` is nonzero modulo 13,
and the exact list of `H(0),...,H(12) mod 13` is

```
1, 1, 11, 11, 7, 8, 8, 4, 4, 6, 8, 12, 1.
```

Therefore `H` has no rational root, including roots whose reduced
denominator is divisible by 13 (homogenize and use the nonzero leading
coefficient).  At `s=1` the gcd in `Q[a]` is `a-2`; at `s=-1` it is
`(a-2)^3`; in both fibres `R1(\pm1,2,b)=(b-1)^2`.  Hence the entire
rational degenerate locus is

\[
(s,a,b)=(1,2,1),\ (-1,2,1).
\]

Neither point is admissible for the second cuboid conjecture: `s=1` means
`p=q`, and `s=-1` is not a positive rational square.  Thus for every
admissible parameter, quadratic divisibility is exactly equivalent to
`F(s,a)=0`, `b=-C/L`.

Run the derivation and export the 106-term obstruction polynomial in canonical
coefficient-record form with:

```bash
python research/symbolic_algebra/derive_quadratic_reduction.py \
  --output /tmp/quadratic-reduction.json
```

The script requires SymPy and asserts every displayed identity.

## Seven-prime theorem

The independent normalized-model checker reproduces residual projective-class
counts

| prime | 41 | 61 | 71 | 73 | 83 | 89 | 97 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| residual classes | 22 | 34 | 28 | 38 | 40 | 50 | 42 |

For a primitive integer pair `(p,q)`, every reduction is a point of
`P^1(F_ell)`.  If the reduced quintic has no monic quadratic divisor for at
least one listed prime, the characteristic-zero monic quintic cannot have a
monic quadratic factor.  CRT equidistribution on primitive pairs makes the
residual density the product of the seven local fractions.  Hence the exact
excluded density is

\[
1-\prod_\ell\frac{B_\ell}{\ell+1}
=\frac{13,568,504}{13,657,329}
\approx 99.3496166051\%.
\]

This is an unconditional theorem about the union of explicit congruence
families, not a proof of the conjecture.  Its complement has positive density
`88,825/13,657,329` and contains infinitely many residue classes.

A strictly stronger, still fast certificate uses every prime at most 97.  The
exact residual and excluded densities are respectively

\[
\frac{113,135}{5,689,253,052},\qquad
\frac{5,689,139,917}{5,689,253,052}
  \approx 99.9980114261\%.
\]

The homogeneous implementation reproduces this stronger theorem in about five
seconds on the reference environment:

```bash
python src/modular_sieve.py --scan-through 97 --output /tmp/modular-97.json
```

Primes 2, 3, 5, and 7 have no obstructed projective classes and therefore do
not change this product, but retaining them makes the scan boundary literal.

Run the independent check with:

```bash
python research/symbolic_algebra/independent_sieve_check.py
```
