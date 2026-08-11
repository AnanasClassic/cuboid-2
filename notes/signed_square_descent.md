# Signed-square descent for the quadratic factor

Let `H_{p,q}(X)=Q_{p,q}(t)` with `X=t^2`.  A rational quadratic
factor gives, by Gauss's lemma, an integral monic factor

```text
X^2 + A*X + B.
```

## Newton-polygon theorem

Fix a prime `ell | p*q` and put `k=v_ell(p*q)`.  Coprimality means
that exactly one of `p,q` has valuation `k`.  From the constant
coefficient upward, the coefficient valuations of `H` have lower hull

```text
(0,10k), (2,2k), (3,0), (5,0).
```

At `ell=2,3` additional divisibility can only move the non-vertex
coefficients at degrees one or four upward, so the hull is unchanged.
The five root valuations are therefore

```text
4k, 4k, 2k, 0, 0.
```

The valuation of `B`, the product of two roots, belongs to

```text
{0,2k,4k,6k,8k}.
```

Every prime divisor of `B` divides `p*q`, because `B` divides the
constant `-p^10*q^10`.  Every valuation of `B` is even, proving

\[
B=\varepsilon d^2,\qquad \varepsilon\in\{+1,-1\}.
\]

Thus the normalized constant `b=B/q^8` is also a signed rational
square.  The sign is a single global choice and cannot vary between
reduction primes.

For an odd prime `ell` with `(2/ell)=-1`, the slope-zero residual
quadratic is irreducible.  This further gives

```text
ell | p: v_ell(B)/v_ell(p) in {0,6,8},
ell | q: v_ell(B)/v_ell(q) in {0,2,8}.
```

## Sign-consistent finite-field theorem

For each odd prime, the exact certificate separates projective
parameter classes supporting a quadratic divisor whose constant is a
square from those supporting one whose constant is a negative square.
CRT is applied separately to the two fixed signs, followed by
inclusion--exclusion.  For every odd prime at most 137, the residual
density is

\[
\frac{13169}{3917894203948032}
=3.3612444120\ldots\,10^{-12}.
\]

Consequently a union of explicit congruence families of density

\[
\frac{3917894203934863}{3917894203948032}
=99.9999999996639\ldots\% 
\]

has no rational quadratic factor.  This is an unconditional theorem,
not a completeness result for the residual family.

## Exact limitation of every finite congruence sieve

No finite set of reduction primes can prove the full conjecture.  If
`M` is their product, take `p` divisible by `M` and `q=1`.  At every
selected prime,

```text
H_{p,q}(X) = X^3*(X^2+6*X+1)  (mod ell),
```

so `X^2` is a monic quadratic divisor with constant zero, compatible
with both signs.  Infinitely many primitive pairs have this residue
pattern.  Therefore the remaining proof must use global arithmetic
geometry or valuations at primes depending on `p,q`, rather than a
larger fixed modular sieve.
