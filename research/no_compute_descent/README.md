# Fifth-power norm descent without large computation

This directory records a new exact necessary condition for the sole remaining
quadratic--cubic (`2+3`) factorization mechanism.  It uses only a translated
Newton polygon, the Eisenstein--Dumas criterion, unique factorization in
`Z[i]`, and the factorization of a binomial over a finite field.

It is a genuine infinite-family restriction.  It does **not**, by itself,
finish the conjecture: primitive solutions of `p^2+q^2=r^5` exist.

## 1. A single Newton edge above `s=-1`

Put `s=-1+d` and `x=-1+y`.  Exact expansion gives

```text
P_{-1+d}(-1+y) =
    y^5
  + d*(3-2*d)*y^4
  + d*(-56+60*d-18*d^2+d^3)*y^3
  + d*(144-192*d+80*d^2-8*d^3-d^4)*y^2
  - 4*d*(40-68*d+42*d^2-11*d^3+d^4)*y
  + 4*d*(d-2)^4.
```

Let `ell` be an odd prime dividing `p^2+q^2`, and put

```text
d = s+1 = (p^2+q^2)/q^2,
k = v_ell(d) = v_ell(p^2+q^2).
```

Coprimality gives `ell not dividing q`.  The constant coefficient has exact
valuation `k`, because `d-2` is an `ell`-adic unit; every intermediate
coefficient has valuation at least `k`; and the leading coefficient is one.
Consequently the lower Newton polygon is the single segment

```text
(0,k) ---- (5,0).
```

If `gcd(k,5)=1`, the Eisenstein--Dumas criterion makes the translated quintic
irreducible over `Q_ell`.  A rational quadratic factor is therefore possible
only if

```text
5 | v_ell(p^2+q^2)
```

for every odd `ell | p^2+q^2`.

Since `p,q` are coprime, the two-adic valuation of their sum of squares is
zero when they have opposite parity and one when they are both odd.  Hence any
counterexample to the quadratic-factor assertion must satisfy

```text
p^2+q^2 = r^5       if p,q have opposite parity,
p^2+q^2 = 2*r^5     if p,q are both odd,
```

for an integer `r>0`.

## 2. The residual degree-two obstruction

Write `v_ell(r)=m`, so `k=5m`, and replace `y` by `ell^m Y`.  After division by
`ell^(5m)`, all non-endpoint terms vanish modulo `ell`; the residual polynomial
is

```text
Y^5 + 64*u,
u = ((s+1)/ell^(5m)) mod ell.
```

A degree-two factor over `Q_ell` yields, after the same integral scaling, a
monic degree-two divisor of this residual binomial.

The primitive equations above are completely parametrized in the Gaussian
integers.  There are coprime `a,b` and a Gaussian unit `eta` such that

```text
p+i*q = eta*(a+i*b)^5
```

in the opposite-parity case, while in the odd--odd case

```text
p+i*q = (1+i)*eta*(a+i*b)^5.
```

Fix an embedding `i -> i_ell` corresponding to the Gaussian prime above
`ell` which divides `a+i*b`.  If `alpha=a+i_ell*b`, `kappa` is the displayed
unit factor, and a bar denotes the other split embedding, then

```text
u = -4 * (kappa/bar(kappa)) * fifth_power    in F_ell^*.
```

For a Gaussian unit, and also after multiplication by `1+i`, the quotient
`kappa/bar(kappa)` is itself a fifth power: it belongs to
`{+1,-1,+i_ell,-i_ell}`, and each of these elements is its own fifth power.
Thus

```text
u belongs to -4*(F_ell^*)^5,
Y^5+64*u is fifth-power equivalent to Z^5-256.
```

## 3. Exact splitting restriction on every prime divisor of `r`

For `ell != 5`, the binomial `Z^5-256` has a degree-two divisor over
`F_ell` only in the following cases.

- `ell = -1 (mod 5)`: its factor degrees are `1+2+2`.
- `ell = 1 (mod 5)` and `256` is a fifth power: it splits completely.

For `ell = 2` or `3 (mod 5)`, its factor degrees are `1+4`, so no monic
quadratic divisor exists.  When `ell = 1 (mod 5)`, `256=2^8` is a fifth power
if and only if `2` is a fifth power.

Every odd prime divisor of a primitive sum of two squares is either `5` or is
`1 (mod 4)`.  Therefore every odd prime `ell != 5` dividing `r` in a
hypothetical counterexample must satisfy exactly one of

```text
ell = 9 (mod 20),
ell = 1 (mod 20) and 2^((ell-1)/5) = 1 (mod ell).
```

This removes all prime divisors `ell = 13,17 (mod 20)` and most primes
`ell = 1 (mod 20)` from the fifth-power norm.

## Logical boundary

This theorem is stronger than a fixed congruence sieve because the prime
`ell` is allowed to depend on `(p,q)`.  Nevertheless it is still a necessary
condition rather than a contradiction.  For example,

```text
38^2 + 41^2 = 5^5.
```

The next no-large-compute target is to combine the Gaussian fifth-power
parametrization with the signed-square factor constant and the local Newton
pair types at primes dividing `p*q`.  A successful route would show that the
allowed splitting conditions above cannot coexist with a global quadratic
factor, yielding an infinite descent.  The alternative finishing route is the
already staged exact transport to the rank-one elliptic quotient followed by
the four-branch Mordell--Weil character sieve.

## Reproduction

```bash
python3 research/no_compute_descent/fifth_power_sum_descent.py
```
