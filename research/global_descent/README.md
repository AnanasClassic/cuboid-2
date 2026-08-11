# Global descent: exact infinite families

This directory contains an exact unconditional exclusion of the remaining
quadratic--cubic split for a new infinite family.

It now also contains a complete two-inert-prime-power theorem.  If

\[
p=L^m,\qquad q=R^n,
\]

where \(L,R\) are distinct odd primes and \(2\) is a quadratic nonresidue at
both, then \(P_{(p/q)^2}\) has no rational quadratic factor.  The first
endpoint congruences alone do not prove this: they have infinite formal
survivors.  `second_endpoint_layer.py` uses the next coefficient layer and
strictly positive expansions of the full projection to close every one of
those survivor branches.  The proof is in `second_endpoint_layer.md`.

## Theorem

Let \(\ell\) be any prime and let \(k\geq1\).
If

\[
   (p,q)=(\ell^k,1)\quad\text{or}\quad(1,\ell^k),
\]

then the normalized quintic \(P_{(p/q)^2}(x)\) has no rational quadratic
factor.

This is an infinite-family theorem, not a bounded search.

More generally, at every prime \(r\mid pq\) a hypothetical factor determines
an index

\[
 v_r(b)=m_r v_r(s),\qquad m_r\in\{0,1,2,3,4\}.
\]

The same resultant calculation proves that the indices cannot be constant
over all primes dividing \(pq\).  Thus any counterexample must have at least
two distinct prime divisors in \(pq\), and must use different local Newton
pair types at two of them.

## Proof

Write a hypothetical monic quadratic divisor as

\[
 D(x)=x^2+a x+b.
\]

In the integral polynomial in \(X=t^2\), write its constant as \(B\).
The exact Newton polygon at \(\ell\) gives the multiset of root valuations

\[
\{0,0,2k,4k,4k\}.
\]

The valuation of the product of any two roots is consequently in
\(\{0,2k,4k,6k,8k\}\).  This deliberately does not use residual
irreducibility, so it includes \(\ell=2\) and primes for which 2 is a square.

Every prime divisor of \(B\) divides \(pq\), and every valuation is even;
thus its sign is the only remaining square class.  Since one of \(p,q\) is
1 and the other is \(\ell^k\), after the normalization \(b=B/q^8\) the two
orientations both give exactly

\[
 b\in\{\pm s^m:0\leq m\leq4\}.
\]

The identical conclusion holds whenever the local indices \(m_r\) are all
the same: equality of every finite valuation gives \(b=\pm s^m\).  Therefore
the computation below also proves the stronger nonuniformity obstruction.

For each choice, divide \(P_s(x)\) by \(D(x)\):

\[
 P_s(x)\bmod D(x)=R_1(s,a,b)x+R_0(s,a,b).
\]

A genuine divisor requires both remainders to vanish and therefore

\[
 \operatorname{Res}_a(R_1(s,a,b),R_0(s,a,b))=0.
\]

`inert_prime_power_family.py` constructs the remainders directly from
\(P_s\), computes and completely factors all ten resultants over
\(\mathbb Q\).  In every branch the only positive rational root is \(s=1\).
This conclusion is exact and does not require trusting an irreducibility
flag: every displayed nonlinear factor is monic with constant term
\(\pm1\), so the rational-root theorem leaves only \(\pm1\), and direct
substitution excludes both.  No numerical root search is used.  But the
displayed family has \(s=\ell^{\pm2k}\ne1\), a contradiction.

The argument only uses the resultant in the necessary direction, so no
reverse-lifting or saturation assumption is hidden in the proof.

## Reproduction

```bash
.venv/bin/python research/global_descent/inert_prime_power_family.py
.venv/bin/python research/global_descent/second_endpoint_layer.py
```

The generated JSON records every exact factor and a checksum.
