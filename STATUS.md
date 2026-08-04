# Status

Date: 2026-08-04

## Bottom line

Sharipov's second cuboid conjecture is **OPEN**.  No counterexample was found,
and no complete determination of the relevant rational points on the `2+3`
curve is presently available.

## Proved or machine-verified here

- Exact weighted normalization and reciprocal identity.
- Complete `1+4` / `2+3` / symmetric `5+5` factorization classification via
  Gauss's lemma and Capell's theorem.
- Exact remainder equations `R1=R0=0`, the identity `b=C/L`, the obstruction
  polynomial `F(s,a)`, and the reverse lift when `L != 0`.
- Complete rational degenerate locus `L=C=0`: `(s,a)=(1,2),(-1,2)`.
- Exact replay of the arXiv:2601.04240 `5+5` discriminant and Sturm script.
- Signed-square descent: the constant of every hypothetical integral
  quadratic factor is `B=+d^2` or `B=-d^2`.
- Sign-consistent finite-prime theorem excluding `2+3` for density
  `3917894203934863/3917894203948032` of primitive pairs, leaving exact
  residual density `13169/3917894203948032`.
- Exact genus-four quotient plane equation, generic subresultant lift, and
  bielliptic plane equation `G(X,A)=X^8 H(X+1/X,A)`.
- Exact singularity, special-fiber, and discriminant diagnostics for `H`.  In
  particular, the squarefree discriminant quartic is rigorously shown not to
  be the reciprocal elliptic quotient with the `q`-map preserved.

## Conditional or externally dependent

- The algebraic part of arXiv:2601.04241 (`1+4`) is independently verified.
  Its list of rational points on a genus-2 curve depends on a Magma transcript
  (`RankBound=1`, infinite Jacobian point, `Chabauty`).  The Magma run was not
  available locally, so the final exclusion is labelled CONDITIONALLY VERIFIED.
- Exact local Newton and Riemann--Hurwitz calculations recover genus 7 for the
  two-root curve and genus 17 for the square pullback.  The fixed-point counts
  giving reciprocal quotient genera 1, 4, and 8 have not been checked in a
  second geometry system; no complete rational-point computation follows.
- The normalization/branch interpretation of the new singular quotient models
  still depends on that local quotient audit.  The polynomial identities and
  generic maps are machine-verified; a Weierstrass model and rank bound are not.

## Computational evidence only

- arXiv:2601.07899v2 searches the projective obstruction curve through height
  `10^9` and finds eight points, none admissible.  Version 1 used `10^7`.
  Neither bound proves completeness.

## Exact remaining obstruction

Determine all rational points on `F(s,a)=0` that satisfy

```text
s = z^2 > 0, z in Q, z != 1, L(s,a) != 0,
b = C(s,a)/L(s,a), and R1(s,a,b)=0.
```

Equivalently, prove that none exist or reconstruct an explicit factorization
from one.  Every genuine point must additionally have signed-square `b` and,
on the reciprocal quotient, satisfy

```text
U-2 and U+2 are rational squares; V=a^2/b is a square or a negative square.
```

The finite-prime theorem reduces this to the explicit residual congruence
classes stored in the certificate, but the residual set is infinite.  No
finite fixed-prime sieve can finish the proof: `p=0 mod ell, q=1 mod ell`
survives every selected prime.
