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
- New finite-prime modular theorem excluding `2+3` for density
  `5689139917/5689253052` of primitive pairs.  The certificate is checked by both
  exhaustive monic-quadratic division and independent finite-field
  factorization.

## Conditional or externally dependent

- The algebraic part of arXiv:2601.04241 (`1+4`) is independently verified.
  Its list of rational points on a genus-2 curve depends on a Magma transcript
  (`RankBound=1`, infinite Jacobian point, `Chabauty`).  The Magma run was not
  available locally, so the final exclusion is labelled CONDITIONALLY VERIFIED.
- Exact local Newton and Riemann--Hurwitz calculations recover genus 7 for the
  two-root curve and genus 17 for the square pullback.  The fixed-point counts
  giving reciprocal quotient genera 1, 4, and 8 have not been checked in a
  second geometry system; no complete rational-point computation follows.

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
from one.  The finite-prime theorem reduces this to the explicit residual
congruence classes stored in the certificate, but the residual set is infinite.
