# Status

Date: 2026-08-05

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
- A direct exact rational expression `V(q,A)=a^2/b` on the reciprocal
  quotient.  Dihedral cross-products replace the function-field inversion
  that timed out in Sage; the formula is independently replayable and gives
  `V(6,6/7)=-36` at the stored smooth point.
- An independent invariant elimination reduces that expression to degree at
  most `9` in `A` and verifies equality by exact pseudo-remainders modulo
  `H`.  Exact saturated resultants show that every rational denominator-zero
  branch has `U` in `{-2,-1,2}` and is inadmissible; for an admissible
  positive square parameter the final denominator is nonzero.
- Exact singularity, special-fiber, and discriminant diagnostics for `H`.  In
  particular, the squarefree discriminant quartic is rigorously shown not to
  be the reciprocal elliptic quotient with the `q`-map preserved.
- Exact reciprocal elimination in `U=s+1/s`, `W=b+1/b`, producing an
  irreducible bidegree-`(20,10)` equation `K(U,W)=0` and a perfect-square
  resultant certificate.
- Complete branch table for the three required square characters
  `U+2`, `U-2`, and `W+2` or `2-W`.  The seven character quotients have
  genera at most 8, while each full signed-square cover has genus 33.
- Exact global exclusion of the `2+3` split for every prime-power axis family
  `{p,q}={1,ell^k}`.  More generally, a hypothetical counterexample needs at
  least two primes in `pq` and different Newton pair types at two of them.
- Exact global exclusion of the `2+3` split for
  `{p,q}={3,r^n}` with `r!=3` prime, `r` congruent to `3` or `5` modulo `8`,
  and every `n>=1`.
  The proof uses exact resultant endpoint valuations and separately closes
  the only intermediate primes `5` and `13`.
- For two distinct prime powers `p=L^m,q=R^n` with `2` a quadratic
  nonresidue at both primes, all nonuniform Newton branches satisfy five
  explicit endpoint systems.  Reciprocity removes negative sign with
  `e=8`; the remaining negative branches require `L,R=5 mod 8`, odd `m,n`,
  and mutual quadratic nonresiduosity.  These endpoint conditions are only
  necessary: the exact certificate records surviving infinite systems rather
  than claiming a general two-prime theorem.
- An independently audited Frobenius/Burnside fingerprint for the reciprocal
  elliptic quotient at nineteen certified good primes.  Both curves in the
  candidate class `544.c` match every trace and their explicit 2-isogenies are
  verified.
- An elementary, database-free 2-isogeny descent proving that the candidate
  curve `y^2=x^3-5*x+4` has rank `1` and torsion `Z/2Z`.
- A complete Schaefer--Stoll 2-descent for the genus-2 Jacobian in the `1+4`
  case.  It proves `dim Sel_2=2`, rank `1`, and trivial `Sha[2]` using a
  certified quartic class/unit group and exhaustive local images at `2` and
  infinity; the odd prime `43` is closed by the tame discriminant-one case.
- A complete, Magma-free exclusion of the `1+4` split.  At `p=5`, the six
  known rational points occupy every residue disk.  Coleman integration gives
  the annihilator `(1+t)dt/(2w)`; it is ordinary in five disks, while the
  Weierstrass disk at `(-1,0)` has the exact Strassmann form
  `G(5z)/25=z*(unit+5*z^2*Z_5[[z^2]])`.  The exact lift table leaves only
  `s=1`, `s=-1`, or poles.
- Exact closure of the `Q1(T,A)=0` branch in the reverse `2+3` lift.  The
  resultant has rational roots only at `T=-1,0,1`, corresponding to boundary
  parameters or excluded `s=1`.

## Conditional or externally dependent

- Exact local Newton and Riemann--Hurwitz calculations recover genus 7 for the
  two-root curve and genus 17 for the square pullback.  The fixed-point counts
  giving reciprocal quotient genera 1, 4, and 8 have not been checked in a
  second geometry system; no complete rational-point computation follows.
- The normalization/branch interpretation of the new singular quotient models
  still depends on that local quotient audit.  The polynomial identities and
  generic maps are machine-verified.  Finitely many traces select `544.c` as a
  compelling candidate, but they do not prove an isogeny or choose one of its
  two non-isomorphic models.  Until an exact function-field map is produced,
  the proved rank-one statement for the candidate cannot be transferred to
  the cuboid quotient.  The invariant `V` itself no longer needs a separate
  Sage descent: once `q,A` are transported, its certified formula composes
  with that map.

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
K(U,W)=0;
U-2 and U+2 are rational squares;
W+2 is a square if b>0, or 2-W is a square if b<0.
```

The two signs give explicit `(Z/2)^3` covers.  A point on `K` or on one
character quotient is only necessary: all compatible characters and the
reverse lift to `s,a,b` must be checked.

The generic reverse lift no longer has an unresolved linear-subresultant
branch: C033 proves that `Q1(T,A)=0` occurs over `Q` only at inadmissible
values.  What remains is the global rational-point computation, not another
resultant-denominator audit.

The finite-prime theorem reduces this to the explicit residual congruence
classes stored in the certificate, but the residual set is infinite.  No
finite fixed-prime sieve can finish the proof: `p=0 mod ell, q=1 mod ell`
survives every selected prime.

Any residual counterexample must additionally avoid the two infinite-family
theorems above: `pq` has at least two distinct prime factors with nonuniform
local pair types, and it is not in the certified `{3,r^n}` inert family.  If
`p,q` are powers of two distinct inert odd primes, their local types must also
lie in one of the five endpoint systems recorded in C026--C027.
