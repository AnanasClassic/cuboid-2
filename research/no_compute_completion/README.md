# No-compute completion route

Date: 2026-08-10

## Status

**Superseded by the completed low-resource proof.**  This file is retained as a historical
record of the routes considered before C039--C042.  The proof now closes C010 and C020 through
the compact reciprocal quotient, an explicit low-degree transport to `E1`, a common-character
valuation descent, and an exact genus-2 square-abscissa classification.  It does not use the
persistent Sage/Singular normalization route, and C025 remains open because it is no longer
needed.  See `notes/quadratic_cubic_completion.md` and `STATUS.md`.

The remainder of this note describes the state before that completion and must not be read as
the current claim ledger.

This note originally recorded the strategy when the persistent Sage/Singular compute route was
unavailable.  At that time it did **not** claim a proof of Sharipov's second cuboid conjecture and
did not upgrade C010, C020, or C025.

The exact remaining obstruction is still the `2+3` split: an admissible rational point on the
quadratic-factor curve must survive the reverse lift and the three simultaneous square-character
conditions on the reciprocal elliptic quotient.

## Results obtained after the initial strategy audit

The endpoint no-go below remains correct, but the next coefficient layer and
the **full** projection now close all of its formal survivors when
`p=L^m,q=R^n` are powers of two distinct inert odd primes.  This is C034,
reproduced by `research/global_descent/second_endpoint_layer.py`.  It does
not extend automatically to multi-prime `p,q`, because different prime
divisors may carry different local types.

Imposing the square equations early also produced C035: an exact 71-term
compact curve `Q_epsilon(z,k)=0` equivalent to the signed-square factor
locus at every admissible rational point, with a complete rational inverse
and no denominator exception.  Its rational points remain open.

The direct Kummer-identity target in item 2 is now an exact no-go: all seven
nontrivial products of `q+2,q-2,epsilon*V` are ramified, while the standard
2-isogeny Kummer character is unramified.  Likewise, the ambient
Möbius/monomial V4 shortcut in item 4 is excluded.  Arithmetic evaluation
after an explicit transport, nonlinear automorphisms, and Prym splittings
without automorphisms remain possible.

## What was checked in the no-compute pass

The first natural attempt was to replace the elliptic normalization/Mordell--Weil computation by a
purely local-global argument using the Newton pair types at primes dividing `pq`.
The repository already contains enough exact information to rule out the naive version of that idea.

For an inert odd prime `(2/ell)=-1`, a hypothetical quadratic factor has normalized local index in
`{0,3,4}`.  For two inert prime powers `p=L^m`, `q=R^n`, every nonuniform branch satisfies the endpoint
conditions

```text
R^(e n) = sigma (mod L),
L^(e m) = sigma (mod R),
e = 2|u-v| in {2,6,8},
sigma = sign(b).
```

The existing exact endpoint analysis proves several eliminations, but also proves that endpoint
congruences plus quadratic reciprocity are not complete:

- positive-sign endpoint systems have infinite formal survivors (for example by Fermat after choosing
  suitable exponents);
- negative `e=2,6` systems genuinely survive reciprocity, e.g. the endpoint pair `(L,R,m,n)=(5,13,1,1)`;
- a single rational quadratic factor can select different Newton pair types at different primes, so
  local valuation data for `A,B` alone cannot force a global uniform type.

Therefore a proof that only propagates endpoint congruences, Legendre symbols, or valuations of `A,B`
will not finish the general case.  Any local-global route must use **more of the full remainder
system** `R1=R0=0` (or an equivalent global invariant), not merely the Newton polygon endpoints.

## Recommended non-compute targets

The best remaining routes, in decreasing order of attractiveness, are:

1. **Explicit hand derivation of the elliptic model.**  Starting from the lower-degree coordinates
   `C=A-2`, `r=q*C`, look for a direct sequence of rational substitutions reducing the normalization
   of `H(q,A)=0` to one of the candidate curves
   `E1: y^2=x^3-5*x+4` or `E2: y^2=x^3+5*x+18`.
   The goal is an exact birational map with inverse and an audit of denominator/base-locus fibers,
   obtained by symbolic identities rather than a general-purpose normalization routine.

2. **Direct rank-one square-character descent.**  If an explicit map to `E1` can be written down,
   avoid a large Mordell--Weil sieve if possible.  Prove directly for
   `E1(Q)=<P=(0,2)> + <T=(1,0)>` that no admissible point has all three required characters
   `q+2`, `q-2`, and `epsilon*V` square.  Search for a 2-isogeny/Kummer interpretation of these
   functions, divisor relations, or a parity/height obstruction on `nP+eT`.

3. **Strengthen the full-resultant local-global descent.**  For each nonuniform Newton type, retain
   at least the next coefficient(s) beyond the lowest endpoint in the full projection.  Look for a
   multiplicative/global relation coupling different prime divisors of `p` and `q`.  A successful
   theorem must distinguish the endpoint survivors already stored in the repository.

4. **Exploit extra automorphisms or Prym splitting.**  The genus-4 character curve for
   `(q+2)(q-2)` has only the reciprocal involution certified so far.  Search manually for an
   additional involution after a low-degree coordinate change.  A split into elliptic factors could
   replace the high-genus Chabauty/Prym computation by explicit rank-one/rank-zero arguments.

5. **Elementary contradiction from the reverse lift.**  Work directly with
   `G(T^2,A)=0`, `Q1(T,A)B+Q0(T,A)=0`, `C^2=epsilon*(1-B^2)` and the already-proved fact that
   `Q1=0` is inadmissible.  Eliminate `A` or `B` only after imposing the square equations, seeking a
   factorization into low-genus curves or a sum-of-squares/positivity contradiction.

## Guardrails for the next agent

Do not claim completion from any of the following:

- more fixed-prime sieving;
- bounded-height searches;
- endpoint congruences alone;
- a Frobenius fingerprint without an exact function-field map;
- a nonempty finite Mordell--Weil residue class as if it were a finite rational-point set;
- a point on `K(U,W)=0` or on one character quotient without the other square characters and exact
  reverse lift.

A valid completion must either prove C010 directly, or prove enough of C025/C020 to classify all
compatible rational points and then run the exact reverse lift including every boundary fiber.

## Existing exact facts to reuse

- `1+4` is closed by a complete Magma-free genus-2 argument.
- symmetric `5+5` is machine-verified.
- signed-square descent gives `B=+d^2` or `B=-d^2`.
- fixed-prime sieving has an exact infinite-family limitation.
- the candidate elliptic curve `E1` has proved rank 1 and torsion `Z/2Z`.
- `V=a^2/b` is already available as an exact rational function on `H`.
- the reverse-lift exceptional branch `Q1(T,A)=0` is already closed.

The purpose of this note is to keep future work focused on a genuinely stronger global invariant or
an explicit low-complexity elliptic descent, rather than repeating local endpoint arguments that the
current repository already shows are insufficient.
