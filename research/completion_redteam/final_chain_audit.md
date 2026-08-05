# Adversarial audit of the proposed `2+3` completion chain

## Bottom line

An exact isomorphism between the normalization of `H(q,A)=0` and a rank-one
elliptic curve is necessary, but it does not by itself finish the rational
point problem.  A finite Mordell--Weil sieve is a proof only if its certified
global intersection is empty.  A nonempty class modulo a large modulus is an
infinite arithmetic progression of Mordell--Weil coefficients, not a finite
list of rational points.

The most economical stronger target is probably the genus-four curve
`G(X,A)=0`.  Every admissible point gives a rational point on this curve with
`X=T^2` a rational square.  A complete determination of `G(Q)`, followed by
an exact square and lift check, would finish `2+3` without determining all
seven signed-character curves.  Since

```text
Jac(G) ~ E x Prym(G/E),  dim Prym = 3,
```

the decisive computation is a certified rank bound and rational-point
calculation for this genus-four curve/Prym.

## 1. Exact normalization and Weierstrass transport

The following obligations are independent and must all be certified.

1. `H` is geometrically integral and its projective normalization is a smooth
   genus-one curve with a rational point.
2. The maps between its function field and the proposed Weierstrass model are
   inverse exact field homomorphisms.  Dense-open polynomial identities are
   sufficient for the function-field isomorphism, provided all displayed
   denominators are nonzero as functions and both field degrees are one.
3. The cubic produced by Riemann--Roch is geometrically smooth.  A singular
   affine normalization alone is not a certificate for the projective points
   at infinity.
4. The exact `j`-invariant decides whether the model is `E1` or `E2`; finitely
   many matching Frobenius traces do not.  If the answer is `E2`, a basis for
   `E2(Q)` is required.  An isogeny from `E1` proves the rank but need not send
   a generator to a saturated generator of `E2(Q)`.
5. The rational functions `q`, `A`, and `V` must be transported as function
   field elements, with exact substitution identities.  Their full zero and
   pole divisors, including points above singular plane coordinates, must be
   recorded.
6. A birational map of smooth projective curves extends uniquely to an
   isomorphism, so formula-by-formula values at every base point are not
   needed to transfer the Mordell--Weil group.  They are needed for the final
   coordinate/lift audit: every rational point supporting a map denominator
   must be enumerated on the normalization and treated separately.

## 2. Mordell--Weil basis

Rank one plus a non-torsion point is not a basis theorem.  It only shows that
the point generates a finite-index subgroup.  The required statement is

```text
E(Q) = Z*P direct_sum <T>,  ord(T)=2.
```

For `E1`, the proof-mode Sage output records `rank_bounds=(1,1)`,
`gens_certain=True`, and full saturation index one for `P=(0,2)`.  The final
certificate should retain the exact Sage version, global proof flags, the
meaning of `max_prime=-1`, and the complete transcript.  The elementary
2-isogeny descent proves rank and torsion but does not exclude `P=mG` for an
odd integer `m>1`.

## 3. The actual square conditions

For an admissible point, all of the following are required on `E`:

```text
q+2 = square,
q-2 = square,
epsilon*V = square,  epsilon in {+1,-1},
q > 2.
```

Both first conditions are essential.  If their roots are `r_plus,r_minus`,
then

```text
T=(r_plus+r_minus)/2,
1/T=(r_plus-r_minus)/2,
```

and their product is one.  For `q>2`, one of the reciprocal choices has
`0<|T|<1`, giving a positive rational `z=(1+T)/(1-T)` with `z!=1`.

The implication from `epsilon*V` to signed-square `b` uses
`V=a^2/b` and division by `a`.  The repository's exact specialization
`F(s,0)` excludes `a=0` for admissible rational `s`; this exclusion is a
logical dependency, not an optional chart convenience.

Equivalently, define the two normalized covers

```text
Y_epsilon / E:
  y1^2=q+2, y2^2=q-2, y3^2=epsilon*V.
```

An admissible factor supplies a rational point on one of them away from all
zeros and poles.  Rational points at branch divisors and at infinity must not
be silently discarded when computing local images.

## 4. Exact criterion for an exhaustive finite Mordell--Weil sieve

Let `E(Q)=Z*P direct_sum E(Q)_tors`, and let `S` be a finite set of odd
primes of good reduction for the elliptic curve, the chosen cover model, and
the cover map.  For each `ell`, let

```text
I_(ell,epsilon) = image(Y_epsilon(F_ell) -> E(F_ell)).
```

For each fixed global torsion element `tau`, pull this set back under

```text
n |-> reduction(n*P+tau).
```

This gives a periodic set `C_(ell,epsilon,tau)` modulo the exact order of
`P mod ell`.  Combine the sets in the original integer variable `n`, using
an lcm/generalized CRT; do not multiply moduli as if they were coprime.  Keep
the sign `epsilon` and torsion element `tau` fixed while combining primes.

Then a finite sieve is genuinely exhaustive precisely in either of these
situations:

1. for both signs and every torsion element, the combined pullback is
   literally empty; or
2. every surviving congruence class is combined with a separately proved
   global height bound (so only finitely many `n` remain), or with a complete
   covering/Chabauty theorem that proves which points in the class lift.

Without item 1 or 2, the sieve is evidence only.  In particular:

- one residue class modulo `M`, however large `M` is, contains infinitely
  many integers `n`;
- a bounded search through those integers is not a completeness theorem;
- a finite-prime density tending to one is not a rational-point theorem;
- an excluded rational boundary point on `Y_epsilon` can force a survivor at
  every prime.  Its residue class cannot simply be deleted, since an unknown
  admissible point can have the same reduction.

A safe implementation need not initially normalize every finite-field cover.
Away from the reductions of the zeros and poles, require the three function
values to be squares in `F_ell`.  Mark every reduction where a numerator or
denominator vanishes as **allowed/unknown**.  This is a certified superset of
the true local image; if even this superset has empty global pullback, the
conclusion is valid.  Shrinking the exceptional residue disks requires exact
local normalization or `ell`-adic analysis.  Merely evaluating a rational
function as `0` or infinity there is not safe.

The CRT obstruction for finite congruence sieves on primitive `(p,q)` does
not logically rule out this rank-one Mordell--Weil sieve: the latter acts on
one global integer `n`.  It can finish the proof if its combined set is empty.
It is not guaranteed to be empty.

## 5. Exceptional fibres and reverse lift

For any surviving elliptic point, the following branches must be closed.

1. `q=+/-2`, poles of `q`, and poles of the `H <-> E` coordinate maps.
2. `T=0,+/-1,infinity` in the square-root/Mobius chart.
3. The compact-`V` denominator and the leading-coefficient multiplier used in
   pseudo-reduction.  The existing compact-transport certificate excludes
   their rational admissible points.
4. `Q1(T,A)=0`, where the linear subresultant does not reconstruct `B`.
   This is now closed by `q1_exception_certificate.py`: the exact resultant
   in `A` has only rational `T`-roots `-1,0,1`, all inadmissible.
5. `B=+1` (`b=infinity`), `B=-1` (`b=0`), and the omitted `b=-1` chart.
6. `A=0`/`a=0`, `V=0`, and a zero or pole of the square root used to recover
   `c=a/y`.
7. The degenerate original branch `L=C=0`, already classified rationally as
   `s=+/-1`.
8. All rational normalization branches over singular/projective coordinates;
   rationality of a singular plane coordinate does not imply that every
   branch above it is rational.

On the remaining open set, reconstruct

```text
B=-Q0/Q1,
z=(1+T)/(1-T), s=z^2,
b=(1+B)/(1-B), a=A/(1-B).
```

Then substitute into the original, uncleared equations `R1=R0=0`.  This last
check is required because the plane models were obtained by resultants and
denominator clearing.  If a counterexample survives, reconstruct the monic
quadratic and cubic factors and verify their product with `P_s`, then scale
back to coprime positive integers `p,q` and multiply the proposed factors of
`Q_(p,q)` exactly.

## 6. Recommended decision tree

1. Finish the exact `H <-> E` map and certified basis.
2. Run the safe rank-one finite sieve for both signs.  It is cheap and may
   produce an empty certificate.
3. If it leaves classes, do not enlarge the prime set indefinitely without
   checking whether known boundary points force permanent survivors.
4. In parallel, normalize `G(X,A)=0`, certify `rank Jac(G)`, and attempt a
   complete `G(Q)` calculation.  This genus-four theorem is sufficient after
   filtering `X` for rational squares and running the exact reverse lift.
5. Only if the genus-four route fails should the full seven character curves
   and their Prym ranks become the primary target.
