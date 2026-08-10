# Sharipov's second cuboid conjecture

This repository studies the irreducibility over `Q` (equivalently `Z`) of

\[
Q_{p,q}(t)=q^{20}P_s\!\left(t^2/q^4\right),\qquad
s=(p/q)^2,
\]

for coprime positive integers `p != q`, where

\[
\begin{aligned}
P_s(x)={}&x^5+(2+s)(3-2s)x^4
 +(1+10s+4s^2-14s^3+s^4)x^3\\
&-s(1-14s+4s^2+10s^3+s^4)x^2
-s^3(1+2s)(-2+3s)x-s^5.
\end{aligned}
\]

## Current status

**The conjecture remains open.**  The only unresolved factorization mechanism
is a quadratic--cubic (`2+3`) split of `P_s`.  The `1+4` and symmetric `5+5`
cases are addressed by 2026 preprints; this repository independently checks
their algebra and exactly replays the complete `5+5` Sturm certificate.  The
`1+4` case is now independently proved without Magma: a certified
Schaefer--Stoll 2-descent gives rank one and trivial `Sha[2]` for the relevant
genus-2 Jacobian, and an exact `p=5` Coleman/Strassmann argument determines all
six rational points.  Their complete inverse images give only `s=1`, `s=-1`,
or poles, so no admissible rational root remains.

The strongest new arithmetic result is a signed-square descent.  If the
integral quintic `H_{p,q}(X)=Q_{p,q}(t)`, `X=t^2`, has a quadratic factor
`X^2+A*X+B`, then exact Newton polygons at every prime dividing `p*q` force

\[
B=\pm d^2.
\]

Respecting this one global sign across every odd prime at most 137 gives
explicit projective congruence classes whose union has exact natural density

\[
\frac{3917894203934863}{3917894203948032}
=0.9999999999966388\ldots
\]

among primitive positive pairs `(p,q)`.  Thus the open `2+3` case is confined
to an explicit infinite residual family of density
`13169/3917894203948032`, approximately `3.3612e-12`.  This is still not a
proof: the residual congruence family is infinite.

Three exact global-descent theorems now cut into that residual family without
any height bound.  The `2+3` split is impossible whenever

\[
\{p,q\}=\{1,\ell^k\}
\]

for any prime `ell` and `k>=1`.  It is also impossible for

\[
\{p,q\}=\{3,r^n\},\qquad r\ne3,\quad r\equiv3,5\pmod 8,
\]

for every `n>=1`.  The first theorem checks all ten exact branches
`b=+/-s^m`; the second combines local Newton types with exact endpoint
valuations of the quadratic-factor resultant.  These are infinite-family
theorems for the remaining quadratic factor, not bounded searches.

The third theorem closes the general pair

\[
p=L^m,\qquad q=R^n,
\]

when `L,R` are distinct odd primes and `2` is a quadratic nonresidue at both.
The formerly surviving endpoint systems are eliminated by using the next
coefficient layer and the full projection equation.  Exact
positive-coefficient charts close all `e=6,8` branches, while an elementary
divisibility descent closes `e=2`.  This is a complete two-prime-power
theorem, but it does not cover general multi-prime `p,q`, where one factor may
choose different local types at different primes.

The square-parameter pullback now also has an explicit reciprocal elliptic
plane equation and two exact signed-square `(Z/2)^3` covers.  All seven
character quotients have genus at most 8.  Exact good-prime point counts give
a Frobenius fingerprint matching the two models in isogeny class `544.c`.
The third invariant is already explicit: an exact dihedral calculation gives
`V=a^2/b` as a rational function of the quotient coordinates `(q,A)` and
avoids the function-field inversion that stalled the first Sage run.
An independent invariant elimination reduces this representative to degree
at most nine in `A`; its denominator-zero chart remains explicitly tracked.
For the candidate `y^2=x^3-5*x+4`, an elementary 2-isogeny descent proves
rank `1` and torsion `Z/2Z` without database input.  This remains candidate
data until an exact map from the normalization of `H(q,A)=0` is certified;
matching finitely many traces is not such a map.

The suggested low-degree transport shortcut has been audited exactly.  In
the whole family `C=A-c, r=(q-q0)C`, the only rational shift producing a
common boundary factor is `c=2`, and its primitive plane equation still has
total degree 12.  Rational singularity pencils have degree at least 8, while
the unique unramified rational point above `q=6` rules out expressing `q`
through a rational degree-2 quotient.  A different birational transport using
both elliptic coordinates is not excluded.

The generic inverse used after the square-character computation is also now
complete on admissible rational points.  Exact factorization of
`Res_A(G(T^2,A),Q1(T,A))` shows that its subresultant denominator can vanish
over `Q` only for `T=-1,0,1`, all boundary values or the excluded parameter
`s=1`.  The unresolved task is therefore the global rational-point problem on
the remaining `2+3` cover, not an exceptional denominator branch.

The full signed-square locus now has a smaller exact presentation as well.
For each sign it is birational on every admissible rational point to an
explicit irreducible 71-term plane curve `Q_epsilon(z,k)=0`; the rational
inverse and all denominator exceptions are certified in
`research/compact_signed_square/`.  This does not determine its rational
points.  A separate character audit proves that all seven nontrivial products
of `q+2`, `q-2`, and `epsilon*V` are ramified, ruling out the simplest direct
identification with the unramified 2-isogeny Kummer character.

See [STATUS.md](STATUS.md), [CLAIMS.md](CLAIMS.md), and
[HANDOFF.md](HANDOFF.md) for the conservative claim ledger and next theorem.

## Reproduction

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[test]'
PYTHON_BIN=.venv/bin/python scripts/reproduce.sh
```

The run regenerates the exact obstruction
polynomials, quotient models, and finite-field certificates.

To replay the embedded exact `5+5` script from arXiv:2601.04240:

```bash
PYTHON_BIN=.venv/bin/python scripts/replay_5plus5.sh
```

The research concerns an intermediate irreducibility conjecture.  It is not
equivalent to the nonexistence of perfect cuboids.
