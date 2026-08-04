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
central Magma--Chabauty computation for `1+4` has not been rerun locally.

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

The square-parameter pullback now also has an explicit genus-four plane model,
a generic inverse map, and an exact bielliptic quotient equation.  The missing
step is a certified Weierstrass normalization and complete square-value
computation on that elliptic quotient.

See [STATUS.md](STATUS.md), [CLAIMS.md](CLAIMS.md), and
[HANDOFF.md](HANDOFF.md) for the conservative claim ledger and next theorem.

## Reproduction

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[test]'
PYTHON_BIN=.venv/bin/python scripts/reproduce.sh
```

Expected result: nine tests pass.  The run regenerates the exact obstruction
polynomials, quotient models, and finite-field certificates.

To replay the embedded exact `5+5` script from arXiv:2601.04240:

```bash
PYTHON_BIN=.venv/bin/python scripts/replay_5plus5.sh
```

The research concerns an intermediate irreducibility conjecture.  It is not
equivalent to the nonexistence of perfect cuboids.
