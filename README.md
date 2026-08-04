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

The new result in this branch is a rigorous finite-field theorem.  Using all
25 primes at most 97 gives explicit projective congruence classes whose union
has exact natural density

\[
\frac{5689139917}{5689253052}=0.9999801142\ldots
\]

among primitive positive pairs `(p,q)`.  Thus the open `2+3` case is confined
to an explicit infinite residual family of density
`113135/5689253052 = 0.00198857...%`.  A smaller seven-prime certificate is
also retained for easier inspection.  This is not a proof of the full
conjecture.

See [STATUS.md](STATUS.md), [CLAIMS.md](CLAIMS.md), and
[HANDOFF.md](HANDOFF.md) for the conservative claim ledger and next theorem.

## Reproduction

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[test]'
PYTHON_BIN=.venv/bin/python scripts/reproduce.sh
```

Expected result: four tests pass.  The run regenerates the exact obstruction
polynomials and both finite-field certificates under `certificates/`.

To replay the embedded exact `5+5` script from arXiv:2601.04240:

```bash
PYTHON_BIN=.venv/bin/python scripts/replay_5plus5.sh
```

The research concerns an intermediate irreducibility conjecture.  It is not
equivalent to the nonexistence of perfect cuboids.
