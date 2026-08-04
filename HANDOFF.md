# Handoff

## Best next theorem

Prove that the square-parameter pullback `F(z^2,a)=0`, after imposing
`L != 0` and the lift `b=C/L`, has no rational points in the residual modular
classes from `certificates/modular_sieve_primes_le_97.json` except the known fibers
`z in {0, +/-1}`.

The most concrete route is now explicit.  Normalize the 99-term plane model
`H(q,A)=0` in `artifacts/genus4_quotient.json`, produce a Weierstrass model
`E`, and transport the functions

```text
U = 2*(q+6)/(q-2),
U+2 = 4*(q+2)/(q-2).
```

Then determine the points of `E(Q)` for which `U+2` is a square, and impose
the additional signed-square constant condition from
`notes/signed_square_descent.md`.  This requires certified Mordell--Weil rank
bounds, saturation/index control, an exhaustive covering collection, and
exact lift checks through the stored linear subresultant.

## Why this is the blocker

- A finite congruence sieve cannot exhaust all primitive pairs by CRT; the
  present residual family is infinite.  This limitation is now proved by the
  family `p=0, q=1` modulo the product of any selected primes.
- The published height search is not a completeness theorem.
- The elliptic quotient forgets square-lift information and has positive-rank
  behavior to control; rational points must be lifted through additional
  covers.

## Resume commands

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[test]'
PYTHON_BIN=.venv/bin/python scripts/reproduce.sh
PYTHON_BIN=.venv/bin/python scripts/replay_5plus5.sh
```

Then use Magma/Sage to normalize `F(z^2,a)=0`, construct the two reciprocal
quotients explicitly, certify their Jacobian ranks, and combine their local
images with the existing modular certificate.

The quotient equations and generic inverse are already constructed.  The
remaining external-CAS command should start from
`artifacts/genus4_quotient.json`, not redo the high-degree elimination.
