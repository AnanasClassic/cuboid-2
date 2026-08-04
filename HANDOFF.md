# Handoff

## Best next theorem

Prove that the square-parameter pullback `F(z^2,a)=0`, after imposing
`L != 0` and the lift `b=C/L`, has no rational points in the residual modular
classes from `certificates/modular_sieve_primes_le_97.json` except the known fibers
`z in {0, +/-1}`.

The most concrete route is a covering/Mordell--Weil sieve on the reciprocal
quotients of the genus-17 square pullback.  The genus-1 quotient of the
original genus-7 curve is not enough: after adjoining `z^2=s`, the two lifted
reciprocal quotients have genera 4 and 8.

## Why this is the blocker

- A finite congruence sieve cannot exhaust all primitive pairs by CRT; the
  present residual family is infinite.
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
