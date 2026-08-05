# Handoff

## Best next theorem

Certify an exact function-field isomorphism from the normalization of the
99-term plane model `H(q,A)=0` to one of

```text
E1: y^2=x^3-5*x+4,
E2: y^2=x^3+5*x+18,
```

and transport `q,A` in both directions, including every denominator-zero
fiber.  Nineteen exact traces match the `544.c` isogeny class, and an
elementary proof already gives rank `1` and torsion `Z/2Z` for `E1`, but the
finite fingerprint is not an identification theorem.

The prepared direct route avoids the stalled maximal-order computation:
`e_model_singular_rr_cubic.py` constructs a Riemann--Roch cubic from the
singular projective model, verifies both birational compositions in Singular,
and `e_model_sage_from_singular_cubic.py` converts the smooth cubic to a
Weierstrass curve and transports `q,A`.  An independent static audit found no
API or direction error, but the exact transcript is still required before
claim C025 can be promoted.  GitHub-hosted Actions currently fails before any
job step is allocated, so this is an execution-resource blocker rather than a
mathematical certificate.

The remaining invariant need not be descended again in Sage:
`research/arithmetic_geometry/e_model_dihedral_descent.py` gives a verified
direct formula `V(q,A)`.  Compose it with the transported `q,A` and audit its
zeros and poles on the normalized model.
`research/quotient_transport/derive_invariant_compact_v.py` independently
reduces the same function to `A`-degree at most nine.  Its exceptional
denominator locus is classified by
`research/quotient_transport/classify_transport_exceptions.py`: its only
rational `U`-fibers are inadmissible, so no genuine positive square-parameter
factor is lost by this chart.

Once the map is certified, transport the functions

```text
U+2, U-2, W+2, 2-W.
```

Then compute compatible rational points on the seven character quotients of
the two `(Z/2)^3` covers listed in
`notes/reciprocal_signed_square_covers.md`.  This requires certified
Mordell--Weil rank bounds, saturation/index control, an exhaustive covering
collection, and exact lift checks through the stored linear subresultant.
The staged rank-one sieve in `research/mw_square_sieve/` may finish the generic
open immediately, but only if all four sign/torsion CRT intersections are
literally empty.  A surviving residue class remains infinite and requires a
separate Chabauty, height, or genus-four Prym argument.

The linear-subresultant exception itself is closed: C033 proves that
`Q1(T,A)=0` has rational `T` only in `{-1,0,1}`, all inadmissible.  Remaining
special work concerns projective transport base loci and the `q=+/-2`,
`T=0,infinity`, `B=+/-1`, and omitted `b=-1` fibers.

## Why this is the blocker

- A finite congruence sieve cannot exhaust all primitive pairs by CRT; the
  present residual family is infinite.  This limitation is now proved by the
  family `p=0, q=1` modulo the product of any selected primes.
- The published height search is not a completeness theorem.
- The elliptic quotient forgets three independent square characters.  The
  genus-4 quotient from `U+2` alone is not sufficient: `U-2` and the signed
  `b` character must be imposed as well.

## Resume commands

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[test]'
PYTHON_BIN=.venv/bin/python scripts/reproduce.sh
PYTHON_BIN=.venv/bin/python scripts/replay_5plus5.sh
```

The `1+4` theorem is complete in `research/linear_factor_completion/`; a clean
Sage replay remains useful only as an archival reproducibility transcript.

For the remaining `2+3` case, run the Riemann--Roch transport followed by the
rank-one character sieve:

```bash
python3 research/arithmetic_geometry/e_model_singular_rr_cubic.py \
  --output /tmp/e_model_rr.sing --metadata /tmp/e_model_rr_input.json
Singular --random=1 -q /tmp/e_model_rr.sing | tee /tmp/e_model_rr.txt
sage -python research/arithmetic_geometry/e_model_sage_from_singular_cubic.py \
  --transcript /tmp/e_model_rr.txt --output /tmp/e_model_transport.json
sage -python research/mw_square_sieve/sage_mw_character_sieve.py \
  --transport /tmp/e_model_transport.json --prime-bound 500 \
  --output /tmp/mw_character_sieve.json
```
