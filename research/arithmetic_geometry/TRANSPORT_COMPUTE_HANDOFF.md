# Exact elliptic transport: compute-machine handoff

> **Archived handoff — not a current task.** This high-memory route was not
> needed for the completed proof or Lean formalization. The direct
> normalization claim C025 remains an independent research question; see the
> [current repository status](../../README.md).

Date: 2026-08-06

## Objective

Produce a characteristic-zero, replayable certificate for a birational map
from the normalization of the reciprocal quotient to a Weierstrass curve, and
transport the functions `q`, `A`, and `V` in both directions.

The expected target is one of

```text
E1: y^2 = x^3 - 5*x + 4
E2: y^2 = x^3 + 5*x + 18
```

but a Frobenius fingerprint is not an identification theorem.  Do not promote
claim C025 until the exact maps and their compositions have been checked over
`QQ`.

## Recommended machine

This is a CPU/RAM symbolic-algebra job; a GPU is not useful.

Recommended minimum:

```text
RAM:       64 GiB; 128 GiB preferred
CPU:       16 cores; 32 useful for independent modular jobs
Storage:   50 GiB free scratch
Runtime:   uninterrupted 24--72 hours
Software:  SageMath 10.8+; Singular 4.4+; Magma if available
```

Run long jobs under `tmux`, `screen`, or a batch scheduler.  Preserve stdout,
stderr, wall time, peak RSS, software versions, random seeds, generated inputs,
and SHA-256 hashes.

## Repository checkpoint

At handoff, the branch is

```text
research/second-cuboid-conjecture
```

The repository already contains the primary characteristic-zero route:

```text
research/arithmetic_geometry/e_model_singular_rr_cubic.py
research/arithmetic_geometry/e_model_sage_from_singular_cubic.py
research/mw_square_sieve/sage_mw_character_sieve.py
```

The source quotient model is stored in

```text
artifacts/genus4_quotient.json
```

A useful lower-degree affine presentation is obtained from

```text
C = A - 2,
r = q*C.
```

Write the resulting equation as `J(r,C)=0`.  Local exploratory work indicates
that its projective degree is 12 and that its normalization has genus 1.  Those
local outputs are a checkpoint to replay, not a repository claim until their
inputs and transcripts are committed and independently verified.

## First run: existing direct route

Create a clean environment and reproduce the existing exact suite first:

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[test]'
PYTHON_BIN=.venv/bin/python scripts/reproduce.sh
PYTHON_BIN=.venv/bin/python bash scripts/replay_5plus5.sh
```

Then generate and execute the Singular Riemann--Roch route:

```bash
mkdir -p run/transport
python3 research/arithmetic_geometry/e_model_singular_rr_cubic.py \
  --output run/transport/e_model_rr.sing \
  --metadata run/transport/e_model_rr_input.json

/usr/bin/time -v Singular --random=1 -q run/transport/e_model_rr.sing \
  > run/transport/e_model_rr.txt \
  2> run/transport/e_model_rr.time.txt
```

If the transcript reaches

```text
CERT singular_rr_cubic_finished=OK
CERT source_projective_composition=OK
CERT target_projective_composition=OK
```

convert the cubic and transport the functions:

```bash
sage -python research/arithmetic_geometry/e_model_sage_from_singular_cubic.py \
  --transcript run/transport/e_model_rr.txt \
  --output run/transport/e_model_transport.json
```

The Sage stage must verify the cubic is smooth, identify its exact
Weierstrass model, export maps in both directions, and retain every base locus,
pole, and denominator-zero fiber.

## Fallback: exact normalization of the degree-12 model

If `RiemannRochBN` stalls or returns a nongeneric auxiliary form, use the
lower-degree model `J(r,C)` and compute the affine normalization over `QQ`.
The exact target object is

```text
U/d = integral closure of QQ[r,C]/(J).
```

Required checks:

```text
1. U/d is closed under multiplication;
2. the normalization map sends r and C to their original classes;
3. the affine delta length is exactly the independently predicted value;
4. all points at infinity and all branches over singular points are retained;
5. a rational point above (r,C)=(-48/7,-8/7) is identified exactly.
```

Then compute

```text
dim L(2P) = 2
dim L(3P) = 3
```

on the normalized curve, construct the complete `|3P|` map, invert it, and
verify both projective compositions modulo the exact source and target ideals.
Do not infer pole orders from the singular plane model alone.

A modular calculation may be used to discover formulas, but the final formulas
must be reconstructed over `QQ` and checked there.  Recommended independent
primes are good primes not dividing any source denominator or discriminant.
Use at least two primes to detect special reductions before CRT/rational
reconstruction.

## Acceptance criteria for the transport certificate

The final machine-readable artifact must contain:

```text
- exact source equation and its SHA-256;
- exact target Weierstrass equation;
- source-to-target homogeneous map;
- target-to-source homogeneous map;
- exact formulas for q, A, and V on the target;
- source and target base loci;
- zero/pole divisors of all map denominators;
- exact reductions proving both projective compositions;
- software versions, commands, seed, timings, and input hashes.
```

The transcript may print

```text
WEIERSTRASS_Q_A_TRANSPORT_CERTIFIED
```

only after all of the following hold over `QQ`:

```text
E(phi_X,phi_Y,phi_Z) == 0 mod source ideal;
J(psi_r,psi_C,psi_Z) == 0 mod target ideal;
all three projective minors of psi(phi) vanish mod source ideal;
all three projective minors of phi(psi) vanish mod target ideal;
q and A round-trip as rational functions;
V agrees with the independently certified V(q,A) formula;
all denominator and base-locus fibers are listed for separate rational audit.
```

## After transport: square-character sieve

Run the staged rank-one sieve:

```bash
sage -python research/mw_square_sieve/sage_mw_character_sieve.py \
  --transport run/transport/e_model_transport.json \
  --prime-bound 500 \
  --output run/transport/mw_character_sieve.json
```

A finite sieve closes the generic case only if all four sign/torsion CRT
intersections are literally empty.  A surviving residue class is an infinite
arithmetic progression, not a finite candidate.  In that case the next task is
a certified Chabauty/Strassmann/height argument, not merely adding more search
height.

The three simultaneous square conditions that must be enforced are

```text
q + 2 is a rational square;
q - 2 is a rational square;
+V or -V is a rational square, with the sign tracked consistently.
```

## Failure reporting

For every failed route, save the last completed `CERT` marker, exact command,
input checksum, elapsed time, peak RSS, and the full stack trace or CAS error.
Do not convert a timeout, out-of-memory event, modular coincidence, or partial
normalization into a mathematical claim.

## Final repository update

When the certificate succeeds:

1. commit the generator scripts, exact transcript, compact JSON certificate,
   and a small independent replay checker;
2. update `CLAIMS.md`, `STATUS.md`, `HANDOFF.md`, and `paper/main.tex`;
3. run the complete reproduction suite;
4. leave the conjecture marked `OPEN` unless the subsequent square-character
   analysis also eliminates every admissible point.
