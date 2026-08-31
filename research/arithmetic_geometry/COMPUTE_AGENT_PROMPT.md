# Prompt for the compute-machine agent

> **Archived prompt — do not execute as current instructions.** This runbook
> predates the completed proof and Lean formalization. The final argument
> bypasses the direct normalization target C025; see the
> [current repository status](../../README.md).

Use the connected GitHub repository:

```text
https://github.com/AnanasClassic/cuboid-2
```

Work on the existing branch:

```text
research/second-cuboid-conjecture
```

Continue draft PR #1.  Inspect the actual branch head, PR, `README.md`,
`STATUS.md`, `CLAIMS.md`, `HANDOFF.md`, `paper/main.tex`, and all relevant
files under `research/` before changing anything.  Do not assume a recorded
SHA is current; verify it.

Read this runbook first and follow it as the execution contract:

```text
research/arithmetic_geometry/TRANSPORT_COMPUTE_HANDOFF.md
```

## Non-negotiable objective

Produce a characteristic-zero, independently replayable certificate for the
birational transport

```text
normalization of H(q,A)=0  <->  a Weierstrass elliptic curve over QQ
```

and transport `q`, `A`, and the already certified function `V(q,A)` in both
directions.

The expected target is in the isogeny class represented by

```text
E1: y^2 = x^3 - 5*x + 4
E2: y^2 = x^3 + 5*x + 18
```

but do not infer an exact identification from finite Frobenius traces.  The
output must contain explicit rational maps over `QQ` and exact verification of
both projective compositions.

## Required work order

1. Reproduce the existing exact test suite.
2. Run the prepared Singular Riemann--Roch route from
   `e_model_singular_rr_cubic.py` with fixed seed and full resource logging.
3. If it succeeds, convert and verify the cubic with
   `e_model_sage_from_singular_cubic.py`.
4. If it stalls, use the lower-degree presentation
   `C=A-2`, `r=q*C`, compute the exact normalization of `J(r,C)` over `QQ`,
   and compute `L(2P)` and `L(3P)` on the normalization.
5. Modular computations may discover formulas, but reconstruct over `QQ` and
   verify over `QQ`.  Use multiple good primes to detect special reductions.
6. Audit all source/target base loci, denominator-zero fibers, points at
   infinity, and singular branches.
7. Compose the certified direct formula `V(q,A)` with the map and verify it in
   the function field.
8. Emit a compact JSON certificate and an independent replay checker.
9. Run the staged Mordell--Weil square-character sieve only after the
   transport certificate is complete.

## Certificate acceptance criteria

Do not print or claim

```text
WEIERSTRASS_Q_A_TRANSPORT_CERTIFIED
```

unless all of the following have been checked over `QQ`:

```text
- the target Weierstrass equation is exact and smooth;
- the source-to-target map lands on the target;
- the target-to-source map lands on the source;
- all three projective minors vanish for each composition;
- q and A round-trip as rational functions;
- V agrees with the independently certified V(q,A) expression;
- every base locus and map denominator fiber is explicitly recorded;
- source files, commands, versions, seeds, hashes, timings, and peak RSS are saved.
```

A timeout, out-of-memory result, partial normalization, finite-field
coincidence, search bound, or surviving Mordell--Weil residue class is not a
certificate.

## Completion condition

Do not stop merely after obtaining a modular cubic, a likely elliptic curve, a
rank computation, or another partial theorem.  Continue at least until one of
these exact outcomes occurs:

```text
A. WEIERSTRASS_Q_A_TRANSPORT_CERTIFIED is obtained and committed; or
B. a precise reproducible blocker is isolated, with the smallest failing
   exact computation, input, transcript, resource usage, and a concrete next
   algorithmic route committed.
```

If outcome A occurs, immediately run the three-character Mordell--Weil sieve.
The required simultaneous square conditions are

```text
q+2 square,
q-2 square,
+V or -V square with sign tracked consistently.
```

A finite sieve proves the generic exclusion only when every sign/torsion CRT
intersection is empty.  Any surviving class is infinite and requires a
certified Chabauty, Strassmann, Prym, or height argument.

## Repository discipline

Keep the conjecture marked `OPEN` unless every admissible `2+3` point is
eliminated or an explicit counterexample is reconstructed.  Update
`CLAIMS.md`, `STATUS.md`, `HANDOFF.md`, and `paper/main.tex` conservatively.
Commit all useful scripts, compact certificates, and replay checks to the
existing branch and keep PR #1 as draft unless the full conjecture is settled.
