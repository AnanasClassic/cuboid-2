# Handoff

## Current low-memory state (2026-08-10)

C010, C020, and C025 remain open, but the no-high-memory pass produced three
exact advances.

First, C034 closes the entire family

    p=L^m, q=R^n, L!=R, (2/L)=(2/R)=-1.

The old endpoint systems genuinely have infinite formal survivors, so this
does not contradict the endpoint no-go.  The new proof uses the next
coefficient layer and then the **full** projection.  Elementary divisibility
closes e=2; exact positive-coefficient charts close negative e=6, both e=8
signs, and the bounded positive e=6 regions.  Replay
research/global_descent/second_endpoint_layer.py.

Second, C035 gives a lossless compact model of the full signed-square locus:

    Q_epsilon(z,k)=0, z>0, z!=1, k!=0.

Each Q_epsilon is irreducible of bidegree (16,20) with 71 terms.  The explicit
inverse y=-L0/L1 is valid at every admissible rational point; the complete
L1=0 resultant has rational z only in {-1,0,1}.  This turns the elimination
into an equivalence, but it does not classify rational points.  See
research/compact_signed_square/.

Third, C036 proves that every nontrivial product of the literal characters
q+2, q-2, and epsilon*V is ramified.  Therefore no such product can be the
unramified standard E1 2-isogeny Kummer class modulo constants and squares.
The simplest parity/Kummer identity route is closed; a later arithmetic
evaluation argument after C025 is not.

Two further shortcuts are exact no-gos.  The displayed genus-4 model has no
extra automorphism induced by independent rational Möbius changes, and the
compact Newton support has no extra Laurent-monomial symmetry beyond
reciprocity.  These statements do not exclude nonlinear automorphisms or a
Prym splitting without automorphisms.

Priority A also has a precise low-degree boundary now.  The entire family
`C=A-c, r=(q-q0)C` stays at primitive total degree 12, rational singularity
line pencils have degree at least 8, and the unique unramified rational point
over `q=6` proves that `q` cannot factor through a rational degree-2
quotient.  See
`research/arithmetic_geometry/e_model_low_degree_no_go.md`.  A birational
transport using both elliptic coordinates remains open.

Do not repeat fixed-prime sieving, lowest-endpoint reciprocity, a direct
Kummer square-class identification, or an ambient Möbius/monomial V4 search.
Any successful general local-global proof must couple different prime
divisors using more of R1=R0=0.  One factor can select different local Newton
types, so C034 does not automatically extend to multi-prime p,q.

## Earlier no-compute route (partly superseded)

The following strategy note records the starting state of this pass:
[`research/no_compute_completion/README.md`](research/no_compute_completion/README.md)

It remains useful background, but C034--C038 and the current-state section
above supersede its open-route ranking.

The no-compute pass does **not** upgrade C010, C020, or C025.  It does make one
important strategic point explicit: the present Newton-endpoint / Legendre-symbol /
`A,B`-valuation route cannot finish the general `2+3` case by itself.  Existing exact
certificates already contain infinite formal survivors of the endpoint congruences,
and they also exhibit nonuniform Newton pair types for a single rational quadratic
factor.  Any successful local-global proof must therefore use more of the full
remainder system `R1=R0=0`, or replace the normalization job by an explicit low-degree
birational/elliptic descent.

The original no-compute targets and their current outcomes are:

1. The lower-degree coordinates `C=A-2`, `r=q*C` do not directly expose a
   cubic or quartic; the primitive transformed equation still has total
   degree 12.  An unrelated explicit transport remains open.
2. The direct 2-isogeny/Kummer square-class identity is excluded by C036.
   Local evaluation after C025 remains possible.
3. The full-projection route succeeded for two inert prime powers (C034);
   coupling different types in the general multi-prime case remains open.
4. Extra ambient Möbius and monomial V4 actions are excluded by C037;
   nonlinear automorphisms or a Prym splitting remain possible.
5. Imposing the square equations early produced the exact compact model C035,
   but its admissible rational points remain unclassified.

Do not spend another pass merely enlarging a fixed-prime sieve or propagating endpoint
congruences: the repository already proves why those approaches are insufficient.

## Optional compute-machine archive

The 64--128 GiB normalization workflow is not the main route, and no new
claim depends on it.  If a persistent machine later becomes available, the
following runbook remains archival rather than required.
Use [`research/arithmetic_geometry/TRANSPORT_COMPUTE_HANDOFF.md`](research/arithmetic_geometry/TRANSPORT_COMPUTE_HANDOFF.md) as the authoritative runbook.  It records the recommended resources, exact commands, fallback normalization route, required transcript markers, acceptance criteria, and the rule that a modular or partial calculation is not a characteristic-zero certificate.

Its historical recommendation is 64 GiB RAM minimum, 128 GiB preferred,
16--32 CPU cores, and a 24--72 hour job window.  Do not make completion depend
on those resources.

## Best next theorem

The most direct low-memory completion target is now to determine all
admissible rational points on the compact curves Q_epsilon(z,k)=0.  A valid
argument must prove that every rational point is boundary, not search only to
a height bound.  The main local-global alternative is to extend C034 from two
prime powers to multi-prime p,q by finding a product formula, norm/S-unit
equation, or later-coefficient relation that couples the different local
Newton types.

An explicit low-degree characteristic-zero elliptic transport remains
valuable, but it must be derived and verified without treating the staged
high-memory normalization as the primary route.

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
- The compact model is equivalent to the signed-square locus, but its
  admissible rational points are still a genus-33-cover problem.
- C034 closes two inert prime powers, not a product of several prime powers
  carrying different local Newton types.

## Resume commands

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[test]'
PYTHON_BIN=.venv/bin/python scripts/reproduce.sh
PYTHON_BIN=.venv/bin/python scripts/replay_5plus5.sh
```

The `1+4` theorem is complete in `research/linear_factor_completion/`; a clean
Sage replay remains useful only as an archival reproducibility transcript.

The new low-memory certificates can be replayed directly:

```bash
.venv/bin/python research/global_descent/second_endpoint_layer.py
.venv/bin/python research/compact_signed_square/compact_signed_square.py \
  --output /tmp/compact_signed_square.json
.venv/bin/python research/arithmetic_geometry/character_kummer_obstruction.py \
  --output /tmp/character_kummer_obstruction.json
```

The following Riemann--Roch and rank-one block is optional archival work if a
persistent machine later exists; it is not the primary completion route:

```bash
mkdir -p run/transport
python3 research/arithmetic_geometry/e_model_singular_rr_cubic.py \
  --output run/transport/e_model_rr.sing \
  --metadata run/transport/e_model_rr_input.json
/usr/bin/time -v Singular --random=1 -q run/transport/e_model_rr.sing \
  > run/transport/e_model_rr.txt \
  2> run/transport/e_model_rr.time.txt
sage -python research/arithmetic_geometry/e_model_sage_from_singular_cubic.py \
  --transcript run/transport/e_model_rr.txt \
  --output run/transport/e_model_transport.json
sage -python research/mw_square_sieve/sage_mw_character_sieve.py \
  --transport run/transport/e_model_transport.json --prime-bound 500 \
  --output run/transport/mw_character_sieve.json
```

Do not promote the transport claim unless the exact `QQ` transcript verifies both projective compositions, round-trips `q,A,V`, and records all base loci and denominator fibers.  The required final marker is

```text
WEIERSTRASS_Q_A_TRANSPORT_CERTIFIED
```
