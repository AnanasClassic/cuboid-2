# Exact Weierstrass-model computation: execution blocker

Status updated at 2026-08-06.

## Current operational status

The immediate unresolved task is an exact characteristic-zero transport from
the normalization of `H(q,A)=0` to a Weierstrass model, with `q`, `A`, and `V`
transported and both projective compositions verified.  The full execution
contract is now in

```text
research/arithmetic_geometry/TRANSPORT_COMPUTE_HANDOFF.md
```

A copy-paste task specification for a compute-machine agent is in

```text
research/arithmetic_geometry/COMPUTE_AGENT_PROMPT.md
```

Recommended resources are 64 GiB RAM minimum, 128 GiB preferred, 16--32 CPU
cores, 50 GiB scratch, and an uninterrupted 24--72 hour window.  This is a
CPU/RAM exact-algebra workload; a GPU is not useful.  SageMath and Singular are
required, with Magma useful as an independent cross-check.

This remains an execution-resource and exact-CAS blocker.  It is not evidence
that the elliptic transport does not exist, and no partial or modular output is
a proof.

## Locally available exact systems in the earlier environment

The following read-only checks initially returned no executable:

```text
command -v sage
command -v Singular
command -v gp
command -v docker
command -v podman
```

A temporary SageMath/Singular runtime was later assembled and used for
exploratory characteristic-zero and finite-field calculations.  Those local
outputs must be replayed on the persistent machine and committed with their
inputs, hashes, versions, and full transcripts before they are promoted to
repository claims.

The repository virtual environment contains SymPy 1.14.0. It verifies the
plane identities and discriminant factorization, but it has no function-field
normalization, Riemann--Roch, Prym-rank, or elliptic-curve Mordell--Weil
implementation suitable for this proof.

## Existing exact Sage jobs

Two Sage 10.8 GitHub Actions routes were independently started from the same
tree:

| Route | Run | Job | Last observed step state |
|---|---:|---:|---|
| degree-10 model over `QQ(q)` | 30956636310 | 92151142435 | `Normalize quotient and compute exact elliptic data`: `in_progress` |
| degree-8 model over `QQ(A)` | 30956636300 | 92151142330 | `Compute genus in the degree-eight presentation`: `in_progress` |

At the recorded time, both setup, container, checkout and Sage-version steps
had succeeded. Neither mathematical step had completed. Attempts to fetch the
running job logs through the connected GitHub API returned HTTP 404
`BlobNotFound`; GitHub only exposed the log blob after job completion. Thus no
partial CAS output is being promoted to a certificate.

## Prepared direct route

`e_model_singular_rr_cubic.py` avoids the stalled maximal-order computation.
It constructs `L(2P)` and `L(3P)` from the singular projective model using
Singular's Brill--Noether machinery, constructs the cubic, calls
`invertBirMap`, and checks both projective compositions.  The companion
`e_model_sage_from_singular_cubic.py` converts the cubic to a Weierstrass
model and transports `q,A`.

Run the direct route exactly as documented in
`TRANSPORT_COMPUTE_HANDOFF.md`.  The transport claim may be promoted only after
an exact `QQ` transcript reaches all required composition markers and the
companion Sage stage verifies the maps, function round-trips, and exceptional
fibers.

## Prepared fallback

If the direct Riemann--Roch route stalls, use the lower-degree affine model
obtained from

```text
C = A - 2,
r = q*C.
```

Compute the exact affine normalization `U/d` of `QQ[r,C]/(J)`, add the points
at infinity, identify a rational point, and compute `L(2P)` and `L(3P)` on the
normalization.  Modular normalizations are discovery tools only.  Any CRT or
rational reconstruction must be checked over `QQ` before use.

The required final marker is

```text
WEIERSTRASS_Q_A_TRANSPORT_CERTIFIED
```

and its acceptance conditions are enumerated in the runbook.  Do not emit it
for a modular cubic, a likely isogeny class, a rank computation, a timeout, or
a partial normalization.

## Independently completed exact triage

`e_model_plane_discriminant.py` verifies in exact arithmetic that
`(6,6/7)` is a smooth rational point of `H`, and that `Disc_A(H)` has six
pairwise-coprime irreducible factors with `(degree, exponent)`

```text
(1,27), (1,20), (1,4), (2,12), (3,3), (15,2).
```

Hence the direct degree-ten `q`-map is not a three-branch-point/Belyi shortcut.
Plane discriminant exponents are not treated as normalization ramification
indices.
