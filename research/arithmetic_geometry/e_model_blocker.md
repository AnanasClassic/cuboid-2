# Exact Weierstrass-model computation: execution blocker

Status recorded at 2026-08-04 23:41 UTC. This is a resource/API blocker for
the present execution environment, not a mathematical nonexistence claim.

## Locally available exact systems

The following read-only checks all returned no executable:

```text
command -v sage
command -v Singular
command -v gp
command -v docker
command -v podman
```

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

## Prepared bypass

`e_model_sage_transport.py` avoids `FunctionField.genus()` and emits a
certificate after each stage. In particular,

```bash
sage -python research/arithmetic_geometry/e_model_sage_transport.py \
  --stop-after descent --stage-timeout 1200
```

first computes `V` in the degree-eight function field as the relative trace
of its expression on `T^4-q*T^2+1`, divided by four. This stage runs before
`monic_integral_model()` or any maximal-order computation. The full run then
uses the rational smooth point `(q,A)=(6,6/7)`, constructs `L(2P)` and `L(3P)`,
exports the cubic and Weierstrass maps, and represents `q`, `A`, and `V` in the
Riemann--Roch coordinates.

The script has passed Python syntax compilation and whitespace checks, but it
has not been executed under Sage in this environment. Therefore the explicit
Weierstrass equation and transported functions remain `OPEN`; the script is a
reproducible next computation, not a completed certificate.

### First staged Sage 10.9 feedback

Run `30962036989`, jobs `92167849754` and `92167849779`, reached the degree-8
field construction in under 0.1 seconds and certified that `H` is irreducible
and vanishes at `(6,6/7)`. Both then failed after 0.006 seconds at an auxiliary
call to `is_irreducible()` for `T^4-q*T^2+1`: Sage attempted to send a
polynomial ring over an algebraic function field to Singular, for which no
conversion exists, and raised `NotImplementedError`. This is an API limitation,
not evidence of reducibility. The unsupported call has been removed; degree
four/connectedness is supplied by the independent branch-divisor certificate,
while the trace descent still requires an exact coercion round-trip.

The same run also confirms that the generic normalization was not the cause of
this particular fast failure. A rerun of the patched staged script is required.

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
