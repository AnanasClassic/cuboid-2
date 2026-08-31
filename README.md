# Sharipov's second cuboid conjecture

[![Lean formalization](https://github.com/AnanasClassic/cuboid-2/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/AnanasClassic/cuboid-2/actions/workflows/lean.yml)

This repository contains a computer-assisted proof and a complete Lean 4
formalization of Sharipov's second cuboid conjecture. For coprime positive
integers $p\ne q$, the polynomial $Q_{p,q}(t)$ below is irreducible over
$\mathbb{Z}$, or equivalently over $\mathbb{Q}$.

$$
Q_{p,q}(t)=q^{20}P_s\!\left(\frac{t^2}{q^4}\right),
\qquad s=\left(\frac pq\right)^2,
$$

where

$$
\begin{aligned}
P_s(x)={}&x^5+(2+s)(3-2s)x^4 \\
&+(1+10s+4s^2-14s^3+s^4)x^3 \\
&-s(1-14s+4s^2+10s^3+s^4)x^2 \\
&-s^3(1+2s)(-2+3s)x-s^5.
\end{aligned}
$$

## Status

The conjecture is proved. The public Lean theorem is
[`Cuboid2.sharipov_second_cuboid_conjecture`](lean/Cuboid2/Main.lean):

```lean
theorem sharipov_second_cuboid_conjecture
    {p q : ℕ}
    (hp : 0 < p)
    (hq : 0 < q)
    (hcop : Nat.Coprime p q)
    (hne : p ≠ q) :
    Irreducible (sharipovPolynomial p q)
```

The Lean source contains no `sorry` and no project-specific mathematical
`axiom` or `opaque` declaration. The axiom audit for the public theorem has
no `sorryAx`. Its documented trust base includes Lean, mathlib, and the
native evaluator used by `native_decide` for closed finite computations.
See [the formalization status](lean/FORMALIZATION_STATUS.md) for the exact
completion criteria and audit.

The proof is exact: it uses symbolic identities, certified finite
calculations, number-field arithmetic, descent, and local arguments. It does
not infer completeness from a bounded-height search or a probabilistic
calculation.

## Start here

- [Lean formalization](lean/README.md) — build instructions, trust model, and
  source map.
- [`paper/clean3.tex`](paper/clean3.tex) — the recommended concise
  mathematical proof.
- [Formalization status](lean/FORMALIZATION_STATUS.md) — the precise Lean
  completion and axiom audit.
- [Claim ledger](CLAIMS.md) and [research status](STATUS.md) — detailed
  dependencies and independently replayable arithmetic evidence.
- [Research archive](research/README.md) — certificate generators,
  alternative routes, and historical investigations.

The Lean development proves the same final irreducibility theorem as the
paper, but it is not a line-by-line transcription: its three factorization
branches use specialized proof structures chosen for formal verification.

## Verify the Lean proof

The project pins Lean 4.33.0 and mathlib at
`db584cd6d46c92f209a44c0f1c829460d327499d`. With
[`elan`](https://github.com/leanprover/elan) installed and `lake` available
on `PATH`, run from the repository root:

```bash
bash scripts/reproduce_lean.sh complete
```

This builds the project, rejects source placeholders and project-specific
axioms, prints the axiom set of the public theorem, and rejects anything
outside the documented foundational and `native_decide` allowlist. The
equivalent manual commands are:

```bash
cd lean
lake build
lake env lean Cuboid2/AxiomAudit.lean
```

## Build the concise paper

The recommended paper builds with Tectonic 0.17.0:

```bash
mkdir -p build/paper
tectonic --outdir build/paper paper/clean3.tex
```

## Replay the external arithmetic

The Python/SymPy/PARI suite is independent audit material; its output is not
accepted as an unchecked premise by Lean. A full replay requires Python 3.11
or newer and the system libraries needed by `cypari2`.

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[test]'
PYTHON_BIN=.venv/bin/python bash scripts/reproduce.sh
PYTHON_BIN=.venv/bin/python bash scripts/replay_5plus5.sh
```

## Repository layout

| Path | Contents |
|---|---|
| [`lean/`](lean/) | Lean project and the public theorem |
| [`paper/`](paper/) | concise and full mathematical expositions |
| [`src/`](src/) | reusable exact-computation code |
| [`tests/`](tests/) | regression tests for external certificates |
| [`artifacts/`](artifacts/) and [`certificates/`](certificates/) | checked exact data |
| [`research/`](research/) | supporting generators, audits, and superseded routes |

## Scope

This result concerns an intermediate irreducibility conjecture arising in
the perfect-cuboid program. It does **not** prove or disprove the existence of
a perfect cuboid.
