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

Sharipov states the conjecture in Conjecture 5.2, equation (5.13), and restates it as Conjecture 1.1, equation (1.1). [Sharipov, 2011, p. 6](https://arxiv.org/pdf/1108.5348v1#page=6) · [Sharipov, 2012, p. 1](https://arxiv.org/pdf/1201.1229v1#page=1)

## Status

The Lean theorem for the conjecture is
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
- [`paper/sharipov.tex`](paper/sharipov.tex) — the mathematical proof,
  with a map from statements to Lean declarations (older drafts are in
  `paper/archive/`).
- [Formalization status](lean/FORMALIZATION_STATUS.md) — the precise Lean
  completion and axiom audit.
- [Claim ledger](CLAIMS.md) and [research status](STATUS.md) — detailed
  dependencies and independently replayable arithmetic evidence.
- [Research archive](research/README.md) — certificate generators,
  alternative routes, and historical investigations.

The paper follows the three branches of the Lean proof. The research archive also preserves alternative arguments for the quadratic-factor branch.

## Manuscript and related work

Vladislav Kuznetsov is the scientific author. The manuscript gives the arithmetic route used by the Lean development. Its quadratic-factor argument reduces to the rational points of an octic curve and uses descent over the Gaussian rationals and a formal-group calculation at the split prime 37. The historical paper revision records AI assistance in its Git co-authorship trailer. [Manuscript PDF](paper/sharipov.pdf) · [TeX source](paper/sharipov.tex) · [Citation metadata](CITATION.cff)

Valery Asiryan's October 2026 preprint gives a rank-one Chabauty–Coleman argument for the broader classification over every rational parameter outside $\{0,1,-1\}$. The Lean theorem here treats the classical cuboid parameters $s=(p/q)^2$. The September manuscript cites Asiryan’s earlier work and his joint computational study with Randall L. Rathbun. [Asiryan, v2](https://arxiv.org/abs/2610.25319v2) · [Asiryan and Rathbun](https://arxiv.org/abs/2601.07899)

GitHub recorded a successful formal build and axiom audit on 2 September 2026 at 20:31:18 UTC while this repository was private. The manuscript revision was pushed on 4 September. [Chronology and evidence](PRIORITY_EVIDENCE.md) · [Reproduction at the historical revision](REPRODUCIBILITY.md)

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
outside the documented foundational and `native_decide` allowlist. To inspect the compiled project and print the axiom lists manually, run the following commands. The strict script above also checks its allowlist and source restrictions.

```bash
cd lean
lake build
lake env lean Cuboid2/AxiomAudit.lean
```

## Build the concise paper

The paper builds with pdflatex:

```bash
cd paper && pdflatex sharipov.tex && pdflatex sharipov.tex
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

## License

Original code is available under Apache-2.0. The manuscript and its PDF are available under CC BY 4.0. [Scope and license texts](LICENSE.md)
