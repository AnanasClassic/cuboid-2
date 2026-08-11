# Lean formalization

This directory is a contained Lean 4/mathlib project for formalizing the
completed proof in `paper/clean3.tex`.

## Current status

The project is **not yet a complete formal verification**.  The exact public
theorem is present and the final proof is assembled through the three cases
`1+4`, `2+3`, and symmetric `5+5`, but four proof-critical theorems still use
temporary `sorry` placeholders.  Their exact statements and dependencies are
listed in [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md).

No project-specific `axiom` declarations are used.

## Pinned environment

- Lean: `v4.33.0`
- mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`
  (the `v4.33.0` tag)

The revision is pinned in `lakefile.toml`; the toolchain is pinned in
`lean-toolchain`.

## Public theorem

```lean
theorem sharipov_second_cuboid_conjecture
    {p q : ℕ}
    (hp : 0 < p)
    (hq : 0 < q)
    (hcop : Nat.Coprime p q)
    (hne : p ≠ q) :
    Irreducible (sharipovPolynomial p q)
```

`sharipovPolynomial p q : Polynomial ℤ` is defined coefficient-by-coefficient
from `src/symbolic_reduction.py`, rather than reconstructed from memory.

## Trusted-computing-base policy

The intended final trusted base is the Lean kernel plus mathlib.  Python,
SymPy, PARI, and Sage may generate finite certificate data, but their `PASS`
results and checksums are not proof premises.  Every imported certificate must
ultimately be checked by Lean as explicit polynomial identities, finite-field
arithmetic, matrices, group tables, valuation bounds, or local-series data.

The current kernel-checked layer includes:

- the exact normalized quintic and integer degree-ten polynomial;
- coefficient, degree, monicity, and primitivity facts;
- the pointwise weighted scaling identity;
- Gauss-lemma transfer from `Polynomial ℤ` to `Polynomial ℚ`;
- the logical three-case contradiction assembly;
- the exact octic-to-`D+` map and its square-abscissa property;
- the initial infinity-chart algebra.

The arithmetic-geometric certificate checkers remain under construction.

## Reproduction

From the repository root:

```bash
bash scripts/reproduce_lean.sh
```

This builds the project, rejects project-specific `axiom`/`opaque`
declarations, reports every remaining `sorry`, and prints the axiom audit for
the public theorem.

The strict completion gate is:

```bash
bash scripts/reproduce_lean.sh complete
```

It additionally fails if any source `sorry` remains or if the final axiom
audit contains `sorryAx`.

Directly inside this directory:

```bash
lake build
lake env lean Cuboid2/AxiomAudit.lean
```

## Source layout

- `Cuboid2/Polynomial.lean`: exact polynomials, scaling, degree, Gauss transfer.
- `Cuboid2/Factorization.lean`: precise definitions of the three cases.
- `Cuboid2/DPlus/Basic.lean`: exact algebra on the direct genus-two route.
- `Cuboid2/Main.lean`: public theorem and contradiction assembly.
- `Cuboid2/AxiomAudit.lean`: `#check` and `#print axioms` audit.

Future certificate generators will remain outside the Lean checker or under a
clearly labelled generation directory.  Generated data is never accepted only
because its external checksum matches.
