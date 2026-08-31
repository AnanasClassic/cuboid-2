# Lean formalization

This directory is a self-contained Lean 4/mathlib project proving the
irreducibility theorem stated in the [repository README](../README.md).

## Completion status

The formalization is complete under the trust model below. The public theorem
is assembled from the `1+4`, `2+3`, and symmetric `5+5` cases, and the source
contains:

- no `sorry`;
- no project-specific mathematical `axiom` declaration;
- no project-specific `opaque` declaration;
- no `sorryAx` in the axiom audit of the public theorem.

The full build and strict audit are run by
[the Lean CI workflow](../.github/workflows/lean.yml). Exact completion
criteria and the detailed module inventory are recorded in
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md).

## Public theorem

[`Cuboid2/Main.lean`](Cuboid2/Main.lean) exports:

```lean
theorem sharipov_second_cuboid_conjecture
    {p q : ℕ}
    (hp : 0 < p)
    (hq : 0 < q)
    (hcop : Nat.Coprime p q)
    (hne : p ≠ q) :
    Irreducible (sharipovPolynomial p q)
```

The polynomial `sharipovPolynomial p q : Polynomial ℤ` is defined
coefficient-by-coefficient in [`Cuboid2/Polynomial.lean`](Cuboid2/Polynomial.lean).
The formalization proves its irreducibility over `ℤ` by first proving the
corresponding rational statement and then applying the formalized Gauss
transfer.

## Trust model

The theorem is checked by Lean against the pinned mathlib revision. Its axiom
audit contains the standard foundational axioms used by mathlib and the
closed-computation extension introduced by `native_decide`; it contains
neither `sorryAx` nor a project-defined mathematical assumption.

`native_decide` is used for explicit finite calculations, primarily in the
`2+3` branch. The `1+4` and symmetric `5+5` completions do not add that
dependency. Python, SymPy, PARI, Sage, JSON status fields, and external
checksums are not proof premises. They were used to generate or independently
replay data that Lean checks as concrete identities, finite arithmetic,
matrices, group tables, valuation bounds, or local-series statements.

## Pinned environment

- Lean: `v4.33.0`
- mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`
  (the `v4.33.0` tag)

The toolchain is pinned in [`lean-toolchain`](lean-toolchain), mathlib is
pinned in [`lakefile.toml`](lakefile.toml), and the complete transitive Lake
dependency graph is recorded in
[`lake-manifest.json`](lake-manifest.json).

## Reproduce

Install [`elan`](https://github.com/leanprover/elan), ensure `lake` is on
`PATH`, and run from the repository root:

```bash
bash scripts/reproduce_lean.sh complete
```

The script builds the project, rejects project-specific `axiom`/`opaque`
declarations and source placeholders, prints the public theorem's axiom set,
and fails on `sorryAx` or any axiom outside the documented foundational and
`native_decide` allowlist.

The equivalent commands from this directory are:

```bash
lake build
lake env lean Cuboid2/AxiomAudit.lean
```

## Proof structure

- [`Cuboid2/Polynomial.lean`](Cuboid2/Polynomial.lean): exact integer and
  rational polynomials, coefficient facts, and Gauss transfer.
- [`Cuboid2/Scaling.lean`](Cuboid2/Scaling.lean): weighted root scaling from
  $Q_{p,q}$ to the normalized even polynomial.
- [`Cuboid2/FactorizationClassification.lean`](Cuboid2/FactorizationClassification.lean)
  and the `Capell*.lean` modules: the exhaustive `1+4`, `2+3`, and symmetric
  `5+5` classification.
- [`Cuboid2/LinearQuartic/`](Cuboid2/LinearQuartic/): the specialized `1+4`
  completion.
- [`Cuboid2/QuadraticReduction/`](Cuboid2/QuadraticReduction/): the
  unconditional Gaussian/octic completion of `2+3`.
- [`Cuboid2/FiveFive/`](Cuboid2/FiveFive/): exact real-algebra root exclusion
  closing symmetric `5+5`.
- [`Cuboid2/Main.lean`](Cuboid2/Main.lean): final case split and public theorem.
- [`Cuboid2/AxiomAudit.lean`](Cuboid2/AxiomAudit.lean): `#check` and
  `#print axioms` audit.

Additional `DPlus/`, `Genus2/`, and certificate modules preserve reusable
infrastructure and independently checked arithmetic developed along the way.
