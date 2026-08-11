# Formalization status

Last updated: 2026-08-11.

## Completion criterion

The formalization is complete only when all of the following hold:

1. `lake build` succeeds;
2. no source file under `Cuboid2/` contains `sorry`;
3. no project-specific `axiom` or `opaque` declaration exists;
4. `#print axioms sharipov_second_cuboid_conjecture` contains no `sorryAx` and
   no project-specific mathematical axiom.

Standard mathlib foundational axioms such as classical choice, `propext`, and
quotient soundness are acceptable.

## Remaining proof gaps

There are currently **four** source `sorry`s.  They are intentionally broad
only where the existing proof still depends on substantial certificate
infrastructure; no gap is hidden behind a custom axiom.

### 1. `sharipov_factorization_classification`

**Statement.** Reducibility of the exact rational polynomial
`sharipovPolynomialQ p q`, in the admissible domain, yields one of:

- a rational linear factor of `P_s`;
- a monic quadratic times a monic cubic in `P_s`;
- a symmetric irreducible `5+5` factorization of `P_s(u^2)`.

**Why open in Lean.** The elementary degree split, invertible scaling, and
specialized Capell composition argument have not yet been connected in
mathlib.

**External proof.** `notes/factorization_classification.md`,
`paper/clean3.tex`, Proposition “Complete factorization reduction”.

**Estimated burden.** Medium.  This should require a small specialized Capell
lemma rather than general composition theory.

**Downstream dependencies.** The rational and integer final theorem.

### 2. `linear_quartic_impossible`

**Statement.** For `s>0`, `s≠1`, the normalized quintic has no rational root.

**Why open in Lean.** The exact quotient to the genus-two curve, its
Schaefer--Stoll rank certificate, the `p=5` local argument, and the complete
inverse/denominator table are not yet kernel-checked.

**External proof.** `research/linear_factor_completion/`, especially
`two_descent.py`, `two_descent_proof.md`, `chabauty_p5.py`,
`chabauty_p5_proof.md`, `quotient_map.py`, and `linear_factor_lift.py`.

**Estimated burden.** High.  It should reuse the same explicit Mumford/Cantor
and descent-certificate infrastructure as the direct `D+` block.

**Downstream dependencies.** The `1+4` branch of the final contradiction.

### 3. `quadratic_cubic_impossible`

**Statement.** For `s>0`, `s≠1`, the normalized quintic has no monic
quadratic-times-cubic factorization.

**Why open in Lean.** The signed-square lemma, compact inverse and exceptional
fibres, reciprocal transport, common-character valuation descent, direct
`p=3` square-abscissa theorem on `D+`, and exceptional lifts are not yet fully
formalized.  Several polynomial identities and the octic-to-`D+` map are
already checked in Lean.

**External proof.** The C012/C035/C039/C040/direct-C041 chain cited in
`STATUS.md`, with the recommended endpoint in
`research/proof_simplification_3/dplus_p3_square_abscissa.py`.

**Estimated burden.** Very high.  The two main subgaps are the exact
Schaefer--Stoll rank certificate and specialized `3`-adic local analysis.

**Downstream dependencies.** The `2+3` branch of the final contradiction.

### 4. `symmetric_five_five_impossible`

**Statement.** For `s>0`, `s≠1`, no symmetric irreducible `5+5`
factorization exists.

**Why open in Lean.** The seven pinned real-root exclusion obligations have
not yet been converted into Lean-checked Sturm/positivity certificates.

**External proof.** `scripts/replay_5plus5.sh` and the pinned scripts and data
it invokes.

**Estimated burden.** Medium.  Explicit checked Sturm chains or positivity
certificates should avoid a large general real-algebraic library.

**Downstream dependencies.** The `5+5` branch of the final contradiction.

## Kernel-checked declarations already downstream of the gaps

The following are ordinary Lean proofs and will become axiom-clean
immediately when the four gaps above are closed:

- `sharipovPolynomialQ_irreducible`;
- `sharipov_second_cuboid_conjecture`;
- `no_nontrivial_factorization`.

## Audit commands

```bash
grep -R -n -w sorry lean/Cuboid2
grep -R -n -E '^[[:space:]]*(axiom|opaque)[[:space:]]' lean/Cuboid2
bash scripts/reproduce_lean.sh
bash scripts/reproduce_lean.sh complete
```

The development-mode axiom audit is expected to report `sorryAx` until the
four entries above are discharged.  That output must not be described as a
completed formal verification.
