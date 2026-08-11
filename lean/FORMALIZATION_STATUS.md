# Formalization status

Last updated: 2026-08-12.

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

There are now **three** source `sorry`s:

1. `linear_quartic_impossible`;
2. `quadratic_cubic_impossible`;
3. `symmetric_five_five_impossible`.

The former fourth gap, the complete factorization-classification/Capell shell,
has been replaced by explicit Lean source with no local `sorry`.  No gap is
hidden behind a custom axiom.

Because the current execution environment cannot run Lean, the newly added
algebraic files are **pending an actual `lake build`**.  They must not yet be
described as kernel-checked merely because their source is present.

## Closed algebraic shell in Lean source

The following declarations now contain ordinary Lean proof terms rather than
placeholders:

- `monic_quintic_reducible_cases`: a reducible monic quintic has a rational
  linear factor or a monic quadratic factor with monic cubic quotient;
- `normalizedQuintic_reducible_cases`: specialization to `P_s`;
- `sharipovPolynomialQ_eq_scaleRoots`: exact polynomial identity
  `Q_{p,q}=scaleRoots(P_s(X^2),q^2)`;
- `irreducible_scaleRoots_iff`: nonzero root scaling preserves and reflects
  irreducibility;
- the reflection involution `X ↦ -X`, including preservation of divisibility,
  units, irreducibility, and degree;
- `expand_contract_two_of_reflectPolynomial_eq`: every reflection-fixed
  polynomial is exactly a polynomial in `X^2`;
- contraction of `R(X)R(-X)` to a divisor of the original polynomial;
- the symmetric-factor degree descent;
- exclusion of an irreducible factor associated to its own reflection;
- `normalizedEven_capell_reduction`: the specialized Capell implication for
  an irreducible quintic;
- `sharipov_factorization_classification`: the exact `1+4 / 2+3 / 5+5`
  classification used by the final theorem.

These files are:

```text
Cuboid2/FactorizationClassification.lean
Cuboid2/Scaling.lean
Cuboid2/Capell.lean
Cuboid2/CapellDegree.lean
Cuboid2/CapellFactor.lean
Cuboid2/CapellQuintic.lean
```

## Gap 1 — `linear_quartic_impossible`

**Statement.** For `s>0`, `s≠1`, the normalized quintic has no rational root.

**Why open in Lean.** The exact quotient to the genus-two curve, its
Schaefer--Stoll rank certificate, the `p=5` local argument, and the complete
inverse/denominator table are not yet kernel-checked.

**External proof.** `research/linear_factor_completion/`, especially
`two_descent_rank.py`, `two_descent_proof.md`, `sage_chabauty_p5.py`,
`chabauty_p5_proof.md`, and `exact_prerequisites.py`.

**Estimated burden.** High.  It should reuse the explicit Mumford/Cantor and
descent-certificate infrastructure also needed for `D+`.

## Gap 2 — `quadratic_cubic_impossible`

**Statement.** For `s>0`, `s≠1`, the normalized quintic has no monic
quadratic-times-cubic factorization.

**Why open in Lean.** The signed-square theorem, compact inverse and exceptional
fibres, reciprocal transport, common-character valuation descent, direct
`p=3` square-abscissa theorem on `D+`, and exceptional lifts are not yet fully
formalized.

**Already represented in Lean source.** Exact quadratic remainder identities,
both physical compact equations, reciprocal character identities, the
essential factor `2` in the cleared `E1` identity, the positive map to `D+`,
both 71-term projection Bézout certificates, boundary-fibre identities, and
the abstract `p=7` integral 3-saturation argument.

**External proof.** The C012/C035/C039/C040/direct-C041 chain cited in
`STATUS.md`, ending at
`research/proof_simplification_3/dplus_p3_square_abscissa.py`.

**Estimated burden.** Very high.  The main subgaps are the exact
Schaefer--Stoll rank certificate and the specialized `3`-adic local analysis.

## Gap 3 — `symmetric_five_five_impossible`

**Statement.** For `s>0`, `s≠1`, no symmetric irreducible `5+5`
factorization exists.

**Why open in Lean.** The seven pinned real-root exclusion obligations have
not yet been converted into Lean-checked Sturm or positivity certificates.

**External proof.** `scripts/replay_5plus5.sh` and the pinned scripts/data it
invokes.

**Estimated burden.** Medium.  Explicit checked Sturm chains or positivity
certificates should avoid a large general real-algebraic library.

## Downstream theorem bodies without local `sorry`

The following theorem bodies become axiom-clean immediately when the three
remaining gaps are discharged and the complete project builds:

- `sharipov_composition_reduction`;
- `sharipov_factorization_classification`;
- `sharipovPolynomialQ_irreducible`;
- `sharipov_second_cuboid_conjecture`;
- `no_nontrivial_factorization`.

## Validation limitation in the current environment

GitHub Actions did not start because the repository owner's Actions billing
or spending-limit state prevented job allocation.  The current execution
environment has no installed Lean binary and cannot resolve outbound package
hosts, so it cannot install the pinned toolchain.  Consequently the new
commits were source-audited against the exact pinned mathlib revision, but
must still pass:

```bash
cd lean
lake build
```

before any compiling milestone is claimed.

## Audit commands

```bash
grep -R -n -w sorry lean/Cuboid2
grep -R -n -E '^[[:space:]]*(axiom|opaque)[[:space:]]' lean/Cuboid2
bash scripts/reproduce_lean.sh
bash scripts/reproduce_lean.sh complete
```

Development mode is expected to report `sorryAx` until the three entries
above are discharged.  The project is not yet a complete formal verification.
