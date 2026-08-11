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

There are currently **four** source `sorry`s.  The elementary factorization
classification and the complete weighted scaling from `Q_{p,q}` to
`P_s(u^2)` are now represented by ordinary Lean proofs.  The former broad
factorization-shell gap has therefore been reduced to the single specialized
Capell implication below.

No gap is hidden behind a custom axiom.

### 1. `normalizedEven_capell_reduction`

**Statement.** If `P_s(u^2)` is reducible, then either `P_s` itself is
reducible or the composition has a symmetric irreducible `5+5`
factorization.

**Already formalized downstream.**

- `monic_quintic_reducible_cases` proves that a reducible monic quintic has a
  rational linear factor or a monic quadratic factor with monic cubic
  quotient.
- `normalizedQuintic_reducible_cases` specializes this to `P_s`.
- `sharipovPolynomialQ_eq_scaleRoots` proves the exact polynomial identity
  `Q_{p,q}=scaleRoots(P_s(u^2),q^2)`.
- `irreducible_scaleRoots_iff` proves that nonzero root scaling preserves and
  reflects irreducibility.
- `sharipov_factorization_classification` is therefore now an ordinary Lean
  proof conditional only on the specialized Capell statement.

**Why open in Lean.** Mathlib does not currently expose the exact specialized
Capell composition theorem required here.  The remaining task is to pass to
a root `α` of irreducible `P_s`, show that reducibility of `u^2-α` is
squarehood of `α` in `ℚ(α)`, and reconstruct the symmetric degree-five
minimal polynomial of a square root.

**External proof.** `notes/factorization_classification.md`,
`paper/clean3.tex`, Proposition “Complete factorization reduction”.

**Estimated burden.** Medium.  This should remain a specialized field-quotient
argument rather than a general formalization of Capell's theorem.

**Downstream dependencies.** The rational and integer final theorem.

### 2. `linear_quartic_impossible`

**Statement.** For `s>0`, `s≠1`, the normalized quintic has no rational root.

**Why open in Lean.** The exact quotient to the genus-two curve, its
Schaefer--Stoll rank certificate, the `p=5` local argument, and the complete
inverse/denominator table are not yet kernel-checked.

**External proof.** `research/linear_factor_completion/`, especially
`two_descent_rank.py`, `two_descent_proof.md`, `sage_chabauty_p5.py`,
`chabauty_p5_proof.md`, and `exact_prerequisites.py`.

**Estimated burden.** High.  It should reuse the same explicit Mumford/Cantor
and descent-certificate infrastructure as the direct `D+` block.

**Downstream dependencies.** The `1+4` branch of the final contradiction.

### 3. `quadratic_cubic_impossible`

**Statement.** For `s>0`, `s≠1`, the normalized quintic has no monic
quadratic-times-cubic factorization.

**Why open in Lean.** The signed-square theorem, compact inverse and exceptional
fibres, reciprocal transport, common-character valuation descent, direct
`p=3` square-abscissa theorem on `D+`, and exceptional lifts are not yet fully
formalized.

**Already kernel-checked in this branch.** The exact quadratic remainder
identities, both physical compact equations, reciprocal character identities,
the essential factor `2` in the cleared `E1` character identity, positive
map to `D+`, both 71-term projection Bézout certificates, boundary-fibre
identities, and the abstract `p=7` integral 3-saturation argument.

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

- `sharipov_composition_reduction`;
- `sharipov_factorization_classification`;
- `sharipovPolynomialQ_irreducible`;
- `sharipov_second_cuboid_conjecture`;
- `no_nontrivial_factorization`.

## Validation limitation in the current environment

GitHub Actions did not start because of the repository owner's Actions billing
state.  The current execution environment also has no installed Lean binary
and no outbound package download.  Therefore new commits are source-audited
against the pinned mathlib API but must still pass an actual `lake build`
before any milestone is called compiling.

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
