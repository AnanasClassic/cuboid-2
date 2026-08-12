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

There are **three** source `sorry`s:

1. `linear_quartic_impossible`;
2. `quadratic_cubic_impossible`;
3. `fiveFiveResultantFactor_ne_zero`.

The derived theorems `fiveFive_reduced_locus_empty` and
`symmetric_five_five_impossible` contain no local placeholder. No gap is
hidden behind a custom axiom.

The current execution environment cannot download or run the pinned Lean
toolchain. GitHub Actions also currently fails before allocating a runner
(`runner_id = 0`, no executed steps). Therefore the newest source changes are
pending an actual `lake build`; source presence alone is not described as
kernel verification.

## Closed factorization shell in Lean source

The following have ordinary Lean proof bodies rather than placeholders:

- reducible monic quintic `→` rational linear factor or monic `2+3` split;
- exact scaling `Q_{p,q}=scaleRoots(P_s(X^2),q^2)` and irreducibility transfer;
- reflection `X ↦ -X`, exponent doubling, contraction, and divisibility;
- symmetric-factor degree descent and exclusion of self-reflecting factors;
- the specialized quintic Capell reduction;
- the exact `1+4 / 2+3 / symmetric 5+5` classification.

Relevant files:

```text
Cuboid2/FactorizationClassification.lean
Cuboid2/Scaling.lean
Cuboid2/Capell.lean
Cuboid2/CapellDegree.lean
Cuboid2/CapellFactor.lean
Cuboid2/CapellQuintic.lean
```

## `5+5` progress

Relevant files:

```text
Cuboid2/FiveFive/Basic.lean
Cuboid2/FiveFive/Reduction.lean
Cuboid2/FiveFive/Resultant.lean
Cuboid2/FiveFive/ResultantCertificate.lean
Cuboid2/FiveFive/ResultantPolynomial.lean
Cuboid2/FiveFive/DiscriminantRoots.lean
Cuboid2/FiveFive/DiscriminantIntervals.lean
Cuboid2/FiveFive/SamplePositivity.lean
Cuboid2/FiveFive/SamplePositivityMore.lean
Cuboid2/FiveFive/SamplePositivity63.lean
Cuboid2/FiveFive/SamplePositivity317.lean
Cuboid2/FiveFive/SamplePositivity40.lean
Cuboid2/FiveFive/RootExclusion.lean
```

The source now contains:

- the exact five coefficient equations forced by a symmetric quintic factor;
- the sign-sensitive normalization `r=e/s^2`, with `r^2=s` and `e=r^5`;
- elimination to the exact normalized equations `G₂=G₃=0`;
- reciprocal transport `s ↔ 1/s`, `y ↔ z`;
- the explicit 104-term resultant factor and exact Bézout multiplication-back
  identity `U*G₂+V*G₃=resultantFactor`;
- the resultant factor grouped as an explicit degree-sixteen polynomial in
  `y`, with exact evaluation and leading-coefficient identities;
- the exact degree-six and degree-twenty-eight discriminant factors;
- a homogeneous `ZMod 7` projective certificate proving that neither
  discriminant factor has a rational root;
- exact signs at all ten rational isolating-bracket endpoints;
- exact ordering of all brackets and all seven sample parameters;
- sparse diagonally-dominant sum-of-squares certificates for `s=1/100` and
  `s=1/5`;
- exact rational positive-definite Gram/LDL sum-of-squares certificates for
  `s=4/5`, `s=2`, `s=63/2`, `s=317/10`, and `s=40`;
- strict positivity, hence absence of rational roots, for **all seven sample
  fibres** used by the pinned replay.

The remaining `5+5` placeholder is exactly:

```lean
theorem fiveFiveResultantFactor_ne_zero
    {s : ℚ} (hs : 0 < s) (hs1 : s ≠ 1) (y : ℚ) :
    fiveFiveResultantFactor s y ≠ 0
```

All sample checks and all rational endpoint checks are now represented by
explicit Lean proof terms. The remaining work is the interval-continuation
part: kernel-check the Sturm counts showing that the two discriminant factors
have exactly five positive real roots in the pinned brackets, and prove that
the number of real roots of the fibre polynomial is constant on each
complementary interval. The Python replay and its checksum remain generation
and audit aids, not proof premises.

## Gap 1 — `linear_quartic_impossible`

**Statement.** For `s>0`, `s≠1`, the normalized quintic has no rational root.

**External proof.** `research/linear_factor_completion/`, including the exact
Schaefer--Stoll rank certificate, `p=5` Coleman/Strassmann argument, and
complete quotient lift table.

**Estimated burden.** High. The explicit Mumford/Cantor and descent checker
should be shared with the `D+` block.

## Gap 2 — `quadratic_cubic_impossible`

**Statement.** For `s>0`, `s≠1`, the normalized quintic has no monic
quadratic-times-cubic factorization.

**Already represented in Lean source.** Exact remainder identities, both
physical compact equations, reciprocal character identities, the essential
factor `2`, the positive map to `D+`, two 71-term projection Bézout
certificates, boundary identities, and the abstract `p=7` integral
3-saturation argument.

**External proof.** The C012/C035/C039/C040/direct-C041 chain ending at
`research/proof_simplification_3/dplus_p3_square_abscissa.py`.

**Estimated burden.** Very high. The main subgaps are the exact
Schaefer--Stoll rank certificate and specialized `3`-adic local analysis.

## Gap 3 — `fiveFiveResultantFactor_ne_zero`

**Statement.** For positive rational `s≠1`, the explicit scalar resultant
factor has no rational zero in `y`.

**Now checked before this gap.** Both discriminant factors have no rational
roots; all isolating endpoint signs and sample placements are exact; all seven
sample fibres have direct strict sum-of-squares certificates.

**External proof.** The second script in arXiv:2601.04240, replayed by
`scripts/replay_5plus5.sh`.

**Estimated burden.** Medium. The remaining endpoint should be explicit
checked Sturm chains plus a specialized constancy lemma, not a general-purpose
real algebraic geometry stack.

## Downstream theorem bodies without local `sorry`

The following theorem bodies become axiom-clean immediately when the three
remaining gaps are discharged and the complete project builds:

- `sharipov_composition_reduction`;
- `sharipov_factorization_classification`;
- `fiveFive_reduced_locus_empty`;
- `symmetric_five_five_impossible`;
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

Development mode is expected to report `sorryAx` until the three entries
above are discharged. The project is not yet a complete formal verification.
