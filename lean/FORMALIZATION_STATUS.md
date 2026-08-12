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
3. `fiveFive_reduced_locus_empty`.

The public theorem `symmetric_five_five_impossible` itself no longer contains
a placeholder: it is deduced from the normalized two-equation root-exclusion
theorem.  No gap is hidden behind a custom axiom.

Because the current execution environment cannot run Lean, all recent algebraic
files are **pending an actual `lake build`** and must not yet be described as
kernel-checked merely because their source is present.

## Closed factorization shell in Lean source

The following now have ordinary Lean proof bodies rather than placeholders:

- reducible monic quintic `→` rational linear factor or monic `2+3` split;
- exact polynomial scaling
  `Q_{p,q}=scaleRoots(P_s(X^2),q^2)` and irreducibility transfer;
- reflection `X ↦ -X`, exponent doubling, contraction, and divisibility;
- symmetric-factor degree descent;
- exclusion of self-reflecting irreducible factors;
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

The algebra before the published real-root certificate is now isolated in:

```text
Cuboid2/FiveFive/Basic.lean
Cuboid2/FiveFive/Reduction.lean
Cuboid2/FiveFive/RootExclusion.lean
```

The new source contains:

- exact multiplication of
  `R(X)=X^5+aX^4+bX^3+cX^2+dX+e` by `-R(-X)`;
- extraction of all five scalar coefficient equations from a
  `SymmetricFiveFiveCase`;
- the sign-sensitive normalization
  `r=e/s^2`, proving `r^2=s` and `e=r^5` for `s>0`;
- elimination of `b,c` and exact cleared equations `E₂=E₃=0`;
- normalization `a=r y`, `d=r^4 z` and the two published equations
  `G₂(s,y,z)=G₃(s,y,z)=0`;
- exact reciprocal identities exchanging `s` with `1/s` and `y` with `z`;
- a proof that every symmetric factorization yields a rational point on this
  normalized locus.

Thus the only remaining `5+5` gap is now:

```lean
theorem fiveFive_reduced_locus_empty
    {s : ℚ} (hs : 0 < s) (hs1 : s ≠ 1) :
    ¬ Nonempty (FiveFiveReducedPoint s)
```

Its final implementation must check the seven pinned Sturm/positivity
obligations in Lean.  The Python replay and its checksum are generation and
audit aids, not proof premises.

## Gap 1 — `linear_quartic_impossible`

**Statement.** For `s>0`, `s≠1`, the normalized quintic has no rational root.

**External proof.** `research/linear_factor_completion/`, including the exact
Schaefer--Stoll rank certificate, `p=5` Coleman/Strassmann argument, and
complete quotient lift table.

**Estimated burden.** High.  The explicit Mumford/Cantor and descent checker
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

**Estimated burden.** Very high.  The main subgaps are the exact
Schaefer--Stoll rank certificate and specialized `3`-adic local analysis.

## Gap 3 — `fiveFive_reduced_locus_empty`

**Statement.** The normalized two-equation `5+5` locus has no rational point
for positive `s≠1`.

**External proof.** The second script in arXiv:2601.04240, replayed by
`scripts/replay_5plus5.sh`.

**Estimated burden.** Medium.  The preferred endpoint is explicit checked
Sturm chains or smaller positivity certificates, not a general-purpose real
algebraic geometry stack.

## Downstream theorem bodies without local `sorry`

The following theorem bodies become axiom-clean immediately when the three
remaining gaps are discharged and the complete project builds:

- `sharipov_composition_reduction`;
- `sharipov_factorization_classification`;
- `symmetric_five_five_impossible`;
- `sharipovPolynomialQ_irreducible`;
- `sharipov_second_cuboid_conjecture`;
- `no_nontrivial_factorization`.

## Validation limitation

GitHub Actions did not start because the repository owner's Actions billing
or spending-limit state prevented job allocation.  The current execution
environment has no installed Lean binary and cannot install the pinned
external toolchain.  The commits were source-audited against the exact pinned
mathlib revision, but must still pass:

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
