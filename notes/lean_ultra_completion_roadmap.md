# Lean Ultra completion roadmap

This is the historical operational roadmap used to complete the Lean proof
under the trust model documented in `lean/FORMALIZATION_STATUS.md`.

**Completion note (2026-08-31).** All four sessions are complete. The source
`sorry` count is zero, the project-specific `axiom`/`opaque` count is zero,
`lake build` passes, and `bash scripts/reproduce_lean.sh complete` passes.
Session 2 was ultimately closed by a theorem specialized to
`s=(p/q)²`: signed-square root valuations, signed-square inverse-slope
transport, a Fermat descent for the positive cover, and a joint 3-adic
argument for the negative cover. The generic arbitrary-`s` Chabauty route
below remains historical planning material and is not a dependency.

## Historical baseline

- Repository: `AnanasClassic/cuboid-2`
- Branch: `formalization/lean`
- Draft PR: [#7](https://github.com/AnanasClassic/cuboid-2/pull/7)
- Last build verified while preparing this roadmap: `lake build` PASS
  (`8765` jobs)
- Baseline before the roadmap commit: `7bcce60`
- Source `sorry` count: `3`
- Project-specific `axiom` / `opaque` count: `0`

The three remaining source gaps are:

1. `FiveFive/RootExclusion.lean`: exact real-algebra/root-exclusion
   certificate;
2. `Main.lean`: `linear_quartic_impossible`;
3. `Main.lean`: `quadratic_cubic_impossible`.

Do not interpret the small `sorry` count as three small lemmas.  The remaining
statements contain the global arithmetic-geometry closures.

## Session 1 (closed): `2+3`

Work from the already checked signed-square, compact, reciprocal,
common-character, valuation, finite-group and local-series modules.

Required work:

1. Check the inverse `C8 -> E1` subresultant certificate and every exceptional
   denominator fibre from
   `research/arithmetic_geometry/low_degree_transport.json`.
2. Implement only the specialized Cantor/Jacobian arithmetic needed to
   identify the checked rational Mumford pair with `11D`.
3. Instantiate the global rank/torsion/3-saturation interface for `D+`.
4. Check the direct `p=3` Coleman/Strassmann certificate in the four relevant
   residue disks.
5. Prove the square-abscissa classification, exceptional lifts, and a theorem
   specialized to `sharipovParameter p q`.
6. Replace the `quadratic_cubic_impossible` placeholder in final assembly.

Definition of done:

- the `2+3` branch contains no `sorry`;
- `lake build` passes;
- the source `sorry` count falls from `3` to `2`;
- one logically complete commit is pushed to `formalization/lean`.

Do not build a generic arithmetic-geometry library.  Store explicit
certificates and make Lean check their polynomial, finite-field, group-law and
valuation identities.

## Session 2 (closed): `1+4`

Reuse the checked modules in `LinearQuartic`, especially finite counts, local
`p=5` series, descent tables and `DescentCompletion`.

Required work:

1. Construct the actual Schaefer--Stoll bridge: maximal-order/class-unit
   completeness, Kummer map, local images and good/tame-prime completeness.
2. Connect the exact finite tables to the Jacobian and prove the required
   Selmer bound and Mordell--Weil rank statement.
3. Check the Coleman annihilator `(1+t) dt/(2w)` at `p=5`.
4. Close all ordinary disks, infinity, and the exceptional point `(-1,0)`
   using the stored series and a specialized Strassmann lemma.
5. Verify the complete inverse/lift table and prove
   `linear_quartic_impossible`.

Definition of done:

- the `1+4` branch contains no `sorry`;
- `lake build` passes;
- the source `sorry` count falls by one;
- one logically complete commit is pushed.

Finite tables alone are not a global completeness theorem.  Do not leave the
existing bridge structure as an assumption: construct its instance for the
actual curve.

## Session 3 (closed): `5+5`

The existing algebraic reduction and resultant machinery should be reused.
The missing endpoint is an exact real-algebra certificate.

Certificate strategy:

1. Give exact rationalization/facial reduction of the current singular SOS
   candidate only a bounded attempt.
2. If no exact positive-semidefinite Gram certificate emerges, switch to the
   pinned subresultant/Sturm continuation route.
3. In the Sturm route, check:
   - the link from the displayed discriminant factors to the resultant;
   - exact P6/P28 root isolation;
   - absence/classification of common roots;
   - constancy of the real-root count between critical parameters;
   - endpoint and reciprocal cases.
4. Encode every coefficient and sign certificate as explicit rational data
   checked by Lean.

Definition of done:

- `symmetric_five_five_impossible` has no `sorry`;
- `lake build` passes;
- the final mathematical source `sorry` disappears;
- one logically complete commit is pushed.

Numerical SDP output is discovery data, not a proof premise.  Do not commit a
floating-point tolerance claim or a new abstract bridge assumption.

## Session 4 (closed): final integration and audit

1. Ensure final assembly uses the specialized `p,q` theorem for `2+3`; the
   current overly general placeholder must not survive.
2. Run:

   ```bash
   cd lean
   lake build
   lake env lean Cuboid2/AxiomAudit.lean

   cd ..
   grep -R -n -w sorry lean/Cuboid2
   grep -R -n -E '^[[:space:]]*(axiom|opaque)[[:space:]]' lean/Cuboid2
   bash scripts/reproduce_lean.sh complete
   ```

3. Inspect `#print axioms sharipov_second_cuboid_conjecture`.
4. Update `lean/FORMALIZATION_STATUS.md`, `lean/README.md`, `STATUS.md` and
   `HANDOFF.md` with the exact outputs.
5. Commit and push the final audit to the existing draft PR.

Completion requires simultaneously:

```text
source sorry count: 0
project-specific axioms: 0
lake build: PASS
complete reproduction gate: PASS
```

The public theorem must have no `sorryAx` and no project-specific mathematical
axiom in its printed dependency set.

## Session discipline

At the beginning of every session:

```bash
git switch formalization/lean
git pull --ff-only
cd lean
lake build
cd ..
grep -R -n -w sorry lean/Cuboid2
```

Use one writer for any shared Mumford/Cantor API.  Parallel agents may own the
independent `5+5`, `1+4`, and `2+3` blocks, but the coordinator owns imports,
final theorem assembly, commits and pushes.

After every meaningful sub-block, run the targeted Lean build; after every
closed branch, run the full build.  Preserve the Lean/mathlib pins and work
only on `formalization/lean`.
