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

There are currently **four** source `sorry`s.  The source tree now contains
explicit Lean proofs for the elementary factorization classification, exact
weighted scaling, and the reflection/even-polynomial algebra needed for the
specialized Capell step.  The former broad factorization-shell gap has
therefore been reduced to the single specialized implication below.

No gap is hidden behind a custom axiom.  Because the current execution
environment cannot run Lean, all new proof scripts in this update remain
**pending an actual `lake build`** and are not yet described as kernel-checked.

### 1. `normalizedEven_capell_reduction`

**Statement.** If `P_s(u^2)` is reducible, then either `P_s` itself is
reducible or the composition has a symmetric irreducible `5+5`
factorization.

**Implemented in Lean source, pending build.**

- `monic_quintic_reducible_cases` proves that a reducible monic quintic has a
  rational linear factor or a monic quadratic factor with monic cubic
  quotient.
- `normalizedQuintic_reducible_cases` specializes this to `P_s`.
- `sharipovPolynomialQ_eq_scaleRoots` states and proves the exact polynomial
  identity `Q_{p,q}=scaleRoots(P_s(u^2),q^2)`.
- `irreducible_scaleRoots_iff` proves that nonzero root scaling preserves and
  reflects irreducibility.
- `reflectPolynomial` implements the involution `X ↦ -X`; its involutivity,
  preservation of divisibility and irreducibility, and coefficient signs are
  proved in `Capell.lean`.
- `expand_contract_two_of_reflectPolynomial_eq` proves that every polynomial
  fixed by reflection is exactly `G(X^2)`, with
  `G = Polynomial.contract 2 F`.
- `symmetric_product_eq_expand_contract` applies this to
  `R(X)R(-X)`, providing the descent mechanism needed to rule out factors of
  degree below five when `P_s` is irreducible.
- `sharipov_factorization_classification` is now an ordinary Lean proof
  conditional only on the remaining specialized Capell implication.

**What remains.** Choose an irreducible factor `R` of reducible `P_s(X^2)`,
pair it with its reflected factor, descend the symmetric product through
`contract 2`, and prove that irreducibility of `P_s` forces `deg R = 5` and

```text
P_s(X^2) = R(X) * (-R(-X)).
```

The only exceptional subcase is an irreducible factor associated to its own
reflection; it must be reduced separately to a proper factor of `P_s` or a
factor `X`, both incompatible with irreducibility and the nonzero constant
term.

**External proof.** `notes/factorization_classification.md`,
`paper/clean3.tex`, Proposition “Complete factorization reduction”.

**Estimated burden.** Medium.  The required infrastructure is now explicit;
the remaining work is a UFD/divisibility and degree argument rather than a
formalization of general Capell theory.

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

**Implemented in source before the present update.** The exact quadratic
remainder identities, both physical compact equations, reciprocal character
identities, the essential factor `2` in the cleared `E1` character identity,
positive map to `D+`, both 71-term projection Bézout certificates,
boundary-fibre identities, and the abstract `p=7` integral 3-saturation
argument.  These declarations also remain subject to the full build gate.

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

## Declarations already downstream of the gaps

The following theorem bodies contain no local `sorry`; they will become
axiom-clean when the four gaps above are closed and the complete project
builds:

- `sharipov_composition_reduction`;
- `sharipov_factorization_classification`;
- `sharipovPolynomialQ_irreducible`;
- `sharipov_second_cuboid_conjecture`;
- `no_nontrivial_factorization`.

## Validation limitation in the current environment

GitHub Actions did not start because the repository owner's Actions billing
or spending-limit state prevented job allocation.  The current execution
environment has no installed Lean binary and cannot resolve outbound package
hosts, so it cannot install the pinned toolchain.  Consequently the commits
in this update were checked against the exact pinned mathlib source API, but
must still pass a real

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

The development-mode axiom audit is expected to report `sorryAx` until the
four entries above are discharged.  That output must not be described as a
completed formal verification.
