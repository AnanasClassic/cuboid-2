# Formalization status

Last updated: 2026-08-31.

## Completion criterion

The formalization is complete only when all of the following hold:

1. `lake build` succeeds;
2. no source file under `Cuboid2/` contains `sorry`;
3. no project-specific `axiom` or `opaque` declaration exists;
4. `#print axioms sharipov_second_cuboid_conjecture` contains no `sorryAx` and
   no project-specific mathematical axiom.

Standard mathlib foundational axioms such as classical choice, `propext`, and
quotient soundness are acceptable.

Closed finite propositions discharged by `native_decide` are also accepted
as a documented computation trust extension. They are not mathematical
assumptions, but they are not reduced by the kernel alone. The specialized
Session 2 theorem does not use this extension.

## Remaining proof gaps

There are **no** source `sorry`s. All three factorization branches and the
public theorem are closed under the trust model above. No gap is hidden behind
a custom mathematical axiom or `opaque` declaration.

The pinned Lean 4.33.0 toolchain completes a full `lake build`, and
`Cuboid2/AxiomAudit.lean` reports no `sorryAx`. Its non-foundational axiom
footprint consists only of closed `native_decide` certificates.

## Closed factorization shell in Lean source

The following have Lean theorem bodies rather than placeholders:

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
Cuboid2/FiveFive/DiscriminantP6Roots.lean
Cuboid2/FiveFive/DiscriminantP28Local.lean
Cuboid2/FiveFive/DiscriminantP28Roots.lean
Cuboid2/FiveFive/ResultantCritical.lean
Cuboid2/FiveFive/SamplePositivity.lean
Cuboid2/FiveFive/SamplePositivityMore.lean
Cuboid2/FiveFive/SamplePositivity63.lean
Cuboid2/FiveFive/SamplePositivity317.lean
Cuboid2/FiveFive/SamplePositivity40.lean
Cuboid2/FiveFive/SamplePositivityReal.lean
Cuboid2/FiveFive/RootTransport.lean
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
- complete exact isolation of the two positive P6 roots;
- complete exact isolation of the three positive P28 roots, including proof
  that no other positive P28 root exists;
- sparse diagonally-dominant sum-of-squares certificates for `s=1/100` and
  `s=1/5`;
- exact rational positive-definite Gram/LDL sum-of-squares certificates for
  `s=4/5`, `s=2`, `s=63/2`, `s=317/10`, and `s=40`;
- strict positivity over `ℝ` for **all seven sample fibres** used by the pinned
  replay;
- a direct exact Bézout identity showing that a multiple fibre root forces
  `s=0`, `s=1`, `s=-1`, `P6(s)=0`, or `P28(s)=0`;
- a specialized projective first-contact argument transporting sample
  positivity across every critical-free complementary interval;
- the final theorem `fiveFiveResultantFactor_ne_zero`, and therefore
  `fiveFive_reduced_locus_empty` and `symmetric_five_five_impossible`.

Every polynomial identity, Bernstein/SOS coefficient, sign comparison,
compactness step, derivative argument, and interval dispatch is checked by
Lean. PARI/SymPy output and the replay checksum were generation and audit aids,
not proof premises.

## Closed — `linear_quartic_impossible`

The final assembly proves the specialized statement actually needed for
Sharipov's polynomial:

```lean
theorem linear_quartic_impossible
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hcop : Nat.Coprime p q) (hne : p ≠ q) :
    ¬ LinearQuarticCase (sharipovParameter p q)
```

The proof does not assume the more general rational-point classification for
an arbitrary positive parameter. Instead, it uses the extra arithmetic of
`s=(p/q)²`:

- a rational root scales to an integral root of the homogeneous quintic;
- its prime valuations are `0`, `2k`, or `4k`, so the root is a signed
  rational square;
- the inverse-slope map preserves that signed-square class;
- the positive cover is reduced to Fermat's fourth-power descent;
- the negative cover is combined with the original genus-two equation, and
  exact cancellation of the common 3-adic factor gives incompatible nonzero
  residues modulo three.

The implementation is in:

```text
Cuboid2/LinearQuartic/FermatAuxiliary.lean
Cuboid2/LinearQuartic/SharipovCompletion.lean
Cuboid2/LinearQuartic/SignedSquareCovers.lean
Cuboid2/LinearQuartic/SharipovImpossibility.lean
```

## Closed — `quadratic_cubic_impossible`

The final assembly now proves the specialized statement actually needed for
the cuboid theorem:

```lean
theorem quadratic_cubic_impossible
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hcop : Nat.Coprime p q) (hne : p ≠ q) :
    ¬ QuadraticCubicCase (sharipovParameter p q)
```

The proof is unconditional. It combines the exact compact-to-elliptic
transport, Gaussian 2-isogeny descent, finite generation and exact rank and
torsion normal forms, actual good reduction and saturation at `3`, `7`, and
`37`, and the split-37 paired formal argument. The resulting classifications
of both Gaussian covers imply the exact rational-point classification on the
octic curve, which is consumed by the specialized Sharipov transport theorem.
No primitivity assumption on the visible rank-one point is used.

## Closed — `fiveFiveResultantFactor_ne_zero`

**Statement.** For positive rational `s≠1`, the explicit scalar resultant
factor has no rational zero in `y`.

The proof is unconditional. Exact Bernstein certificates isolate all five
positive discriminant cuts. A fraction-free multiplication-back certificate
excludes multiple roots away from those cuts, and a compact projective
first-contact lemma transports the seven exact real SOS/LDL sample
certificates across the complementary cells. Rational nonvanishing of P6 and
P28 ensures that every admissible rational parameter lies in one such cell.

## Axiom-clean downstream theorem bodies

The following theorem bodies are now axiom-clean apart from the accepted
foundational and closed finite-decision footprint:

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

Both development and complete modes pass. In particular, complete mode finds
zero source placeholders, zero project-specific `axiom`/`opaque`
declarations, and no `sorryAx` in the public theorem.
