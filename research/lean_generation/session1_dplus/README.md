# Session 1 direct `D+` Lean certificate

The checked Lean modules are:

- `Cuboid2/DPlus/GlobalDescent.lean`
- `Cuboid2/DPlus/GlobalKummer.lean`
- `Cuboid2/DPlus/GlobalPointClass.lean`
- `Cuboid2/DPlus/FormalLogP3.lean`
- `Cuboid2/DPlus/SquareDiskReduction.lean`
- `Cuboid2/DPlus/DirectP3.lean`

They replay the fixed finite masks, finite group orders, integral
3-saturation, exact `11D` coefficient rows, the genuine infinity implicit
derivative, normalized `a=1` and infinity primitive rows, and universal
all-degree valuation bounds.  They also construct the actual quartic
algebra `Q[z]/(z^4-16z+20)`, compute its degree-four algebra norm, map every
rational affine point to the product Kummer candidate, prove its total norm
is `(R/2)^2`, and map every rational affine point to a valid degree-one
generator of the exact Cantor presentation.

## Soundness blocker

The external JSON files assert a complete Schaefer--Stoll descent and a
Coleman/Strassmann argument, but JSON assertions are not Lean premises.
The remaining missing implications are:

1. prove that the raw point Kummer value descends to the genuine Jacobian
   Kummer squareclass, and that the complete global image is exactly the
   four masks `{0,96,276,372}` after all `S={2,5,17}` local conditions;
2. identify the exact Cantor presentation (or another explicit divisor
   model) with the rational Jacobian strongly enough to transport the
   Kummer completeness theorem and reduction maps;
3. deduce from that completeness the rank/torsion decomposition
   `J(Q) ≃ Z × Z/2Z` and its compatibility with reduction at `7`;
4. construct the `3`-adic logarithm/Coleman integral as homomorphisms on
   those rational divisor classes and prove that the exact `11D` trace
   computes their logarithm direction;
5. prove that the displayed formal primitives compute the Coleman
   integrals of every rational point in the four relevant disks; and
6. apply a complete power-series/Strassmann zero theorem to the universal
   tail bounds, yielding uniqueness in each disk.

Consequently an unconditional theorem
`DPlusSquareAbscissaClassified` cannot be obtained from the checked rows
without formalizing these bridges.  Encoding any of the conclusions as a
structure field would only rename the missing theorem and is deliberately
not done.

The JSON files are discovery/replay artifacts, not proof objects accepted by
Lean's kernel: string fields such as `"rank": 1`, survivor counts, PARI
class-unit claims, and `"status": "PASS"` have no theorem semantics.  A
checksum proves only byte identity.  The Python computation also delegates
class groups, units, local power tests, and local-image completeness to PARI;
none of those algorithms currently emits a certificate checked by the Lean
definitions above.  In particular the four stored mask numerals are not yet
the image of `dplusPointKummerValue` under any proved squareclass map.

## Shortcut audit

Square abscissa narrows the rational factor of a 2-descent Kummer value, but
even if the four external Selmer masks are granted this only says that the
point class lies in `2J(Q)` or `D+2J(Q)`.  It does not classify the infinitely
many rank-one lattice coefficients.

The elementary identity

```text
r^2 = (2*u^4 - 1)^2 + (2*(u^2 - 1))^2
```

is checked in `GlobalDescent.lean`.  Rational circle parametrization gives

```text
(u^2 - 1)*(1 - t^2) = t*(2*u^4 - 1).
```

Regarding this as a quadratic in `u^2` has discriminant

```text
t^4 + 8*t^3 + 6*t^2 - 8*t + 1,
```

so imposing that `u^2` is itself a square recreates a genus-one square
pullback; it is not an elementary classification shortcut.
