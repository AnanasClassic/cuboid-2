# Exact transport of `V=a^2/b` to `H(q,A)`

This directory contains two independently replayable reductions of the exact
dihedral formula in
`research/arithmetic_geometry/e_model_dihedral_V.json`.

## Preferred formula

`derive_invariant_compact_v.py` works first in the reciprocal invariants

```text
U=s+1/s,  W=b+1/b,  A=2a/(b+1).
```

It derives two equations of `W`-degrees 2 and 5 from the original factorization
remainders.  Their linear subresultant is

```text
L(U,A)*W + C(U,A),
```

where `L` and `C` both have `U`-degree 21 and `A`-degree 19, with 370 and 394
terms respectively.  Their resultant contains the transformed `H(U,A)` as an
exact factor.  Since

```text
V=A^2*(W+2)/4,
```

the generic formula is `V=A^2*(2L-C)/(4L)`.  After the exact Mobius change
`U=2(q+6)/(q-2)` and pseudo-reduction in `A` modulo `H(q,A)`, the exported
formula has:

| part | degree in `q` | degree in `A` | terms |
|---|---:|---:|---:|
| numerator | 100 | 9 | 1010 |
| denominator | 101 | 9 | 1020 |

The cross-product with the independently derived upstream quotient has exact
zero pseudo-remainder modulo `H`.  At `(q,A)=(6,6/7)` the denominator is
nonzero and the value is `V=-36`.

The derivation is a function-field identity.  Its exceptional loci are
preserved explicitly rather than divided away.  The companion exact
classification described below closes their full rational part.

## Exceptional-locus theorem

`classify_transport_exceptions.py` factors the exact elimination resultant
for `H_U=L=C=0`.  Its only possible rational `U`-coordinates are

```text
U=-2, -1, 2.
```

The corresponding scheme gcds in `A` are `(A-2)^5`,
`7A^2+44A+28`, and `(A-2)^6`; their radical supports are `A-2`, the same
quadratic, and `A-2`.  The quadratic has nonsquare discriminant `1152`.
Direct reverse lifting gives `(s,a,b)=(-1,2,1)` and
`(1,2,1)` at the two rational points; the first has nonpositive `s` and the
second is the excluded parameter `s=1`.  The separate `b=-1` chart contributes
only `(s,a,b)=(1,0,-1)`, again excluded.

In the final `q` chart, the only rational roots coming from `L=0` are
`q=-10/3,-2,2`.  Exact pseudo-division gives

```text
2^24 D = lc_A(H)^10 * (4 L_q / 32)  modulo H.
```

The degree-eight polynomial `lc_A(H)` is irreducible and has all-positive
coefficients, so it has no rational root and is positive for `q>0`.  An
admissible square parameter has `q=X+1/X>2`; therefore the displayed compact
denominator is nonzero for every admissible parameter.  The boundary `q=2`
has `T=+/-1`, hence `z=0` or infinity, and does not represent a primitive
positive pair.

The remaining irreducible geometric `U`-orbits have degrees `2,15,68,70` and
therefore contain no rational factor data.  Their individual algebraic lifts
are intentionally not claimed to be classified.

## Checkpoint formula

`derive_compact_v.py` applies pseudo-reduction directly to the upstream
formula.  It gives a larger but logically simpler independent checkpoint with
degrees `(206,9)` and `(207,9)`.  This checkpoint is retained so the invariant
subresultant route is not the only implementation of the reduction.

## Reproduction

With the repository virtual environment and python-flint backend:

```bash
.venv/bin/python research/quotient_transport/derive_compact_v.py
.venv/bin/python research/quotient_transport/derive_invariant_compact_v.py
.venv/bin/python research/quotient_transport/classify_transport_exceptions.py
.venv/bin/python -m pytest -q tests/test_quotient_transport.py
```

Reference runtimes in this workspace were about 11 seconds for the checkpoint,
52 seconds for the invariant derivation, and 64 seconds for the exceptional
classification.  All scripts use exact integer arithmetic and no random seed.
Pure-Python SymPy ground types are valid but substantially slower.

Neither formula identifies the normalization of `H` with elliptic class
`544.c`, proves a Mordell--Weil statement, or determines the rational points
on the three square-character covers.
