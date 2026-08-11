# Status

Date: 2026-08-10

## Bottom line

Sharipov's second cuboid conjecture is **PROVED** for all coprime positive
integers `p != q`.  The proof is computer-assisted and exact.  It does not
depend on the abandoned 64--128 GiB normalization workflow, a bounded-height
search, or a probabilistic calculation.

The factorization classification C003 leaves only `1+4`, `2+3`, and symmetric
`5+5`.  C004 proves the first case impossible, C005 exactly replays the Sturm
certificate for the third, and C010 now proves that the residual `2+3` locus
has no admissible rational point.

## Completion of the `2+3` case

The final argument has four exact stages.

1. **Lossless compact transport.**  C012 gives
   `B=+d^2` or `B=-d^2`.  C035 turns each physical sign into an equivalent
   71-term compact curve, with a rational inverse valid at every admissible
   point.  Simultaneous reciprocity gives the same irreducible 29-term curve
   `C8(U,V)=0` for both signs.  A low-degree characteristic-zero map and its
   inverse identify its admissible normalization with

   ```text
   E1: y^2 = x^3 - 5*x + 4.
   ```

   The calculation explicitly classifies all affine, projective, and
   denominator-zero fibres.  This compact-locus transport is C039.  It
   bypasses C025; the older direct normalization of the original plane model
   `H(q,A)=0` remains open as a separate, unnecessary identification.

2. **Two common square characters.**  Both physical signs require `UV` and
   `1-UV` to be nonzero rational squares.  After translation by the rational
   2-torsion point on `E1`, exact functions `L,M,k,h` satisfy

   ```text
   1-UV = 2*(X+1)*L*M*g^2,
   X*M = (Y+2)*L,
   h^2 - (k^2+2)*h + k^2 + 4*k - 4 = 0.
   ```

   The scalar `2` is essential.  Away from the separately checked divisor,
   squarehood gives `z^2=2*k*h`.  Odd valuations and the 2-adic Newton cases
   imply

   ```text
   k = 2*epsilon*u^2,  h = epsilon*v^2.
   ```

   The `epsilon=-1` curve has no rational point by an exhaustive elementary
   parity/mod-8 argument.  The positive sign maps to

   ```text
   D_+: R^2 = 4*a^5 - 8*a^2 + 5*a,  a=u^2.
   ```

3. **Square abscissas on `D_+`.**  A complete Schaefer--Stoll 2-descent with
   `S={2,5,17}` gives

   ```text
   512 -> 64 -> 8 -> 4,
   rank Jac(D_+)(Q) = 1,
   torsion = Z/2Z.
   ```

   The prime `17` is explicit and essential.  Exact finite Jacobian arithmetic
   gives orders `42` and `462` at `7` and `23`, while `D` has orders `21` and
   `231`.  The two-prime Mordell--Weil sieve is independent of the unknown odd
   index of `<D,T>`: writing `D=mG` with odd `m`, the full reduction orders
   force `m` to be invertible modulo both `21` and `231`.  The sieve removes
   the two extra square-abscissa disks at `7`.

   Exact rational Cantor arithmetic for `42D` gives formal-log direction
   `(1,4)` modulo `7`, so an annihilating differential reduces to

   ```text
   (4-a)*da/R.
   ```

   It is nonzero in every surviving disk, and `7>2g`.  Coleman--Chabauty
   therefore proves

   ```text
   {P in D_+(Q): a(P) is a rational square}
     = {infinity, (0,0), (1,1), (1,-1)}.
   ```

   A second implementation independently obtains the finite Jacobian orders
   from exhaustive counts over `F_p` and `F_(p^2)`.

4. **Exact lift-back.**  Infinity is a projective boundary and `(0,0)` would
   require `r^2=5`.  At `a=1`, the two translated elliptic points are
   `(1,0)` and `(3,4)`.  The first is the `L=M=0` divisor and has direct
   continued common character `1-UV=1/2`, not a square.  The second maps to
   the old point `P=(0,2)` and has `1-UV=0`, which is inadmissible.  The same
   table closes all zeros and poles divided out in the generic argument.

Thus neither physical sign has an admissible point, proving C010 and C020.
The complete proof is written in `notes/quadratic_cubic_completion.md`.

## Proof-critical certificates

- `research/compact_signed_square/compact_signed_square.py`
- `research/compact_signed_square/reciprocal_quotient/derive.py`
- `research/arithmetic_geometry/low_degree_transport.py`
- `research/arithmetic_geometry/product_character_simplification.py`
- `research/arithmetic_geometry/product_squareclass_valuation.py`
- `research/arithmetic_geometry/product_genus2_two_descent.py`
- `research/arithmetic_geometry/product_genus2_square_sieve.py`
- `research/arithmetic_geometry/product_genus2_p7_formal_log.py`
- `research/compact_signed_square/independent_genus2_square_sieve.py`
- `scripts/replay_5plus5.sh`

Every JSON artifact is regenerated and compared exactly by the test suite.

## Claims deliberately left unchanged

- C025 remains `OPEN`: the final proof does not identify the normalization of
  the original plane equation `H(q,A)=0` directly with a `544.c` model.
- C008 and C016 retain their conditional geometry status.  They are no longer
  dependencies of the completion.
- The older finite-prime density theorem, endpoint reciprocity, genus-33
  character covers, Kummer obstruction, and ambient-automorphism no-go remain
  valid independent results.  They are historical reductions, not hidden
  premises in the final classification.

## Reproduction

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[test]'
PYTHON_BIN=.venv/bin/python scripts/reproduce.sh
PYTHON_BIN=.venv/bin/python bash scripts/replay_5plus5.sh
```

The final low-resource block can also be replayed directly:

```bash
.venv/bin/python research/compact_signed_square/reciprocal_quotient/derive.py
.venv/bin/python research/arithmetic_geometry/low_degree_transport.py
.venv/bin/python research/arithmetic_geometry/product_character_simplification.py
.venv/bin/python research/arithmetic_geometry/product_squareclass_valuation.py
.venv/bin/python research/arithmetic_geometry/product_genus2_two_descent.py
.venv/bin/python research/arithmetic_geometry/product_genus2_square_sieve.py
.venv/bin/python research/arithmetic_geometry/product_genus2_p7_formal_log.py
.venv/bin/python research/compact_signed_square/independent_genus2_square_sieve.py
```

There is no remaining mathematical blocker.  The research concerns
Sharipov's intermediate irreducibility conjecture; it does not settle the
existence of a perfect cuboid.
