# Status

Date: 2026-08-31

## Bottom line

Sharipov's second cuboid conjecture is **PROVED** for all coprime positive
integers `p != q`.  The proof is computer-assisted and exact.  It does not
depend on the abandoned 64--128 GiB normalization workflow, a bounded-height
search, or a probabilistic calculation.

The final irreducibility theorem is also formalized in Lean 4 as
`Cuboid2.sharipov_second_cuboid_conjecture`. The source contains no `sorry`
and no project-specific mathematical `axiom`/`opaque` declaration; the strict
audit is `bash scripts/reproduce_lean.sh complete`. The Lean proof establishes
the same theorem as the recommended paper but uses a specialized
Gaussian/octic completion of the `2+3` branch.

The factorization classification C003 leaves only `1+4`, `2+3`, and symmetric
`5+5`.  C004 proves the first case impossible, C005 exactly replays the Sturm
certificate for the third, and C010 proves that the residual `2+3` locus has
no admissible rational point.

The recommended paper is `paper/clean3.tex` (4 pages).  It replaces the old
`7/23` square-abscissa/Coleman block by a direct `p=3` argument on `D_+` and
retains the old proof as an independent verification.

## Completion of the `2+3` case

The recommended argument has four exact stages.

1. **Lossless compact transport.**  C012 gives
   `B=+d^2` or `B=-d^2`.  C035 turns each physical sign into an equivalent
   71-term compact curve, with a rational inverse valid at every admissible
   point.  Simultaneous reciprocity gives the same irreducible 29-term curve
   `C8(U,V)=0` for both signs.  A low-degree characteristic-zero map and its
   inverse identify its admissible normalization with

   ```text
   E1: y^2 = x^3 - 5*x + 4.
   ```

   Every affine, projective, base-locus, and denominator-zero fibre is
   classified.  This is C039 and bypasses, rather than proves, C025.

2. **Two common square characters.**  Both physical signs require `UV` and
   `1-UV` to be nonzero rational squares.  After translation by rational
   2-torsion, exact functions satisfy

   ```text
   1-UV = 2*(X+1)*L*M*g^2,
   X*M = (Y+2)*L,
   h^2 - (k^2+2)*h + k^2 + 4*k - 4 = 0.
   ```

   The scalar `2` is essential.  Squarehood gives `z^2=2*k*h`; valuation
   parity gives

   ```text
   k = 2*epsilon*u^2,  h = epsilon*v^2.
   ```

   The `epsilon=-1` branch is excluded by an exact elementary parity/mod-8
   argument.  The positive branch maps to

   ```text
   D_+: R^2 = 4*a^5 - 8*a^2 + 5*a,  a=u^2.
   ```

3. **Square abscissas directly on `D_+`.**  A complete Schaefer--Stoll
   2-descent with `S={2,5,17}` gives

   ```text
   512 -> 64 -> 8 -> 4,
   rank Jac(D_+)(Q) = 1,
   torsion = Z/2Z,
   D,T independent modulo 2.
   ```

   The prime `17` remains explicit and essential for this rank certificate.
   Exact `p=3` Cantor/formal-log arithmetic gives the annihilator

   ```text
   (lambda-a)*da/R,
   lambda = 7 mod 27,
   v3(lambda-1)=1,
   v3(log_0 D)=2.
   ```

   A rational-square abscissa is classified projectively at `p=3`:

   - if `v3(a)>0`, every nonzero square is impossible because
     `4*a^4-8*a+5 = 2 mod 3` is a nonsquare unit;
   - if `v3(a)=0`, then `a=1 mod 3`, leaving only the disks of `(1,+/-1)`;
   - if `v3(a)<0`, the rational parameter `t=2*a^2/R` has positive valuation
     and places the point in the unique infinity disk of the odd-degree model.

   The Weierstrass disk `(0,0)` uses `R`, not `a`, as a local parameter and
   the same nonsquare-unit argument excludes every nonzero square abscissa.

   In the two `a=1` disks, do not assume `D` primitive.  Write `D=mG` after a
   torsion shift.  Mod-2 independence makes `m` odd, while the only retained
   `p=7` facts

   ```text
   #J(F7)=42,
   ord(D mod 7)=21
   ```

   force `gcd(m,21)=1`, hence `3` does not divide `m`.  Therefore
   `v3(log_0 G)=2`, which forces `a-1 in 9 Z_3`; the annihilating primitive
   is then linear modulo 3 and Strassmann gives uniqueness.

   At infinity, with `w=1/a` and `t=2*a^2/R`, the exact relation

   ```text
   w = t^2*(1 - 2*w^3 + (5/4)*w^4)
   ```

   and the transformed annihilator give a unit linear term.  Universal tail
   bounds prove uniqueness.  Thus C045, and hence C041, gives

   ```text
   {P in D_+(Q): a(P) is a rational square}
     = {infinity, (0,0), (1,1), (1,-1)}.
   ```

   The recommended route uses no `p=23`, no `p=7` square-abscissa table, no
   `42D` `p=7` formal logarithm, and no `p=7` Coleman integration.

4. **Exact lift-back.**  Infinity is a projective boundary and `(0,0)` would
   require `r^2=5`.  At `a=1`, the two translated elliptic points are
   `(1,0)` and `(3,4)`.  The first is the `L=M=0` divisor and has direct
   continued common character `1-UV=1/2`, not a square.  The second has
   `1-UV=0`, which is inadmissible.  The same table closes all zeros and poles
   divided out in the generic argument.

Thus neither physical sign has an admissible point, proving C010 and C020.

## Recommended proof-critical certificates

- `research/compact_signed_square/compact_signed_square.py`
- `research/compact_signed_square/reciprocal_quotient/derive.py`
- `research/arithmetic_geometry/low_degree_transport.py`
- `research/arithmetic_geometry/product_character_simplification.py`
- `research/arithmetic_geometry/product_squareclass_valuation.py`
- `research/arithmetic_geometry/product_genus2_two_descent.py`
- `research/proof_simplification_3/dplus_p3_square_abscissa.py`
- `scripts/replay_5plus5.sh`

The older `7/23` C041 scripts, the direct genus-three C043 certificate, and
the Richelot C044 certificate remain independently runnable audit results,
but are not dependencies of `paper/clean3.tex`.

## Claims deliberately left unchanged

- C025 remains `OPEN`: the final proof does not identify the normalization of
  the original plane equation `H(q,A)=0` directly with a `544.c` model.
- C008 and C016 retain their conditional geometry status and are not proof
  dependencies.
- The older finite-prime density theorem, endpoint reciprocity, genus-33
  character covers, Kummer obstruction, ambient-automorphism no-go,
  genus-three C041 route, and Richelot alternative remain independent results.

## Reproduction

The Lean 4.33.0 formalization is also complete. All three factorization
branches are connected to the public theorem
`sharipov_second_cuboid_conjecture`; the source contains no `sorry` and no
project-specific `axiom`/`opaque` declaration. Its strict gate is:

```bash
bash scripts/reproduce_lean.sh complete
```

The printed axiom set contains standard foundational axioms and closed
`native_decide` certificates, but no `sorryAx`.

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[test]'
PYTHON_BIN=.venv/bin/python bash scripts/reproduce.sh
PYTHON_BIN=.venv/bin/python bash scripts/replay_5plus5.sh
```

The recommended arithmetic core can also be replayed directly:

```bash
.venv/bin/python research/arithmetic_geometry/product_genus2_two_descent.py
.venv/bin/python research/proof_simplification_3/dplus_p3_square_abscissa.py
```

There is no remaining mathematical blocker.  The research concerns
Sharipov's intermediate irreducibility conjecture; it does not settle the
existence of a perfect cuboid.
