# Handoff

## Lean formalization roadmap

The mathematical proof and the Lean formalization are complete under the
documented trust model. Sessions 1 (`2+3`), 2 (`1+4`), and 3 (symmetric
`5+5`) are closed with no source `sorry`s or project-specific mathematical
axioms. The pre-existing `2+3` finite computations use `native_decide`;
Session 2 adds no such dependency. The original four-session plan, exact
gates, and handoff boundaries are recorded in
[`notes/lean_ultra_completion_roadmap.md`](notes/lean_ultra_completion_roadmap.md).
The final strict audit is reproduced with
`bash scripts/reproduce_lean.sh complete`.

## Completed theorem

Sharipov's second cuboid conjecture is proved.  There is no remaining
rational-point or normalization blocker in the proof chain.

The recommended route is

```text
C035 signed-square compact locus
  -> common reciprocal quotient C8
  -> explicit birational E1 transport
  -> two common square characters
  -> valuation descent
  -> direct p=3 square-abscissa theorem on D_+
  -> direct exceptional lift audit
  -> C010/C020
  -> C003 + C004 + C005.
```

Read `paper/clean3.tex` first for the concise proof, then
`notes/c041_direct_dplus_simplification.md` for the arithmetic details.
`CLAIMS.md` is the conservative claim ledger and `STATUS.md` records the
current dependency graph.

The older `paper/clean.tex` proof via the `7/23` Mordell--Weil sieve remains
valid and independently replayable.  The direct genus-three C043 proof and
the Richelot C044 rank proof are also retained as independent audit results.

## Replay before changing a claim

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[test]'
PYTHON_BIN=.venv/bin/python bash scripts/reproduce.sh
PYTHON_BIN=.venv/bin/python bash scripts/replay_5plus5.sh
```

The recommended arithmetic core is independently callable:

```bash
.venv/bin/python research/compact_signed_square/compact_signed_square.py
.venv/bin/python research/compact_signed_square/reciprocal_quotient/derive.py
.venv/bin/python research/arithmetic_geometry/low_degree_transport.py
.venv/bin/python research/arithmetic_geometry/product_character_simplification.py
.venv/bin/python research/arithmetic_geometry/product_squareclass_valuation.py
.venv/bin/python research/arithmetic_geometry/product_genus2_two_descent.py
.venv/bin/python research/proof_simplification_3/dplus_p3_square_abscissa.py
```

No command above invokes the archived high-memory normalization.

## Non-negotiable proof details

Preserve these points in every future rewrite or review.

1. The physical sign `B=+d^2` or `B=-d^2` is not the valuation sign
   `epsilon` in `k=2*epsilon*u^2`.  Both physical signs share the characters
   `UV` and `1-UV`; the final proof uses only these two.

2. The scalar in the transported identity is exactly
   `1-UV=2*(X+1)*L*M*g^2`.  Dropping the factor `2` changes the covering
   curve and invalidates the descent.

3. The compact transport proves C039, not C025.  C025 asks for a direct
   normalization of the original plane model `H(q,A)=0` and remains open but
   unnecessary.

4. The genus-two rank descent includes the bad prime `17`.  The exact
   survivor chain is `512 -> 64 -> 8 -> 4`; the resulting inputs are
   `rank J(Q)=1`, torsion `Z/2Z`, and independence of `D,T` modulo `2`.

5. Do not assume that `D=[(1,1)-infinity]` is a primitive Mordell--Weil
   generator.  After a torsion shift write `D=mG`.  Mod-2 independence makes
   `m` odd.  The recommended proof uses only

   ```text
   #J(F7)=42,
   ord(D mod 7)=21
   ```

   to force `gcd(m,21)=1`, hence `3` does not divide `m`.  This is an integral
   3-saturation lemma, not a residue sieve.  The old `p=23` coefficient
   comparison is no longer a dependency.

6. The direct `p=3` annihilator on

   ```text
   D_+: R^2=4*a^5-8*a^2+5*a
   ```

   is

   ```text
   (lambda-a)*da/R,
   lambda = 7 mod 27,
   v3(lambda-1)=1,
   v3(log_0 D)=2.
   ```

   These are exact formal-log statements with universal tail bounds; do not
   replace them by finite-precision `Q_3` numerics.

7. The square-abscissa classification at `p=3` must remain projective and
   valuation-aware:

   - if `v3(a)>0` and `a` is a nonzero square, then
     `(R/u)^2=4*a^4-8*a+5` is `2 mod 3`, impossible;
   - if `v3(a)=0`, a square unit has `a=1 mod 3`, so only `(1,+/-1)` disks
     remain;
   - if `v3(a)<0`, use `t=2*a^2/R` to reach the unique infinity disk of the
     odd-degree model.

   Do not reduce this to the informal slogan “squares mod 3 are 0 or 1”.

8. At `(0,0)`, `a` is not a valid local parameter.  Use `R`: for
   `F=R^2-a(4a^4-8a+5)`, one has `dF/da=-5`, a 3-adic unit.  The nonsquare
   unit argument excludes every nonzero square abscissa in this disk.

9. In the two `a=1` disks, the integral saturation from item 5 forces
   `a-1 in 9 Z_3`.  Only after this refinement does the annihilating primitive
   reduce to a nonzero scalar times `z` and Strassmann give uniqueness.

10. At infinity use

    ```text
    w=1/a,
    t=2*a^2/R,
    w=t^2*(1-2*w^3+(5/4)*w^4).
    ```

    The formal implicit derivative in `w` is a unit, and the transformed
    annihilator has a unit linear term.  The uniqueness claim requires the
    universal tail bound, not a fixed truncation.

11. At `a=1`, one final transport point lies on `L=M=0`.  It must be checked
    with the original undivided character and has value `1/2`; it is not to be
    called a generic boundary.  The other point has character value zero and
    is inadmissible.

12. Every source and inverse denominator fibre remains part of the proof.  A
    generic function-field identity alone is not enough.

## Exact genus-two data used by the recommended route

For

```text
D_+: R^2=4*a^5-8*a^2+5*a,
D=[(1,1)-infinity], T=[(0,0)-infinity],
```

the 2-descent survivor counts are `512 -> 64 -> 8 -> 4`, with final classes
`0,D,T,D+T`.  The small finite data needed by the recommended proof are

```text
#J(F3)=22,   ord(D mod 3)=11,
#J(F7)=42,   ord(D mod 7)=21.
```

The direct `p=3` formal-log certificate obtains

```text
lambda = log_1(D)/log_0(D) = 7 mod 27,
v3(lambda-1)=1,
v3(log_0 D)=2.
```

The old values at `p=23`, square-abscissa residue tables, the `42D` `p=7`
formal logarithm, and the `p=7` Coleman differential remain historical audit
data only.

## Archived / independent routes

The following remain useful audit material but are not dependencies of the
recommended `clean3` proof:

- the original index-independent `7/23` square-abscissa sieve and `p=7`
  Coleman proof of C041;
- C043, the direct genus-three `p=3` classification of
  `C3: r^2=4*u^8-8*u^2+5`;
- C044, the corrected rational Richelot-isogeny descent with positive twist;
- fixed-prime congruence sieves and their CRT no-go C014;
- Newton endpoint systems and their explicit survivors;
- the two-inert-prime-power theorem C034;
- the genus-33 full covers and ramified-character obstruction C036;
- the direct `C=A-2`, `r=qC` and degree-2 quotient no-gos C038;
- the 64--128 GiB Singular/Sage normalization runbook;
- the still-open direct plane-normalization claim C025.

Do not replace the direct square-abscissa classification with a bounded
search, a finite residue sieve used as a completeness theorem, a Frobenius
fingerprint, or a primitive-generator assumption.
