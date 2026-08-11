# Handoff

## Completed theorem

Sharipov's second cuboid conjecture is proved.  There is no remaining
rational-point or normalization blocker in the proof chain.

The decisive route is

```text
C035 signed-square compact locus
  -> common reciprocal quotient C8
  -> explicit birational E1 transport
  -> two common square characters
  -> valuation descent
  -> square-abscissa points on D_+
  -> direct exceptional lift audit
  -> C010/C020
  -> C003 + C004 + C005.
```

Read `notes/quadratic_cubic_completion.md` first.  The exact current ledger is
`CLAIMS.md`; the concise proof state is `STATUS.md`.

## Replay before changing a claim

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[test]'
PYTHON_BIN=.venv/bin/python scripts/reproduce.sh
PYTHON_BIN=.venv/bin/python bash scripts/replay_5plus5.sh
```

The proof-critical low-resource certificates are independently callable:

```bash
.venv/bin/python research/compact_signed_square/compact_signed_square.py
.venv/bin/python research/compact_signed_square/reciprocal_quotient/derive.py
.venv/bin/python research/arithmetic_geometry/low_degree_transport.py
.venv/bin/python research/arithmetic_geometry/product_character_simplification.py
.venv/bin/python research/arithmetic_geometry/product_squareclass_valuation.py
.venv/bin/python research/arithmetic_geometry/product_genus2_two_descent.py
.venv/bin/python research/arithmetic_geometry/product_genus2_square_sieve.py
.venv/bin/python research/arithmetic_geometry/product_genus2_p7_formal_log.py
.venv/bin/python research/compact_signed_square/independent_genus2_square_sieve.py
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
4. The genus-two descent includes the bad prime `17`.  The exact field data
   are: defining-polynomial discriminant `2^14*17`, field discriminant
   `2^4*17=272`, and power-order index `32`.
5. Do not assume that `D` is a primitive Mordell--Weil generator.  If
   `D=mG+delta*T`, mod-2 independence makes `m` odd; absorb the torsion into
   `G`.  The reduction orders force `m` invertible modulo `21` and `231`, so
   the `7/23` sieve is index-independent.
6. The Coleman step uses an exact 7-adic annihilator whose *reduction* is
   `(4-a)da/R`.  The discarded p=3 shortcut had reduction `(1-a)da/R` and
   vanished at `a=1`; do not restore that argument.
7. At `a=1`, one point lies on `L=M=0`.  It must be checked by the original
   character and has value `1/2`, not called a boundary.  The other point has
   value zero and is the actual boundary.
8. Every source and inverse denominator fibre is part of the proof.  A
   generic function-field identity alone is not enough.

## Exact genus-two data

For

```text
D_+: R^2=4*a^5-8*a^2+5*a,
D=[(1,1)-infinity], T=[(0,0)-infinity],
```

the 2-descent survivor counts are `512 -> 64 -> 8 -> 4`, with final masks
`0,96,276,372` corresponding to `0,D,D+T,T`.  The finite data are

```text
#J(F3)=22,   ord(D mod 3)=11,
#J(F7)=42,   ord(D mod 7)=21,
#J(F23)=462, ord(D mod 23)=231.
```

At `p=7`, square-abscissa classes are `0,+/-1,+/-5` in the torsion-zero
component and `T`.  At `p=23`, their reduction modulo `21` is
`0,+/-1,+/-2,+/-3,+/-4,+/-9` and `T`; hence the extra `+/-5` disks die.
The formal logarithm has direction `(1,4)` and the four surviving disks are
occupied by `infinity,(0,0),(1,+/-1)`.

## Archived routes

The following remain useful audit material but are not proof dependencies:

- fixed-prime congruence sieves and their CRT no-go C014;
- Newton endpoint systems and their explicit survivors;
- the two-inert-prime-power theorem C034;
- the genus-33 full covers and ramified-character obstruction C036;
- the direct `C=A-2`, `r=qC` and degree-2 quotient no-gos C038;
- the 64--128 GiB Singular/Sage normalization runbook;
- the still-open direct plane-normalization claim C025.

Do not replace the final square-abscissa classification with a bounded search,
a finite residue sieve without the index argument and Coleman bound, or a
Frobenius fingerprint.
