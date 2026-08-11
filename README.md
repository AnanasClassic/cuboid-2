# Sharipov's second cuboid conjecture

This repository studies the irreducibility over `Q` (equivalently `Z`) of

\[
Q_{p,q}(t)=q^{20}P_s\!\left(t^2/q^4\right),\qquad
s=(p/q)^2,
\]

for coprime positive integers `p != q`, where

\[
\begin{aligned}
P_s(x)={}&x^5+(2+s)(3-2s)x^4
 +(1+10s+4s^2-14s^3+s^4)x^3\\
&-s(1-14s+4s^2+10s^3+s^4)x^2
-s^3(1+2s)(-2+3s)x-s^5.
\end{aligned}
\]

## Current status

**The conjecture is proved.**  The proof is computer-assisted but exact: it
uses symbolic identities, certified number-field arithmetic, exhaustive
finite-group calculations, and Coleman--Chabauty/Strassmann bounds, not a
height-bounded search or a probabilistic computation.

For reading, start with [`paper/clean3.tex`](paper/clean3.tex), the recommended
four-page proof.  Its arithmetic core proves the square-abscissa theorem
directly on

\[
D_+:R^2=4a^5-8a^2+5a.
\]

[`paper/clean.tex`](paper/clean.tex) is the earlier five-page presentation
using the original `7/23` square-abscissa route, while
[`paper/main.tex`](paper/main.tex) is the frozen full research exposition.
All three prove the same irreducibility theorem, but the recommended
`clean3` route has fewer arithmetic dependencies.

The previously open quadratic--cubic (`2+3`) case is closed as follows.

1. The signed-square theorem forces the constant of a hypothetical integral
   quadratic factor to be `B=+d^2` or `B=-d^2`.  The lossless compact model in
   `research/compact_signed_square/` carries both physical signs to the same
   irreducible 29-term reciprocal quotient `C8(U,V)=0`.  Exact maps and their
   inverses identify its admissible normalization with

   \[
   E_1:y^2=x^3-5x+4.
   \]

   Every source, denominator-zero, and projective exceptional fibre is
   classified directly.  This compact-locus transport bypasses the older
   still-open direct normalization claim C025.

2. Both physical signs require the same two nonzero square characters `UV`
   and `1-UV`.  After translating by the rational 2-torsion point on `E1`, an
   exact identity reduces the second character to

   \[
   z^2=2kh,\qquad
   h^2-(k^2+2)h+k^2+4k-4=0.
   \]

   Valuations give `k=2*epsilon*u^2` and `h=epsilon*v^2`.  An elementary
   2-adic parity argument excludes `epsilon=-1`; the positive sign maps to

   \[
   D_+:R^2=4a^5-8a^2+5a,\qquad a=u^2.
   \]

3. A complete Schaefer--Stoll 2-descent at `2,5,17` proves that
   `Jac(D_+)(Q)` has rank 1, torsion `Z/2Z`, and the required mod-2
   independence.  The recommended C041 proof then works directly on `D_+` at
   `p=3`.  Rational-square abscissas can lie only in the disks of
   `infinity`, `(0,0)`, and `(1,+/-1)`.  The direct annihilator is

   \[
   (\lambda-a)\,da/R,\qquad
   \lambda\equiv7\pmod{27},\quad v_3(\lambda-1)=1.
   \]

   The `(0,0)` disk is excluded for nonzero square abscissas by a nonsquare
   unit modulo 3.  At `(1,+/-1)`, the small finite-group facts
   `#J(F_7)=42` and `ord(D mod 7)=21` prove the needed integral 3-saturation
   without assuming `D` primitive; this forces `a-1 in 9 Z_3`, where an exact
   Strassmann bound gives uniqueness.  A projective `p=3` expansion treats
   infinity.  Hence

   \[
   \{P\in D_+(\mathbf Q):a(P)\in\mathbf Q^2\}
   =\{\infty,(0,0),(1,1),(1,-1)\}.
   \]

   This route does not use `p=23`, a `p=7` square-abscissa table, a `p=7`
   formal logarithm, or `p=7` Coleman integration.  The older `7/23` proof
   remains in the repository as an independent verification.

4. The point at infinity is a transport boundary; `(0,0)` has no rational
   lift; and the two `a=1` lifts have direct character values `1/2` and `0`.
   Thus neither physical sign contains an admissible point.  This proves C010
   and excludes the `2+3` split.

C004 already proves the `1+4` exclusion, while C005 is the exact replay of
the symmetric `5+5` Sturm certificate.  The complete factorization theorem
C003 therefore proves irreducibility of `Q_{p,q}(t)` for every pair of
coprime positive integers `p!=q`.

The older finite congruence sieves, Newton endpoint theorems, genus-33 cover,
the direct genus-three C041 proof, and failed Kummer/ambient-automorphism
routes remain in the repository as independent results and audit material.

See [STATUS.md](STATUS.md), [CLAIMS.md](CLAIMS.md), and
[HANDOFF.md](HANDOFF.md) for the conservative claim ledger and proof state.

## Reproduction

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[test]'
PYTHON_BIN=.venv/bin/python bash scripts/reproduce.sh
```

The run regenerates the exact obstruction polynomials, quotient models, rank
certificates, and direct `D_+` square-abscissa certificate.

To replay the embedded exact `5+5` script from arXiv:2601.04240:

```bash
PYTHON_BIN=.venv/bin/python bash scripts/replay_5plus5.sh
```

The research concerns an intermediate irreducibility conjecture.  It is not
equivalent to the nonexistence of perfect cuboids.
