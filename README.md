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
finite-group calculations, and Coleman--Chabauty bounds, not a height-bounded
search or a probabilistic computation.

For reading, start with [`paper/clean.tex`](paper/clean.tex), the streamlined
five-page proof.  [`paper/main.tex`](paper/main.tex) is the frozen full
research exposition.  Both prove the same theorem and use the same
proof-critical certificates.

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
   `Jac(D_+)(Q)` has rank 1 and torsion `Z/2Z`.  An index-independent
   Mordell--Weil sieve at `7` and `23`, followed by an exact `7`-adic formal
   logarithm and Coleman disk bound, proves

   \[
   \{P\in D_+(\mathbf Q):a(P)\in\mathbf Q^2\}
   =\{\infty,(0,0),(1,1),(1,-1)\}.
   \]

4. The point at infinity is a transport boundary; `(0,0)` has no rational
   lift; and the two `a=1` lifts have direct character values `1/2` and `0`.
   Thus neither physical sign contains an admissible point.  This proves C010
   and excludes the `2+3` split.

C004 already proves the `1+4` exclusion, while C005 is the exact replay of
the symmetric `5+5` Sturm certificate.  The complete factorization theorem
C003 therefore proves irreducibility of `Q_{p,q}(t)` for every pair of
coprime positive integers `p!=q`.

The older finite congruence sieves, Newton endpoint theorems, genus-33 cover,
and failed Kummer/ambient-automorphism routes remain in the repository as
independent results and no-go records.  None is used as a substitute for the
global rational-point classification above.

See [STATUS.md](STATUS.md), [CLAIMS.md](CLAIMS.md), and
[HANDOFF.md](HANDOFF.md) for the conservative claim ledger and next theorem.

## Reproduction

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[test]'
PYTHON_BIN=.venv/bin/python bash scripts/reproduce.sh
```

The run regenerates the exact obstruction
polynomials, quotient models, and finite-field certificates.

To replay the embedded exact `5+5` script from arXiv:2601.04240:

```bash
PYTHON_BIN=.venv/bin/python bash scripts/replay_5plus5.sh
```

The research concerns an intermediate irreducibility conjecture.  It is not
equivalent to the nonexistence of perfect cuboids.
