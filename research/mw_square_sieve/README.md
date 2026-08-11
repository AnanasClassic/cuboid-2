# Exact Mordell--Weil square-character sieve

This directory contains the finishing finite sieve prepared for the explicit
normalization map from `H(q,A)=0` to the candidate elliptic curve.

The certified candidate arithmetic is

```text
E1: y^2 = x^3 - 5*x + 4,
E1(Q) = <P=(0,2)> + <T=(1,0)>,
rank(E1(Q))=1,  T has order 2, and <P> is fully saturated.
```

For each good odd prime, `sage_mw_character_sieve.py` enumerates every
reduction of

```text
n*P + e*T,  n modulo ord(P mod ell), e in {0,1},
```

and retains exactly the classes for which all three necessary characters can
be squares:

```text
q+2, q-2, epsilon*V, epsilon in {+1,-1}.
```

Here `V=a^2/b=N(q,A)/D(q,A)` is the independently verified compact invariant.
Generalized CRT is used with the actual, possibly non-coprime orders.  Zeros
are retained as squares.  A pole, a zero transport denominator, or a zero
compact-V denominator modulo a sieve prime is conservatively retained rather
than rejected.

## Exact logical boundary

The finite sieve proves exhaustiveness **only if all four intersections**
`(epsilon,e)` are empty.  A nonempty set of residues `n mod M` describes
infinitely many integers and is not a rational-point theorem.  The program
therefore has three disjoint statuses:

- `GENERIC_OPEN_EXCLUDED_BY_EXHAUSTIVE_FINITE_MW_SIEVE`;
- `INCOMPLETE_FINITE_SIEVE_NONEMPTY_RESIDUAL_CLASSES`;
- `COMPUTATIONAL_LIMIT_NO_MATHEMATICAL_CONCLUSION`.

Even the first status applies only to the transported generic open locus.  A
full proof still needs the separately exact treatment of:

- projective base points and denominator-zero points of the birational map;
- `q=+/-2` and `T=0,infinity` boundary fibers;
- `Q1(T,A)=0`, where the displayed subresultant inverse is undefined;
- `B=+/-1` and the omitted `b=-1` chart.

The compact-V denominator audit does **not** by itself close `Q1=0`.

## Exact reverse lift

`sage_reconstruct_lift.py` takes a particular `(n,e,epsilon)`, evaluates it
over `QQ`, and tests every character-root sign.  On the generic chart it uses

```text
T=(sqrt(q+2)+sqrt(q-2))/2,
B=-Q0(T,A)/Q1(T,A),
z=(1+T)/(1-T),  s=z^2,
b=(1+B)/(1-B),  a=A/(1-B).
```

It then divides `P_s(x)` by `x^2+a*x+b` exactly.  If a genuine lift exists,
it constructs the corresponding quartic and sextic factors of
`Q_{p,q}(t)` and verifies their product by exact multiplication.  If `Q1=0`,
the script does not divide: it reconstructs the two original remainder
numerators as polynomials in `B`, computes their exact gcd, and enumerates all
rational roots.  Only the separately flagged case in which both numerators
vanish identically would leave a positive-dimensional exceptional fiber.

## Reproduction after the transport certificate exists

```bash
sage -python research/mw_square_sieve/sage_mw_character_sieve.py \
  --transport research/arithmetic_geometry/e_model_singular_cubic_certificate.json \
  --prime-bound 500 \
  --output research/mw_square_sieve/mw_character_sieve.json

sage -python research/mw_square_sieve/sage_reconstruct_lift.py \
  --transport research/arithmetic_geometry/e_model_singular_cubic_certificate.json \
  --n 0 --torsion 0 --epsilon 1 \
  --output research/mw_square_sieve/reconstructed_lift.json

python -m pytest -q research/mw_square_sieve/test_core.py
```

The first two commands intentionally refuse to run before the quotient
transport says `WEIERSTRASS_Q_A_TRANSPORT_CERTIFIED` and identifies the exact
candidate as `544.c_E1`.

The sieve additionally binds the Mordell--Weil certificate to the exact E1
Weierstrass coefficients and generator `(0,2)`.  The reverse lift verifies the
embedded checksum of `artifacts/genus4_quotient.json` before using `Q0,Q1`.
