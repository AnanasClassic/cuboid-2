# Gaussian 2-isogeny descent and split-prime certificate

This directory records the exact certificate work behind the Gaussian route
used by the completed Lean formalization of the `2+3` branch:

```text
r^2 = 4 u^8 - 8 u^2 + 5,     u,r in Q.
```

`verify_certificates.py` independently checks the finite calculations without
Sage, Magma, PARI, or floating-point arithmetic. The corresponding
specialized global bridges are now implemented in
[`lean/Cuboid2/QuadraticReduction/`](../../lean/Cuboid2/QuadraticReduction/).

## 1. Gaussian split

Put

```text
q(u) = 2u^4 + 2 i u^2 - 1 - 2i.
```

Then

```text
4u^8 - 8u^2 + 5 = q(u) conjugate(q(u)).
```

For a reduced fraction `u=m/n`, Gaussian gcd and `(1+i)`-valuation
analysis gives exactly two square cases:

```text
C0: v^2 = q(u),
C1: w^2 = -i q(u).
```

Here is the complete elementary gcd step.  Set

```text
F = 2m^4 + 2i m^2n^2 - (1+2i)n^4.
```

Then `F*conjugate(F)=(rn^4)^2`, and a rational number whose square is
an integer is an integer.  If an odd Gaussian prime divides both
factors, it divides

```text
2m^4-n^4                  and                  n^2(m^2-n^2).
```

It cannot divide `n`, by coprimality of `m,n`; hence it divides
`m^2-n^2`, after which the first expression forces it to divide `n`.
This contradiction shows that only `lambda=1+i` can occur in the gcd.

If `n` is odd, `Re(F)` is odd and `Im(F)` is even, so
`v_lambda(F)=0`; unique factorization and the parity shape of a
Gaussian square give `F=gamma^2`.  If `n` is even, `m` is odd,
`Re(F)=2 mod 4`, and `Im(F)=0 mod 8`; now `v_lambda(F)=2`, and the
same parity check gives `F=i*gamma^2`.  Dividing by `n^4` gives `C0`
and `C1`, respectively.

The degree-two elliptic quotients are

```text
E0: Y^2 = X^3 + 2i X^2 - (2+4i)X,
    X = 2u^2,       Y = 2uv;

E1: Y^2 = X^3 + 2X^2 + (2+4i)X,
    X = -2i u^2,    Y = -2iuw.
```

Write `K=Q(i)`, `lambda=1+i`, `pi=1+2i`, and `rho=1+4i`.

## 2. Exact 2-isogeny descent

For

```text
E(A,B): y^2 = x(x^2+Ax+B)
```

use the isogenous curve

```text
E'(A,B): y^2 = x(x^2-2Ax+(A^2-4B)).
```

Away from the exceptional points, the two maps are

```text
phi(x,y) =
  (y^2/x^2, y*(B-x^2)/x^2),

phiHat(X,Y) =
  (Y^2/(4X^2), Y*((A^2-4B)-X^2)/(8X^2)).
```

Their exceptional values are fixed by continuity, their kernels are
`{O,(0,0)}`, and `phiHat(phi(Q))=[2]Q`.  Direct substitution checks all
of these identities on the displayed models.

The usual descent map is

```text
alpha(O)=1, alpha((0,0))=B, alpha((x,y))=x
```

in `K*/K*^2`.  A class `d` is soluble only if the homogeneous space

```text
N^2 = d U^4 + A U^2 V^2 + (B/d)V^4                 (HS)
```

is soluble.  Since `Z[i]` is a PID, valuation parity outside `B` says
that a squarefree representative `d` is supported on the primes of `B`.
Modulo squares, the unit group contributes only `{1,i}`.

The complete candidate and local-obstruction rows are:

```text
E0:  A=2i, B=-2-4i, candidates {1,i,pi,i*pi}.
     All four occur:
       O -> 1,
       P=(2,2) -> i,
       T=(0,0) -> i*pi,
       P+T=(-1-2i,1+2i) -> pi.
     Therefore |alpha(E0)|=4.

E0': A=-4i, B=4+16i, candidates {1,i,rho,i*rho}.
     1 and rho occur at O and T'.
     For d=i and d=i*rho, (HS) has no lambda-primitive
     solution modulo lambda^8=(16).
     Therefore |alpha(E0')|=2.

E1:  A=2, B=2+4i, candidates {1,i,pi,i*pi}.
     1 and i*pi occur at O and T.
     For d=i, (HS) has no lambda-primitive solution modulo (8).
     For d=pi it already has none modulo (4), hence none modulo (8).
     Therefore |alpha(E1)|=2.

E1': A=-4, B=-4-16i, candidates {1,i,rho,i*rho}.
     1 and rho occur at O and T'.
     For d=i and d=i*rho, (HS) has no lambda-primitive
     solution modulo lambda^10=(32).
     Therefore |alpha(E1')|=2.
```

Here `lambda` divides `a+bi` exactly when `a+b` is even.  Thus each local
claim above is a finite statement about pairs in
`(Z/NZ)^2`; the verifier exhausts it directly.

The discriminants of the nonzero quadratic factors are respectively
`4rho` and `-4rho`.  Since `Norm(rho)=17` is not a rational square,
both curves have exactly one nonzero `K`-rational 2-torsion point.
The 2-isogeny rank formula

```text
2^rank = |alpha(E)| |alpha(E')| / 4
```

therefore gives

```text
rank E0(K) = 1,
rank E1(K) = 0.
```

For clarity, the factor `4` in the rank formula is not a convention:
`ker(phiHat)` has order two and its nonzero point is not in
`phi(E(K))`.  Thus

```text
[E(K):2E(K)] = |alpha(E)|*|alpha(E')|/2.
```

Since `E(K)[2]` has order two, Mordell--Weil gives
`[E(K):2E(K)]=2^(rank+1)`, yielding the displayed formula.

The full torsion groups are also exactly `Z/2Z`.  Good-reduction counts
are:

```text
             p=13, i=5   p=13, i=8   p=29, i=12   p=29, i=17
E0                 12            18             28             38
E1                 16            10             32             22
```

Reduction at both primes over 13 bounds every prime-to-13 torsion
subgroup; reduction over 29 excludes 13-torsion.  The gcds leave order
at most two, and `(0,0)` supplies that point.

Consequently `E1(K)={O,(0,0)}`.  Neither point is the image of an affine
point of `C1`: `O` has no finite `X`, while `(0,0)` forces `u=0` and

```text
w^2 = -2+i.
```

Taking norms would make the rational number `Norm(w)` have square `5`,
which is impossible.  Thus `C1` has no affine `K`-points.

## 3. Rank-one index facts needed at 37

Let `G` generate the free part of `E0(K)` and write

```text
P = mG + delta*T,      delta in {0,1}.
```

No assertion that `P` is primitive is needed.

The four descent classes of `O,P,T,P+T` are distinct, so `P,T` are
independent in `E0(K)/2E0(K)`.  Hence `m` is odd.

Three tiny good-reduction certificates give the other required
saturation facts:

```text
p=37,  i=6:   #E=48,  ord(P)=12  -> 3 does not divide m;
p=29,  i=12:  #E=28,  ord(P)=14  -> 7 does not divide m;
p=157, i=28:  #E=148, ord(P)=74  -> 37 does not divide m.
```

In the last row `[37]P=(92,0)` and `[74]P=O`.

## 4. Complete split-prime row at p=37

The two embeddings are `i -> 6` and `i -> -6=31`.

```text
E+: y^2=x^3+12x^2+11x, #E+(F37)=48, exp(E+)=12;
E-: y^2=x^3+25x^2+22x, #E-(F37)=42, E- cyclic.
```

The orders of `P=(2,2)` are 12 and 6.  Since `m` is prime to
`2*3*7`, multiplication by `m` is an automorphism of both reduction
groups.  Therefore every

```text
Q=kG+epsilon*T
```

reduces at the two split primes as the same row

```text
nP+eta*T
```

with `n` read modulo 12 on `E+` and modulo 6 on `E-`.

Comparing the two `x`-coordinates gives:

```text
eta=0: n=0,1,11 mod 12;
eta=1: n=0 mod 12.
```

The `n=0,eta=0` row is the infinity residue disk.  An affine point can
reduce there, so it must not simply be discarded: it has
`v_37(X)<0`, hence `v_37(u)<0`, and division of the quartic equation by
`u^4` would make `2` a square modulo 37.  But `2` is a nonsquare
modulo 37.  The `n=0,eta=1` row has `X=0`; it does not lift because at
`i=6`

```text
q(0)=-1-2i = 24 mod 37
```

is a nonsquare.  Thus an affine `C0` point with rational `u` lies in
one of the two common disks of `P` and `-P`.

## 5. Formal-group coefficient

Lift the two square roots of `-1` to

```text
j+ = 117 mod 37^2,
j- = -117 mod 37^2.
```

They satisfy `j^2+1=0 mod 37^2` and reduce to `6,31`.
Put `R=12P`, and use the formal parameter `t=-x/y` at infinity.  Exact
group arithmetic gives

```text
t(R+) = 629 = 37*17 mod 37^2,
t(R-) = 703 = 37*19 mod 37^2.
```

For `z in Z_37`,

```text
t([z]R+) = 37*17*z + O(37^2),
t([z]R-) = 37*19*z + O(37^2).
```

Translation at `P=(2,2)` has

```text
x(P+S)=2+4t(S)+O(t(S)^2).
```

Hence

```text
(x_+(P+[z]R)-x_-(P+[z]R))/37 = 29z mod 37.
```

At `-P` the coefficient is `8z mod 37`.  Both are units.  All
nonlinear coefficients become divisible by 37 after division by 37,
so the specialized Strassmann/valuation induction has the unique zero
`z=0` in either disk.

Indeed, for `Q=kG+epsilon*T` in the disk of `sP`, `s=+1` or `-1`, the
same parameter at both split places is

```text
z = (k/m-s)/12 in Z_37.
```

This is integral because `37` does not divide `12m`; the elliptic
logarithm kills the 2-torsion.  Therefore rational `X` forces
`Q=sP`.  Since `X=2u^2`, the affine lifts have exactly `u=+1,-1`.

## 6. Lean formalization status

The blockers described in earlier versions of this note are closed by
specialized Lean proofs. The implementation includes:

- Gaussian UFD and square-class support;
- explicit 2-isogeny descent and weak Mordell--Weil arguments;
- exact rank, torsion, and index-saturation results;
- good-reduction and split-prime finite computations;
- paired formal-parameter and uniqueness arguments;
- the final theorem
  `GaussianSession1Completion.quadratic_cubic_impossible_sharipov`.

The assembly is in
[`GaussianSession1Completion.lean`](../../lean/Cuboid2/QuadraticReduction/GaussianSession1Completion.lean)
and is consumed by the public theorem in
[`Cuboid2/Main.lean`](../../lean/Cuboid2/Main.lean). Closed finite
propositions use `native_decide`; database ranks and PARI analytic ranks are
not premises.

For independent discovery confirmation only, LMFDB records

```text
E0: 2.0.4.1-87040.4-l1,  rank_bounds=[1,1], torsion Z/2;
E1: 2.0.4.1-87040.4-ba1, rank_bounds=[0,0], torsion Z/2.
```

On the LMFDB model

```text
y^2=x^3-i*x^2+(-1-4i)*x-4+i
```

the stored free generator is `(-1-i,-1-2i)`.  The change
`x_new=x_old+i`, `y_new=y_old` carries it to
`H=(-1-2i,-1-2i)` on `E0`, and direct addition gives
`P=-H+T`.  Thus the database generator is equivalent to `P` modulo
torsion. This is a useful consistency check, but its generator status is
deliberately not a premise of the formalization. These database rows are not
used by the finite verifier.
