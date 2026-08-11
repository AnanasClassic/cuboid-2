# C041 simplification audit

## Result

No proof-quality replacement for C041 was found.  The existing
Schaefer--Stoll descent, index-independent `7/23` Mordell--Weil sieve, and
exact `p=7` Coleman step remain proof-critical.

The investigation did produce exact structural negative results:

1. the genus-three curve has no hidden automorphisms over `Qbar`;
2. its only positive-genus double quotients are the expected elliptic curve
   and `D+`;
3. the elliptic quotient is birational over `Q` to the already occurring
   curve `E1`;
4. the Prym is `Jac(D+)`, which is geometrically simple;
5. `Jac(D+)` has no nontrivial `Q`-rational endomorphism;
6. a rational Richelot neighbour exists, but it is another simple genus-two
   Jacobian rather than an elliptic product.

All new exact calculations are replayed by
`research/proof_simplification/c041_structure.py`.  Its JSON output is a
checksum-protected audit artifact.  The script is not inserted into the
logical proof of C041.

## 1. Genus-three quotient structure

Let

\[
 C_3:\quad r^2=4u^8-8u^2+5.
\]

Besides the hyperelliptic involution `j:(u,r)->(u,-r)`, there is
`s:(u,r)->(-u,r)`.  The two positive-genus quotients are

\[
\begin{array}{rcll}
 C_3/\langle s\rangle:
 &r^2&=4a^4-8a+5,&a=u^2,\\[1mm]
 C_3/\langle sj\rangle:
 &R^2&=4a^5-8a^2+5a,&a=u^2,\ R=ur.
\end{array}
\]

The differential decomposition is exact:

\[
H^0(C_3,\Omega^1)
=\langle u\,du/r\rangle
\langle du/r,u^2du/r\rangle.
\]

The first summand comes from the elliptic quotient and the second from
`D+`.  Consequently

\[
 \operatorname{Jac}(C_3)\sim_{\mathbf Q}
 E_0\times\operatorname{Jac}(D_+).
\]

### Exact identification of the elliptic quotient

Put `t=a-1` and

\[
 m=\frac{r-1-4t}{t^2}.
\]

Substitution gives

\[
(m^2-4)t^2+(8m-16)t+2m-8=0,
\]

whose discriminant is

\[
-8(m-2)(m^2-10m+8).
\]

The exact birational coordinates

\[
x=2-\frac m2,\qquad
y=\frac{(m^2-4)t+4m-8}{4}
\]

satisfy

\[
y^2=x^3-5x+4.
\]

Thus `E0` is `E1`, not a new lower-rank quotient.  Its rank is one.  The
Prym of `C3 -> E0` is the rank-one genus-two factor `Jac(D+)`; the quotient
decomposition therefore exposes the existing bottleneck rather than
removing it.

### Complete automorphism audit

For a hyperelliptic curve of genus at least two, every non-hyperelliptic
automorphism induces a projective transformation preserving the branch
divisor.  Write such a transformation as

\[
u\longmapsto\frac{\alpha u+\beta}{\gamma u+d}.
\]

On the chart `d=1`, coefficient comparison in

\[
(\gamma u+1)^8
f\!\left(\frac{\alpha u+\beta}{\gamma u+1}\right)
=\lambda f(u),
\qquad f(u)=4u^8-8u^2+5,
\]

saturated by
`inverse_det*(alpha-beta*gamma)-1`, has reduced Gröbner basis

```text
-alpha + inverse_det,
lambda - 1,
(alpha - 1)*(alpha + 1),
beta,
gamma.
```

On the chart `d=0`, normalized by `gamma=1` and saturated by
`inverse_det*beta-1`, the reduced basis is `[1]`.  Hence the complete
`PGL2(Qbar)` branch stabilizer is `{u,-u}`.  Including the hyperelliptic
involution gives

\[
\operatorname{Aut}_{\overline{\mathbf Q}}(C_3)
\simeq C_2\times C_2.
\]

There are therefore no further degree-two elliptic or genus-two quotients
over `Q` or a small extension (indeed, over any extension).

## 2. Absolute simplicity of `Jac(D+)`

At the good prime `3`, exact counts give

\[
\#D_+(\mathbf F_3)=6,\qquad
\#D_+(\mathbf F_9)=14,
\]

and the Weil polynomial

\[
P_3(T)=T^4+2T^3+4T^2+6T+9.
\]

It is irreducible over `Q` and ordinary.  The exact root-ratio resultant is

\[
\begin{aligned}
\operatorname{Res}_T(P_3(T),P_3(zT))
={}&81(z-1)^4\\
&\cdot(3z^4+2z^3+2z^2+2z+3)^2\\
&\cdot(9z^4+12z^3+10z^2+12z+9).
\end{aligned}
\]

After removing the diagonal factor `(z-1)^4`, the remaining polynomial has
gcd one with every cyclotomic polynomial whose degree is at most 16.
This list is exhaustive: a quotient of two roots lies in a compositum of
degree at most 16, and `phi(n)>=sqrt(n/2)` reduces the finite check to
`n<=512`.  Thus no quotient of two distinct Frobenius roots is a root of
unity.  The reduction is absolutely simple, so

\[
\operatorname{Jac}(D_+)
\quad\text{is geometrically simple over }\mathbf Q.
\]

This rules out:

- a `Q`-isogeny to a product of elliptic curves;
- a splitting after a small extension;
- any degree-two elliptic quotient of `D+`;
- a bielliptic shortcut;
- a Richelot isogeny whose target is an elliptic product.

### Rational endomorphisms

The ordinary absolutely simple reductions at `3` and `13` have irreducible
Frobenius polynomials with `D4` Galois group.  PARI's exact subfield
calculation gives their unique quadratic subfields:

\[
\mathbf Q(\sqrt3),\qquad \mathbf Q(\sqrt{29}),
\]

respectively.  A `Q`-rational endomorphism commutes with Frobenius and hence
embeds into both Frobenius fields.  Since the fields have no common
nontrivial subfield,

\[
\operatorname{End}_{\mathbf Q}(\operatorname{Jac}(D_+))
\otimes\mathbf Q=\mathbf Q.
\]

This excludes rational real multiplication and rational nontrivial
correspondences.  The calculation does not claim to determine every
geometric endomorphism of the already absolutely simple surface.

## 3. Richelot route

The quartic factor of `D+` has Galois group `D4` and factors over `Q(i)` as

\[
4a^4-8a+5=
(2a^2+2ia-1-2i)(2a^2-2ia-1+2i).
\]

Pairing the branch points `0` and infinity supplies the third Richelot
factor.  The determinant is `-8i`, and the exact bracket construction
descends to the rational dual model

\[
\widehat D:\quad
Y^2=-2(2a^2-4a+1)(4a^4+4a^2+5).
\]

The quartic factor on the right is irreducible over `Q`.  More importantly,
the source Jacobian is geometrically simple, so its Richelot-isogenous target
is also geometrically simple.  This is a genuine rational `(2,2)`-isogeny,
but it changes one genus-two Jacobian into another and does not turn the rank
or square-abscissa problem into elliptic arithmetic.

The bracket convention is the standard one
`[A,B]=A'B-AB'`; see the explicit Richelot formulas in the
[Magma handbook](https://magma.maths.usyd.edu.au/magma/handbook/text/1614)
and Bruin--Doerksen,
[The arithmetic of genus two curves with (4,4)-split Jacobians](https://arxiv.org/abs/0902.3480).

## 4. Direct Chabauty on `C3`

This route is attractive because

\[
\operatorname{rank}\operatorname{Jac}(C_3)
=1+1=2<3.
\]

It does not, however, remove the existing local work.

At `p=3`,

\[
\#C_3(\mathbf F_3)=6,
\]

and the six disks are exactly the reductions of the two rational points at
infinity and `(u,r)=(+/-1,+/-1)`.  This looks ideal.  The annihilating
differential inherited from the `D+` factor reduces to a multiple of

\[
(1-u^2)\frac{du}{r}.
\]

It vanishes in all four affine disks, and `3<=2g`.  The ordinary one-disk
Coleman bound therefore does not apply.  A new exact four-disk
Strassmann calculation would be required.  No such proof-quality
calculation was obtained, so the discarded `p=3` shortcut was not restored.

At `p=7`, exact enumeration gives

\[
\#C_3(\mathbf F_7)=10.
\]

Besides the six occupied disks there are four disks

\[
u=3,4,\qquad r=2,5.
\]

Under the map to `D+`, these are exactly the two extra square-abscissa
classes `+/-5` in the torsion-zero component.  The existing `p=23`
Mordell--Weil sieve is what proves that no rational point occupies them.
Direct genus-three Chabauty therefore repackages the same sieve obligation.

## 5. Can the existing C041 proof itself be shortened?

### Rank and torsion

The geometric simplicity result rules out an elliptic-factor rank proof.
The rational Richelot neighbour does not split.  No smaller unconditional
rank-one certificate was found.  The current Schaefer--Stoll computation is
therefore retained.  Within that computation the local condition at `17` is
genuinely active:

```text
512 -> 64 -> 8 -> 4.
```

Omitting `17` leaves an eight-class upper bound and does not prove rank one.

### The second sieve prime

At `7`, the exact square-abscissa list contains the extra classes `+/-5`.
The `23` table, compared modulo `21` with the index-independent argument,
removes precisely those classes.  A proof that uses the current `p=7`
Coleman calculation but simply deletes the `p=23` step is invalid.  No
single-prime replacement with a complete exact local argument was found.

### Better Chabauty prime

The tempting prime `3` has the minimal residue set but a vanishing
annihilator in the four affine disks.  The prime `7` has a nonvanishing
annihilator on the surviving disks but four unoccupied square-abscissa
disks before the MW sieve.  The current pairing of the `7/23` sieve with the
`p=7` formal logarithm remains the shortest fully certified route found.

### Covering collections and local/global shortcuts

The octic `4u^8-8u^2+5` is irreducible over `Q`, its geometric automorphism
group is only `C2 x C2`, and its non-elliptic Prym is geometrically simple.
These facts do not prove that every possible covering collection is useless,
but they rule out the obvious low-degree quotient and split-Jacobian
mechanisms.  No direct local/global square-class argument was found that
classifies `C3(Q)` or the square abscissas on `D+`.

## 6. Final status

This audit improves exposition and closes tempting structural detours, but it
does **not** establish Level 2 or Level 3:

- no proof dependency of C041 is replaced;
- `p=23` remains necessary in the current argument;
- the full exact 2-descent remains the certified rank proof;
- the theorem remains fully proved by the original C041 machinery.

The negative results are intentionally kept outside the clean paper's main
logical chain.  They belong in this audit, not as additional prerequisites
for the conjecture.
