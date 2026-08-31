# Completion of the quadratic--cubic case

This note records the logical chain that closes C010.  It is deliberately an
overview: the large rational functions and the exact local-image tables live
in the cited certificates.  Every implication used below is over
characteristic zero.  Finite-field calculations occur only in the certified
Mordell--Weil sieve and Coleman argument, where they are used to classify
rational points rather than as a bounded search.

There are two unrelated signs in the argument.  They must not be conflated.

* The **physical sign** $\sigma\in\{+1,-1\}$ is the sign in the constant
  coefficient $B=\sigma d^2$ of a hypothetical integral quadratic factor.
* The sign $\epsilon\in\{+1,-1\}$ below is a square-class sign forced by
  valuations of two rational functions on the elliptic quotient.

Both physical branches have the same two common square characters.  The
argument excludes an admissible point using only those common characters, so
it applies to both values of $\sigma$.

## 1. Exact elliptic transport and the common characters

C035 gives a lossless compact model of each signed-square factor locus,
including its rational inverse and its complete admissible denominator audit.
The low-degree transport certificate then gives a birational map, with
inverse, from the resulting admissible compact curve $C_8$ to

$$
 E_1:\quad y^2=x^3-5x+4.
$$

Both compositions are verified in the respective characteristic-zero
function fields, and the projective base loci and denominator-zero fibres are
enumerated separately.  Thus every
genuine factor reaches $E_1$ through an exact two-way chain, but this does
**not** prove C025 as worded: a direct birational normalization of the
original plane model $H(q,A)=0$ remains a separate open identification.
The completion bypasses that identification and is not an inference from the
Frobenius fingerprint.

Write $\mathcal U,\mathcal V$ for the two transported functions used by the
signed-square cover.  For a genuine factor the three physical square
characters are

$$
\begin{array}{c|c}
\sigma=+1&\mathcal U\mathcal V,\quad
 1-\mathcal U\mathcal V,\quad 1-\mathcal V/\mathcal U,\\[2mm]
\sigma=-1&\mathcal U\mathcal V,\quad
 1-\mathcal U\mathcal V,\quad 1-\mathcal U/\mathcal V.
\end{array}
$$

Thus $\mathcal U\mathcal V$ and $1-\mathcal U\mathcal V$ are required
to be rational squares in both physical branches.  This notation is local to
the transport and should not be confused with the earlier reciprocal
coordinate $U=s+s^{-1}$.

Translate by the rational two-torsion point $T=(1,0)$:

$$
 X=\frac{x-3}{x-1},\qquad
 Y=\frac{2y}{(x-1)^2}.
$$

This is an involution of $E_1$.  Put

$$
 L=2X+Y-2,\qquad M=X^2+2Y-1,
 \qquad k=\frac{Y+2}{X},\qquad h=X+1.
$$

Exact reduction modulo $Y^2-X^3+5X-4$ gives

$$
 XM=(Y+2)L
$$

and, for an explicitly recorded rational function $g$,

$$
 1-\mathcal U\mathcal V
   =2(X+1)LMg^2.
$$

The scalar $2$ in this identity is essential.  On the open set where the
displayed divisions are legal, $M=kL$, and squarehood of the second common
character implies

$$
 z^2=2kh                                                     \tag{1}
$$

for some $z\in\mathbf Q$.  Substitution in the elliptic equation gives

$$
 h^2-(k^2+2)h+(k^2+4k-4)=0.                                \tag{2}
$$

The identities and all exceptional fibres are replayed by
`research/arithmetic_geometry/low_degree_transport.py` and
`research/arithmetic_geometry/product_character_simplification.py`.

## 2. Square-class valuation lemma

Assume first that $k,h,z\ne0$ and that (1)--(2) hold.  For every odd prime
$\ell$, a valuation comparison in (2) shows that
$v_\ell(k)$ is even.  Indeed, if $v_\ell(k)>0$, then $h$ is a unit; if
$v_\ell(k)<0$, the two possible root valuations are $0$ and
$2v_\ell(k)$.  In either case, the parity of
$v_\ell(2kh)$ gives the assertion.

At $2$, the discriminant of (2), viewed as a quadratic in $h$, is

$$
 \Delta=k^4-16k+20.
$$

If $v_2(k)=0$, then $\Delta\equiv5\pmod8$.  If
$v_2(k)>1$, then $\Delta/4\equiv5\pmod8$.  Both are impossible for a
rational square.  If $v_2(k)<0$, the two root valuations are again $0$
and $2v_2(k)$, and (1) forces $v_2(k)$ to be odd.  The remaining positive
case is $v_2(k)=1$.  Consequently

$$
 k=2\epsilon u^2,qquad h=\epsilon v^2                   \tag{3}
$$

with $u,v\in\mathbf Q^\times$ and
$\epsilon\in\{+1,-1\}$.  The second equality follows from (1), since
the square class of $h$ is that of $2k$.

For $\epsilon=-1$, treating (2) as a quadratic in $u^2$ forces a rational
point on

$$
 W^2=-(v^2+2)(v^4+v^2-4).                                  \tag{4}
$$

Write $v=m/n$ in lowest terms and clear the denominator.  If $m,n$ are
odd, the right side of (4) is $6\pmod8$.  If $m$ is odd and $n$ is
even, it is $3$ or $7\pmod8$.  If $m$ is even and $n$ is odd, then
the two factors have 2-adic valuations $1$ and respectively $2$ or
$4$, so their product has odd valuation $3$ or $5$.  All cases
contradict squarehood.  Hence the negative square-class sign is impossible.

For $\epsilon=+1$, put $k=2u^2$.  The discriminant of (2) is a square
only if

$$
 r^2=4u^8-8u^2+5.                                         \tag{5}
$$

This reduction is exact on the stated open set.  Its valuation proof and the
direct audit of the omitted zeros and poles are in
`research/arithmetic_geometry/product_squareclass_valuation.py`.

## 3. The square-abscissa theorem on the genus-two curve

Set

$$
 C:\quad R^2=4a^5-8a^2+5a,
 \qquad D=[(1,1)-\infty],\qquad T_0=[(0,0)-\infty].
$$

The exact arithmetic theorem needed here is

$$
 \{Q\in C(\mathbf Q):a(Q)\in\mathbf Q^2\}
   =\{\infty,(0,0),(1,1),(1,-1)\}.                         \tag{6}
$$

Only square abscissas are classified; no stronger assertion about all of
$C(\mathbf Q)$ is used.

Here is the proof of (6).  A Schaefer--Stoll 2-descent with
$S=\{2,5,17\}$ starts with a 512-element norm kernel.  The exact local
images leave successively 64 classes at $2$, eight at $5$, and four at
$17$; the last prime is essential, not automatic.  Hence
$\dim\operatorname{Sel}_2(J/\mathbf Q)=2$.
The classes of $D$ and $T_0$ are independent modulo $2J(\mathbf Q)$.
Reduction at good primes gives
$\gcd(\#J(\mathbf F_3),\#J(\mathbf F_7))=\gcd(22,42)=2$,
so $J(\mathbf Q)_{\rm tors}=\langle T_0\rangle$; moreover $D$ is of
infinite order.  Therefore

$$
 J(\mathbf Q)\simeq\mathbf Z\oplus\mathbf Z/2\mathbf Z,
 \qquad \operatorname{rank}J(\mathbf Q)=1.
$$

There is no hidden saturation assumption in the following sieve.  If
$J(\mathbf Q)=\mathbf ZG\oplus\langle T_0\rangle$, independence modulo
two lets us replace $G$ by $G+T_0$, if needed, and write
$D=mG$ with $m$ odd.  At $p=7,23$, exact group arithmetic gives

$$
 J(\mathbf F_p)=\langle\bar D\rangle\oplus\langle\bar T_0\rangle,
 \qquad \operatorname{ord}(\bar D)=21,231,
$$

respectively.  If $r=\operatorname{ord}(\bar G)$, then
$r/\gcd(r,m)=\operatorname{ord}(m\bar G)=N$ and $r\mid2N$, where
$N=21$ or $231$.  Since $m$ is odd, this forces
$r=N$ and $\gcd(m,N)=1$.  Thus the coefficient of a rational divisor
relative to $G$, after multiplication by $m^{-1}$, is a well-defined
coefficient relative to $D$, and the coefficients at the two primes agree
modulo $21$.

Enumerating the points with square abscissa in the two finite fields gives,
in the torsion-zero component,

$$
 S_7=\{0,\pm1,\pm5\}\pmod {21},
$$

while the $p=23$ possibilities reduce modulo $21$ to

$$
 S_{23}=\{0,\pm1,\pm2,\pm3,\pm4,\pm9\}\pmod {21}.
$$

Their intersection is $\{0,\pm1\}$.  The torsion component contributes
the known point $(0,0)$.  In particular, the two extra square-abscissa
disks at $p=7$, represented by $(a,R)=(2,\pm1)$, have coefficients
$\pm5$ and are removed by the $p=23$ condition.

It remains to prove uniqueness in the four surviving disks.  The exact
formal logarithm of $42D$ modulo $7$ has direction $(1,4)$.  Hence an
exact $7$-adic differential annihilating $J(\mathbf Q)$ may be chosen
whose reduction is

$$
 \bar\eta=(4-a)\frac{da}{2R}.
$$

The reduced differential's only possible
zero in the affine $a$-line modulo $7$ is $a=4$, but

$$
 4a^5-8a^2+5a\bigm|_{a=4}=5\pmod7,
$$

which is not a square.  Thus $\bar\eta$ is nonzero at every point of
$C(\mathbf F_7)$.  Since $7>2g=4$, the standard local
Coleman--Chabauty bound gives at most one rational point in each surviving
residue disk.  The four displayed points already occupy them, proving (6).

The descent, sieve, formal-log calculation, and canonical finite-field tables
are replayed by
`research/arithmetic_geometry/product_genus2_two_descent.py`,
`research/arithmetic_geometry/product_genus2_square_sieve.py`, and
`research/arithmetic_geometry/product_genus2_p7_formal_log.py`.  A detailed
standalone proof is in
`research/arithmetic_geometry/product_genus2_square_abscissa.md`.

## 4. Pullback and the exceptional value $a=1$

A rational point of (5) maps to a square-abscissa point of $C$ by

$$
 a=u^2,qquad R=ur.
$$

The point $(a,R)=(0,0)$ does not lift rationally to (5), because it would
require $r^2=5$.  The point at infinity is a projective boundary fibre.
Thus (6) leaves only $a=1$, so $u=\pm1$ and $r=\pm1$.  Then
$k=2$, and the two roots of (2) are $h=2,4$, giving the two points

$$
 (X,Y)=(1,0),\qquad (X,Y)=(3,4)
$$

on $E_1$.

This last value must be checked before dividing by $L$.  At $(1,0)$,
both $L$ and $M$ vanish, so the implication from squarehood of
$1-\mathcal U\mathcal V$ to (1) is not reversible there.  Direct
evaluation of the other common character gives the square class $1/2$,
which is not a square in $\mathbf Q$.  The point $(3,4)$ maps back to
the old elliptic point $P=(0,2)$, where the original parameter is a
boundary value (the corresponding common invariant is zero).  Hence neither
point comes from an admissible factor.

The same direct exceptional-fibre table also handles $X=0$, poles or zeros
of $k,h,g$, $L=0$, points at infinity, and the base loci of both
birational maps.  In particular, the inverse base point $-4P$ has
nonsquare $\mathcal U\mathcal V$, while the stored points $P,T,P+T$
map to boundary fibres.  No point is discarded merely because a displayed
denominator vanishes.  C032 and C033 independently close the compact-$V$
and reverse-subresultant denominator branches.

## 5. Consequences

By the two-way compact reduction C035, every admissible quadratic factor has
one of the two physical signs $\sigma$ and reaches the compact curve used
above.  Each sign supplies the two common square characters, and the
preceding argument shows that their simultaneous squarehood has no
admissible rational point.  Therefore the residual quadratic--cubic split is
impossible.  This proves C010 and, equivalently, closes C020 without needing
a classification of every rational point on either genus-33 full cover or a
proof of C025.

C004 already excludes the linear--quartic split.  C005 is the exact
machine-verified exclusion of the symmetric $5+5$ split.  The complete
factorization classification C003 then proves Sharipov's second cuboid
conjecture for coprime positive integers $p\ne q$.  The conclusion is a
computer-assisted exact proof because the C005 replay and several symbolic
identities are certified by exact arithmetic; it is not a height-bounded or
probabilistic computation.

## 6. Conservative ledger status

The exact certificates have been replayed from the completed tree.  The
repository summaries now record C010 and C020 as `PROVED`, with separate
claims C039--C041 for the compact transport, valuation descent, and
square-abscissa theorem, and C042 for the final conjecture.

C025 deliberately remains `OPEN`: the proof uses the lossless C035 compact
locus and its own map to $E_1$, not a direct normalization of the original
plane model $H(q,A)=0$.  C008 and C016 likewise retain their older
conditional geometry status; they are no longer dependencies of the proof
but are not thereby independently verified.  The physical sign $\sigma$
and square-class sign $\epsilon$ are kept distinct throughout the ledger
and paper, and the exceptional $a=1$, $L=M=0$ point is checked by its
continued character value rather than by an invalid division by $L$.
