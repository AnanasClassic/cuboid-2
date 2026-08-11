# Second simplification audit for C041

## Status

Target A succeeds, with one qualification that is essential to the proof:
plain Chabauty/Strassmann on the full \(3\)-adic residue disks does **not**
classify the rational points.  The unique annihilating Coleman function has
two simple \(\mathbf Q_3\)-zeros in each of the four affine disks.  An exact
integral Mordell--Weil lattice argument, using only

\[
 \#J(\mathbf F_7)=42,\qquad
 \operatorname{ord}(\bar D)=21,
\]

shows that a rational point can occupy only the smaller subdisk
\(a-1\in9\mathbf Z_3\).  On that subdisk the annihilating primitive is
linear modulo \(3\).  This removes the four extra \(3\)-adic zeros and proves

\[
\boxed{
C_3(\mathbf Q)=
\{\infty_+,\infty_-\}
\mathbin{\cup}
\{(u,r):u=\pm1,\ r=\pm1\}.}
\tag{1}
\]

Consequently the old square-abscissa theorem C041 follows without the
\(p=23\) Mordell--Weil sieve, the \(p=7\) square-abscissa tables, or the
\(p=7\) Coleman/formal-log calculation.

The exact Target A replay is

```text
research/proof_simplification_2/c3_p3_chabauty.py
research/proof_simplification_2/c3_p3_chabauty.json
tests/test_c3_p3_chabauty.py
```

The JSON artifact is canonical and checksum-protected.  The calculation uses
exact rational and finite-field arithmetic; no finite-precision \(3\)-adic
approximation is used.

Target B is mathematically successful but is **not adopted as a
simplification**.  The exact rational Richelot descent proves the same
rank-one, torsion, and modulo-\(2\) inputs, and every correspondence, twist,
local image, and pairing convention is certified.  However, its complete
proof object is substantially larger than the existing Schaefer--Stoll
certificate.  Under the explicit criterion in the task, this is a valid
alternative proof, not Level 2.

Thus the audit reaches Level 1.  `paper/clean2.tex` uses the direct \(C_3\)
classification while retaining the shorter existing rank certificate.  The
original proof and the Richelot alternative both remain independently
runnable.

## 1. Inputs and scope

Put

\[
\begin{aligned}
C_3&:\quad r^2=4u^8-8u^2+5,\\
D_+&:\quad R^2=4a^5-8a^2+5a,\\
E_1&:\quad y^2=x^3-5x+4,
\end{aligned}
\]

and let

\[
D=[(1,1)-\infty],\qquad T=[(0,0)-\infty]
\]

in \(J=\operatorname{Jac}(D_+)\).  The already certified quotient maps are

\[
 (u,r)\longmapsto (u^2,r)
\]

to the genus-one quartic birational to \(E_1\), and

\[
 \pi:(u,r)\longmapsto(a,R)=(u^2,ur)
\tag{2}
\]

to \(D_+\).  They give

\[
 \operatorname{Jac}(C_3)\sim_{\mathbf Q}
 E_1\times J.
\tag{3}
\]

The relevant certified arithmetic input is

\[
\operatorname{rank}E_1(\mathbf Q)=1,\qquad
\operatorname{rank}J(\mathbf Q)=1,\qquad
J(\mathbf Q)_{\mathrm{tors}}=\langle T\rangle\simeq\mathbf Z/2\mathbf Z.
\tag{4}
\]

The elliptic rank and quotient decomposition are checked by

```text
research/frobenius_audit/candidate_544c_rank_descent.json
research/proof_simplification/c041_structure.json
```

The genus-two statements in (4), together with the independence of \(D,T\)
modulo \(2\), are now independently certified in two ways.  The new clean
proof retains

```text
research/arithmetic_geometry/product_genus2_two_descent.json
```

The alternative Richelot audit is

```text
research/proof_simplification_2/richelot_composition_check.py
research/proof_simplification_2/richelot_isogeny_descent.json
```

The relevant embedded checksums are verified before their conclusions are
used.  Neither rank certificate assumes that \(D\) is primitive.
The degree of the quotient isogeny in (3) is a power of \(2\), hence a
\(3\)-adic unit.  Its tangent-space decomposition is therefore exact at
\(p=3\):

\[
H^0(C_3,\Omega^1)
=
\langle u\,du/r\rangle
\oplus
\langle du/r,u^2du/r\rangle.
\tag{5}
\]

The first summand is the \(E_1\) direction and the second is the \(D_+\)
direction.  The logarithm of a non-torsion point on each rank-one factor is
nonzero.  It follows from (3)--(5) that the annihilator of
\(\operatorname{Jac}(C_3)(\mathbf Q)\) is exactly one-dimensional.  Thus
there is no second annihilating differential with which to avoid the four
exceptional affine disks.

No step below assumes that \(D\) is a primitive generator of \(J(\mathbf
Q)\).  No step uses C025, a bounded search, a finite congruence sieve as a
completeness theorem, or a Frobenius fingerprint.

## 2. Direct \(p=3\) genus-three Chabauty

### 2.1 The six residue disks

Both \(C_3\) and \(D_+\) have good reduction at \(3\).  Exact enumeration
gives

\[
\#C_3(\mathbf F_3)=6.
\]

There are four affine points,

\[
(u,r)=(1,\pm1),\ (-1,\pm1)\pmod3,
\]

and two points at infinity because the leading coefficient \(4\) is a
square.  These are exactly the reductions of the six points displayed in
(1).  Therefore every rational point lies in one of six known disks.  This
finite enumeration only identifies the disks; completeness comes from the
Coleman and integral-lattice arguments below.

### 2.2 Exact annihilator

Use the standard basis

\[
\frac{du}{r},\qquad
\frac{u\,du}{r},\qquad
\frac{u^2\,du}{r}.
\]

On \(D_+\), put

\[
\omega_0=\frac{da}{R},\qquad
\omega_1=\frac{a\,da}{R}.
\]

Let

\[
\ell_j=\int_0^D\omega_j,\qquad
\lambda=\frac{\ell_1}{\ell_0}.
\tag{6}
\]

The denominator is nonzero by the exact valuation calculation below.
Since \(J(\mathbf Q)\) has rank one, its annihilator in
\(\langle\omega_0,\omega_1\rangle\) is

\[
\eta_D=(\lambda-a)\frac{da}{R}.
\tag{7}
\]

This is independent of the unknown index of \(D\): if \(D=mG\) after a
torsion shift, then \(\log D=m\log G\), so \(D\) and a primitive generator
determine the same line over \(\mathbf Q_3\).  Pulling (7) back through (2)
gives, up to the unit factor \(2\),

\[
\eta=(\lambda-u^2)\frac{du}{r}.
\tag{8}
\]

The \(E_1\) rank direction forces the coefficient of \(u\,du/r\) in an
annihilator to vanish, while the nonzero \(J\)-logarithm leaves exactly the
line (8).  This proves, rather than assumes, that the full Chabauty
annihilator has dimension one.

### 2.3 Exact computation of \(\lambda\)

In \(J(\mathbf F_3)\), \(\bar D\) has order \(11\).  Exact Cantor arithmetic
computes \(11D\).  If its Mumford polynomial is shifted by \(a=1+t\), write

\[
u_{11D}(1+t)=t^2+bt+c.
\]

The certificate obtains

\[
\begin{array}{c|ccc}
 &b&c&b^2-4c\\ \hline
v_3&1&2&4\\
\text{unit mod }3&2&1&1.
\end{array}
\tag{9}
\]

The two support points therefore lie in the two branches above \(a=1\);
their \(t\)-difference has valuation \(2\).  Their reduction is the
principal divisor

\[
(1,1)+(1,-1)-2\infty=\operatorname{div}(a-1).
\]

Around \(a=1\), the first two local primitives are

\[
\begin{aligned}
H_0(t)&=
t-\frac94t^2+\frac{115}{24}t^3+O(t^4),\\
H_1(t)&=
t-\frac74t^2+\frac{79}{24}t^3+O(t^4).
\end{aligned}
\tag{10}
\]

If \(t_+,t_-\) are the two roots in (9), divide
\(H_j(t_+)-H_j(t_-)\) by \(t_+-t_-\).  The exact power-difference
quotients in degrees \(1,2,3\) are

\[
1,\qquad -b,\qquad b^2-c.
\]

All coefficients of the inverse square-root series are \(3\)-integral:
the constant term is a \(3\)-adic unit and the binomial denominators are
powers of \(2\).  For a term of primitive degree \(n\), the divided
power-difference has valuation at least \(n-1\), while integration loses at
most \(v_3(n)\).  Hence every omitted term for \(n\ge4\) has valuation

\[
n-1-v_3(n)\ge3.
\tag{11}
\]

This is an elementary inequality for every \(n\ge4\), not a
finite-precision truncation assumption.  Equations (9)--(11) certify

\[
\lambda\equiv7\pmod{27},\qquad
v_3(\lambda-1)=1,\qquad
\frac{\lambda-1}{3}\equiv2\pmod3.
\tag{12}
\]

They also give

\[
v_3(\ell_0(11D))=2.
\]

Since \(11\) is a \(3\)-adic unit,

\[
v_3(\ell_0(D))=2.
\tag{13}
\]

Only the exact residue information (12)--(13), with the universal tail
bound (11), is used below.

## 3. The four exceptional affine disks

### 3.1 Why naive Strassmann fails

Fix an affine center

\[
(u_0,r_0)=(s,\rho),\qquad s,\rho\in\{\pm1\},
\]

and use

\[
u=s+t,\qquad t=3z.
\]

Write \(\delta=\lambda-1\).  Expanding (8), integrating from the known
center, substituting \(\delta=3\delta_0\), and dividing by \(9\) gives,
up to the nonzero scalar determined by \(\rho\),

\[
\frac{F_{s,\rho}(3z)}9
\equiv 2z-sz^2\pmod3,
\qquad \delta_0\equiv2\pmod3.
\tag{14}
\]

The tail control is exact.  Terms containing \(\delta\) in primitive degree
\(n\ge2\) have normalized valuation at least

\[
n-1-v_3(n)\ge1.
\]

For the remaining terms, degrees \(2\) and \(3\) are computed explicitly;
the cubic coefficient vanishes modulo \(3\), and all degrees \(n\ge4\)
have normalized valuation

\[
n-2-v_3(n)\ge1.
\]

Thus (14) is the actual Weierstrass reduction, not a numerical
approximation.

For \(s=1\), the reduction is \(2z-z^2\), with two simple roots
\(z=0,2\).  For \(s=-1\), it is \(2z+z^2\), with two simple roots
\(z=0,1\).  The overall sign for \(\rho=-1\) does not change the roots.
Hensel/Weierstrass preparation therefore gives exactly two simple
\(\mathbf Q_3\)-zeros in each affine residue disk:

\[
\begin{array}{c|c|c}
u_0&z\bmod3&u\bmod9\\ \hline
 1&0,\ 2&1,\ 7\\
-1&0,\ 1&8,\ 2.
\end{array}
\tag{15}
\]

The zero \(z=0\) is the known rational point.  The second zero is a genuine
\(\mathbf Q_3\)-zero of the Coleman function.  It may not be discarded
merely because it is not among the known rational points.  Consequently:

> The proposed proof “all six residue disks are occupied, so one point per
> disk” is false, and plain Strassmann on the full \(3\)-adic disks does not
> prove (1).

Across the four affine disks there are eight Coleman zeros, and the two
infinity disks contribute two more.  The annihilating function therefore
has ten \(\mathbf Q_3\)-zeros although only six are rational.

### 3.2 Exact \(3\)-saturation from the reduction at \(7\)

The needed refinement uses no primitive-generator assumption.  From (4),
write

\[
J(\mathbf Q)=\mathbf ZG\oplus\langle T\rangle,\qquad
D=mG+\epsilon T.
\]

The certified independence of \(D,T\) in \(J(\mathbf Q)/2J(\mathbf Q)\)
implies that \(m\) is odd.  Replacing \(G\) by \(G+\epsilon T\), which is
valid because \(m\) is odd, gives

\[
D=mG.
\tag{16}
\]

At the good prime \(7\), exact finite-Jacobian arithmetic gives

\[
\#J(\mathbf F_7)=42,\qquad
\operatorname{ord}(\bar D)=21.
\tag{17}
\]

Let \(q=\operatorname{ord}(\bar G)\).  Then \(q\mid42\), while (16)--(17)
give

\[
\frac{q}{\gcd(q,m)}=21.
\tag{18}
\]

Thus \(q\) is \(21\) or \(42\).  The latter would force
\(\gcd(q,m)=2\), impossible because \(m\) is odd.  Therefore

\[
q=21,\qquad \gcd(m,21)=1,
\tag{19}
\]

and in particular \(3\nmid m\).  Combining (13), (16), and (19) gives

\[
v_3(\ell_0(G))=2.
\tag{20}
\]

This is the only \(p=7\) input in the new local classification.  It uses the
group order and the order of \(\bar D\), not a square-abscissa class table,
a residue sieve, a \(7\)-adic logarithm, or a Coleman calculation.

### 3.3 Restricting rational points to \(a-1\in9\mathbf Z_3\)

Under (2), each of the four affine \(C_3\) disks maps to a disk centered at

\[
P=(1,R_0),\qquad R_0=sr_0\in\{\pm1\}
\]

on \(D_+\).  The map is unramified there because \(da/du=2s\) is a
\(3\)-adic unit.  Put \(x=a-1\).  For a rational point \(Q\) in this disk,

\[
[Q-P]=nG+eT,\qquad n\in\mathbf Z,\quad e\in\{0,1\}.
\]

Torsion has zero logarithm, so (20) implies

\[
\int_P^Q\omega_0=n\ell_0(G)\in9\mathbf Z_3.
\tag{21}
\]

On the other hand the exact local primitive is

\[
H_0(x)=\int_0^x\frac{da}{R}=x\cdot U(x),
\qquad U(x)\in\mathbf Z_3[[x]]^\times
\quad(x\in3\mathbf Z_3).
\tag{22}
\]

The higher terms in (22) are strictly more divisible by \(3\) than the
linear term; integration is the only possible source of a factor of \(3\),
and \(n-v_3(n)\ge2\) for \(n\ge2\).  Equations (21)--(22) force

\[
x=a(Q)-1\in9\mathbf Z_3.
\tag{23}
\]

This is a restriction on rational Mordell--Weil classes, not on all
\(\mathbf Q_3\)-points.  It is precisely why it can remove the extra local
zeros in (15).

### 3.4 Strassmann on the refined disks

Now put \(x=9z\).  Integrating (7), dividing by \(27\), and using (12) gives

\[
\frac{1}{27}\int_0^{9z}
(\lambda-a)\frac{da}{R}
\equiv
\begin{cases}
2z&\pmod3,&R_0=1,\\
 z&\pmod3,&R_0=-1.
\end{cases}
\tag{24}
\]

For the terms involving \(\delta=\lambda-1\), normalized primitive degree
\(n\ge2\) has valuation at least

\[
2n-2-v_3(n)\ge1.
\]

For the terms involving \(-x\), degree \(n\ge2\) has valuation at least

\[
2n-3-v_3(n)\ge1.
\]

Thus the right side of (24) is the exact Weierstrass reduction.  It has one
simple zero, \(z=0\), and the known point realizes it.  Every rational point
in each of the four affine disks is therefore its known center.

Equivalently, each extra zero in (15) has

\[
a-1\equiv3\pmod9,
\]

whereas every rational point must satisfy (23).

## 4. The two infinity disks

The even-degree model has two rational points at infinity.  Treat them
separately with

\[
t=\frac1u,\qquad s_\infty=rt^4.
\]

Then

\[
s_\infty^2=4-8t^6+5t^8,\qquad s_\infty(0)=\pm2,
\]

and (8) becomes

\[
\eta=(1-\lambda t^2)\frac{dt}{s_\infty}.
\tag{25}
\]

The coefficient of \(dt\) at \(t=0\) is \(\pm1/2\), a \(3\)-adic unit.
After \(t=3z\) and division by \(3\), the primitive has reduction
\[
2z\quad\text{or}\quad z\pmod3
\]
according to the branch.  All terms of degree \(n\ge2\) have normalized
valuation at least

\[
n-1-v_3(n)\ge1.
\]

Strassmann therefore gives exactly one zero in each infinity disk, namely
the corresponding point at infinity.  No affine coordinate argument is
being used at infinity.

## 5. Rational points and recovery of C041

Sections 2--4 prove (1).  This is enough to recover the **full** old C041,
including the fibers on which (2) is not invertible.

Let \((a,R)\in D_+(\mathbf Q)\) have rational-square affine abscissa.

* If \(a=0\), the equation forces \(R=0\), giving \((0,0)\).
* If \(a=u^2\ne0\), put \(r=R/u\).  Then

  \[
  r^2=4u^8-8u^2+5,
  \]

  so \((u,r)\in C_3(\mathbf Q)\).  Equation (1) gives \(u=\pm1\), hence
  \((a,R)=(1,\pm1)\).
* The projective point at infinity is handled separately.

Therefore

\[
\{P\in D_+(\mathbf Q):a(P)\in\mathbf Q^2\}
=\{\infty,(0,0),(1,1),(1,-1)\},
\]

which is exactly C041.  The existing exact reverse-lift and
exceptional-fibre audit for these four points is unchanged.  In particular,
the new argument does not replace a denominator or base-locus check by a
generic-open-set assertion.

## 6. Exact dependency change from Target A

Once the direct \(C_3\) theorem and the implication in Section 5 are used in
the clean proof, the following are no longer proof dependencies:

* the \(p=23\) Mordell--Weil sieve;
* the \(p=7\) square-abscissa class tables;
* the exact \(42D\) \(p=7\) formal-log computation;
* the \(p=7\) Coleman differential and four-disk bound;
* the index-independent comparison of coefficients modulo \(21\) and
  \(231\).

The following remain:

* the Schaefer--Stoll proof that \(\operatorname{rank}J(\mathbf Q)=1\),
  including torsion and \(D,T\) independence modulo \(2\);
* the rank-one proof for \(E_1\);
* the exact quotient isogeny (3);
* the small finite-group facts
  \(\#J(\mathbf F_3)=22\), \(\#J(\mathbf F_7)=42\), and
  \(\operatorname{ord}(\bar D)=21\), for torsion and the non-torsion/rank
  input, with the \(p=7\) facts also used in the \(3\)-saturation step (19);
* the compact-locus, common-character, and exceptional-fibre certificates
  preceding and following the arithmetic classification.

The full Schaefer--Stoll \(2\)-descent at \(2,5,17\) remains a dependency of
`paper/clean2.tex`.  The Richelot certificate in Section 7 is an independently
replayable alternative, not an ancestor of the clean theorem.

The old C041 scripts remain runnable and provide an independent proof.  The
new script currently imports generic exact Cantor/polynomial helpers from
`product_genus2_p7_formal_log.py` and finite-Jacobian helpers from
`product_genus2_square_sieve.py`.  It does **not** replay or consume the old
\(42D\) result, the \(7\)-adic logarithm, the square-abscissa class table, or
their JSON conclusions; it recomputes only the new \(11D\) calculation and
the two values in (17).  Thus the old claims are removed as logical proof
dependencies, although their modules remain source-level arithmetic
libraries unless those generic helpers are later factored into a neutral
module.

## 7. Richelot isogeny descent

### 7.1 Status and exact certificates

The Target B mathematics succeeds, but the route is not adopted as the
shorter rank proof.  The exact alternative replays are

```text
research/proof_simplification_2/richelot_composition_check.py
research/proof_simplification_2/richelot_isogeny_descent.py
research/proof_simplification_2/richelot_isogeny_descent.json
```

The main certificate imports and requires the exact composition check.  Its
default `PASS` is logically independent of the old full descent.  Replaying
the old descent is available behind `--replay-full-descent` and is labelled
as an optional comparison.

Over \(K=\mathbf Q(i)\), set

\[
\begin{aligned}
q_1&=a,\\
q_2&=2a^2+2ia-1-2i,\\
q_3&=2a^2-2ia-1+2i.
\end{aligned}
\]

Then

\[
q_1q_2q_3=a(4a^4-8a+5),
\]

and, in the stable order \((q_2,q_3,q_1)\), the coefficient determinant
is \(-8i\) in descending-coefficient convention, equivalently \(+8i\) in
Bruin--Doerksen's constant--linear--quadratic convention.  With
\([f,g]=f'g-fg'\), the exact brackets are

\[
\begin{aligned}
[q_2,q_3]&=-4i(2a^2-4a+1),\\
[q_3,q_1]&=2a^2+1-2i,\\
[q_1,q_2]&=-2a^2-1-2i.
\end{aligned}
\tag{26}
\]

Put

\[
h_1=2a^2-4a+1,\quad
h_2=2a^2+1-2i,\quad
h_3=2a^2+1+2i.
\]

The normalized brackets for the stable order are

\[
\left(-\frac{i}{8}h_2,\ \frac{i}{8}h_3,\ -\frac12h_1\right),
\qquad
\prod G_j=-\frac{h_1h_2h_3}{128}.                 \tag{27}
\]

The coefficient étale algebra is
\(\mathbf Q\times\mathbf Q(i)\), whose discriminant has squareclass
\(d=-1\).  The stable-splitting theorem gives
\(d\widetilde Y^2=\prod G_j\), not the untwisted bracket curve.  Hence
\(\widetilde Y^2=h_1h_2h_3/128\), and \(Y=16\widetilde Y\) gives the
rational Richelot neighbour

\[
\widehat D:\quad
Y^2=2(2a^2-4a+1)(4a^4+4a^2+5).
\tag{28}
\]

The sign in (28) is proof-critical.  The negative model is the untwisted
bracket curve, not the rational quotient attached to this nonsplit stable
factorization.  The exact certificate checks the twist and the
correspondences below; composition is not inferred from degrees or bracket
recovery alone.

### 7.2 Exact forward and reverse correspondences

Use \(x\) on \(D_+\) and \(t\) on \(\widehat D\), and write
\[
f(x)=x(4x^4-8x+5),\qquad
\widehat f(t)=2h_1(t)h_2(t)h_3(t).
\]
The forward Richelot correspondence on
\(D_+\times\widehat D\) has the following genuinely rational equations:

\[
\begin{aligned}
E(x,t)&=2t^2x-2t^2-2x^2+x=0,\\
yY&=B(x,t)\\
&=-2(x-t)\bigl(4t^2x^2-2t^2+2x^2+4x-5\bigr).
\end{aligned}
\tag{29}
\]

Over \(\mathbf Q(i)\), the standard split ordinate is
\[
B_K=-2q_2(x)h_2(t)(x-t),\qquad
B_K-B=-4i(x-t)E.
\]
It therefore induces exactly (29) on \(E=0\), rather than merely a
Galois-conjugate correspondence.  The script proves exact polynomial
divisibility of

\[
f(x)\widehat f(t)-B(x,t)^2
\]

by \(E(x,t)\).  Thus (29) is a correspondence on the product of the two
displayed curves, not a point sample.

For the reverse construction use the stable target order

\[
H=(h_2,h_3,2h_1).
\]

Its normalized brackets are

\[
\left(-\frac{i}{8}q_2,\ \frac{i}{8}q_3,\ -\frac14q_1\right),
\qquad
\prod S_j=-\frac{f}{256}.
\]

Applying the same squareclass \(d=-1\) gives
\(\widetilde Z^2=f/256\); with \(Z=-16\widetilde Z\) the recovered curve is
exactly \(Z^2=f(x)\).  Exact symbolic reduction of the split reverse
equations gives \(E/2\) and the same rational ordinate \(B\) modulo \(E\).
Consequently the reverse correspondence is literally the transpose of
(29), after the displayed ordinate normalization.

If \(Z\subset D_+\times\widehat D\) is the exact correspondence (29), the
forward map on degree-zero divisor classes is the usual pull--push

\[
\phi_Z([A])=
\left[\operatorname{pr}_{2*}
 \bigl(\operatorname{pr}_1^*A\cdot Z\bigr)\right],
\]

and the reverse map is the same construction for
\(Z^{\mathsf t}\).  The reverse identities prove exactly that the
second polynomial correspondence defines \(Z^{\mathsf t}\); they do not
merely show that its source and target curves have the expected equations.

The polarized Richelot correspondence theorem now applies.  The
correspondence and transpose formulation, including the composition
identity, is given in Chow--Jarvis, *A p-adic study of the Richelot
isogeny*, Section 3, referring to Cassels--Flynn, Section 8.4.  The exact
script checks smoothness and both nonzero determinants, so the theorem gives

\[
\widehat\phi\circ\phi=[2],
\qquad
\phi\circ\widehat\phi=[2]
\tag{30}
\]

over \(\mathbf Q(i)\).

The equations \(E,B\) are rational, and both unordered quadratic splittings
are Galois stable.  Bruin--Doerksen, Section 4 and Proposition 4.3, identifies
the required squareclass twist and descends both maps to \(\mathbf Q\).
Faithfulness of base extension for homomorphisms of abelian varieties then
descends (30) to \(\mathbf Q\).  These theorem-backed exact correspondence
identities satisfy the composition obligation without a degree-only
argument or a bounded divisor sample.

References:

* Chow--Jarvis, [*A p-adic study of the Richelot
  isogeny*](https://eprints.whiterose.ac.uk/id/eprint/194471/1/Chow-Jarvis1RJrev1.pdf),
  Section 3; Cassels--Flynn, Section 8.4.
* Bruin--Doerksen, [*The arithmetic of genus two curves with
  \((4,4)\)-split Jacobians*](https://arxiv.org/abs/0902.3480), Section 4
  and Proposition 4.3.

### 7.3 Global groups

The exact discriminant data found for the source and target are

\[
2^{14}5^2 17,\qquad
2^{47}5\,17^2,
\]

and the Richelot determinant contributes only the prime above \(2\).
Thus the exact global local-condition set is

\[
S=\{2,5,17\}.
\tag{33}
\]

At the real place,
\(H^1(\mathbf R,\operatorname{Res}_{\mathbf C/\mathbf R}\mu_2)=0\), so
there is no omitted archimedean condition.  Correcting the target by the
\(-1\) twist does not alter the two-torsion modules: its cocycle is the
hyperelliptic involution, which acts as \([-1]\) on the Jacobian and hence
trivially on two-torsion.  The source descent function and both local
Tate-pairing conventions below are therefore unchanged; the certificate
nevertheless recomputes every survivor mask after the correction.

The associated Gaussian \(S\)-unit squareclass space has \(64\) elements.
The corrected connecting function is

\[
\Lambda(a)=\frac{q_2(a)}2,
\tag{34}
\]

not the unnormalized value \(q_2(a)\).  At infinity the generalized
evaluation is \(8q_2(a)\); its ratio to (34) is the square \(16\).  The
exact rational images are

\[
\delta(D)=[i],\qquad
\delta(T)=[2-i].
\tag{35}
\]

The normalization in (34) and the generalized evaluation at infinity are
proof-critical.  Omitting the factor \(1/2\) changes the squareclass and
invalidates the descent.

### 7.4 Complete local images

The exact local generators use the following rational \(a\)-coordinates:

\[
\begin{array}{c|c}
p& a\text{-coordinates}\\ \hline
2&1,\ -4/3,\ 1/4,\\
5&1,\ 2,\ -5,\\
17&-56,\ -50,\ -49.
\end{array}
\tag{36}
\]

For (34), their values are

\[
\begin{array}{c|ccc}
2&1/2&23/18-(7/3)i&-7/16-(3/4)i\\
5&1/2&7/2+i&49/2-6i\\
17&6271/2-57i&4999/2-51i&4801/2-50i.
\end{array}
\tag{37}
\]

In the current convention the dual-isogeny Selmer intersection is

\[
64\longrightarrow32\longrightarrow16\longrightarrow4,
\tag{38}
\]

with final span \(\langle[i],[2-i]\rangle\), of dimension \(2\).
The isogeny Selmer intersection, computed as the exact local Tate
orthogonal complement using corestricted Gaussian Hilbert symbols, is

\[
64\longrightarrow8\longrightarrow2\longrightarrow2,
\tag{39}
\]

of dimension \(1\), represented by \([1+4i]\) (or its conjugate under the
opposite convention).

The local dimensions behind (38) are \(3,3,1\) at \(2,5,17\).
Their completeness cannot be inferred merely from the displayed points.
The certificate proves completeness as follows:
\(2A=\widehat\phi\phi A\subseteq\widehat\phi\widehat A\), so the natural map
from the exact full group \(A(\mathbf Q_p)/2A(\mathbf Q_p)\)
surjects onto the relevant isogeny quotient.  The exact images of the
complete local Kummer bases are distinct and have the claimed dimensions.
Local Tate duality identifies the other isogeny image with the exact Hilbert
orthogonal.  Both possible Galois-equivariant identifications of the kernel
with its Cartier dual (identity and conjugate/swap) are enumerated, and both
give dimension \(1\) in (39).  In particular, the \(p=17\) condition in
(38) is essential.

### 7.5 Rank consequence and complexity

The isogeny exact sequence and (38)--(39) give

\[
\operatorname{rank}J(\mathbf Q)+2\le2+1=3,
\]

and hence

\[
\operatorname{rank}J(\mathbf Q)\le1.
\tag{40}
\]

The reduction of \(D\) at \(7\) has order \(21\), whereas rational torsion
has order at most \(2\), so \(D\) is non-torsion and equality holds.
Moreover (35) consists of two independent classes in

\[
J(\mathbf Q)/\widehat\phi\widehat J(\mathbf Q).
\]

Because

\[
2J(\mathbf Q)=\widehat\phi\phi J(\mathbf Q)
\subseteq\widehat\phi\widehat J(\mathbf Q),
\]

their independence in the isogeny quotient implies that \(D,T\) are
independent in \(J(\mathbf Q)/2J(\mathbf Q)\).  This is not optional:
Target A uses that independence to prove that the unknown index \(m\) in
(16) is odd.  The finite reductions at \(3\) and \(7\), together with the
visible \(T\), then give

\[
J(\mathbf Q)_{\rm tors}=\langle T\rangle\simeq\mathbf Z/2\mathbf Z.
\]

Thus the Target B certificate could supply all three global inputs to
Target A: rank one, torsion \(\langle T\rangle\), and independence of \(D,T\)
modulo \(2\).  The canonical Target A artifact instead retains the shorter
Schaefer--Stoll certificate.

Computationally this replaces the quartic-etale-algebra enumeration

\[
8192\ \longrightarrow\ 512\ \longrightarrow\ 64\ \longrightarrow\ 8
\ \longrightarrow\ 4
\]

by two \(64\)-class Gaussian calculations, (38) and (39).  This reduces the
ambient class enumeration, but not the complete proof object: the existing
rank script has \(315\) lines and a \(1{,}871\)-byte artifact, whereas the
Richelot route needs a \(572\)-line correspondence certificate, a
\(1{,}586\)-line descent certificate, and a roughly \(20\) KB artifact.
It also requires the twist, transpose, local-completeness, and both
Cartier-pairing arguments recorded above.  It is therefore not a
substantially shorter descent under the task's stated standard.

### 7.6 Certification gates

All seven Target B gates pass:

1. **PASS:** the exact source and target factorizations, determinants, bracket
   identities, rational descent of the isogeny, kernel, dual, and
   \(\widehat\phi\circ\phi=[2]\), with consistent model scalings, are
   certified by the exact forward/reverse correspondence check.
2. **PASS:** the connecting homomorphism is exactly (34), including generalized
   divisor evaluation at infinity, and (35) is computed in the same
   convention.
3. **PASS:** the bad-prime set (33) is exhaustive from the source discriminant, target
   discriminant, Richelot determinant, and kernel; no local condition is
   silently omitted.
4. **PASS:** the local images in (38) are complete quotients, not images of a
   sample of points.
5. **PASS:** the Hilbert-symbol product in (39) is exactly the local Tate/Weil pairing
   for this nonsplit rational kernel, with the required conjugation and
   corestriction conventions; both Galois-equivariant conventions give the
   same dimension.
6. **PASS:** the global survivor spaces and the rank exact-sequence dimension formula
   are checked exactly.
7. **PASS:** the Richelot certificate succeeds without invoking the full old descent;
   replay of the old descent is at most a separately labelled independent
   comparison, not an input to the new `PASS`.

The old full descent remains in `scripts/reproduce.sh` to preserve and replay
the original proof and because it is the rank input retained by the clean
Level-1 proof.  It is not an input to the alternative Richelot certificate
itself.

## 8. Direct \(\operatorname{Jac}(C_3)\) rank approach

No shorter independent rank certificate for
\(\operatorname{Jac}(C_3)(\mathbf Q)\) was found.  The exact decomposition
(3) already reduces the rank calculation to two rank-one factors and gives

\[
\operatorname{rank}\operatorname{Jac}(C_3)(\mathbf Q)
=\operatorname{rank}E_1(\mathbf Q)+\operatorname{rank}J(\mathbf Q)=2.
\]

A direct genus-three \(2\)-descent would have to recover at least those two
factor conditions and was not constructed.  It would not improve the
annihilator calculation: (5) is what proves that the annihilator is
one-dimensional and identifies it with (8).

The Richelot certificate can replace the old full-descent rank and
modulo-\(2\) inputs for the \(J\)-factor, but its complete proof object is
larger, so `paper/clean2.tex` retains the Schaefer--Stoll input.  The
elliptic rank proof, quotient isogeny, and \(p=3\) logarithm/lattice
calculation remain necessary in either version.

## 9. Adversarial logic audit

The following tempting but invalid shortcuts were explicitly excluded.

* **Six known reductions are not six-point completeness.**  The four
  affine Coleman functions each have a second simple \(\mathbf Q_3\)-zero.
* **Vanishing modulo \(3\) is not nonvanishing Chabauty.**  The unique
  annihilator reduces to a multiple of
  \((1-u^2)du/r\), so it vanishes at all four affine centers.
* **The extra zeros are not removed by assertion.**  They are removed only
  after the exact global restriction \(a-1\in9\mathbf Z_3\), obtained from
  (17)--(23).
* **No primitive generator is assumed.**  The unknown relation \(D=mG\) is
  retained.  Modulo-\(2\) independence makes \(m\) odd, and the exact
  \(p=7\) group argument proves \(3\nmid m\).
* **The use of \(p=7\) is not a finite sieve completeness claim.**  It proves
  an integral lattice valuation.  Completeness inside the permitted subdisk
  then follows from exact Strassmann.
* **Every disk is handled.**  The two infinity disks use their own parameter
  and are not inferred from the affine calculation.
* **The map \(C_3\to D_+\) is not used generically at \(u=0\) or infinity.**
  Those two fibers are separated explicitly when recovering C041.
* **Tail estimates are infinite statements.**  The proof uses the elementary
  inequalities in (11), (14), (24), and (25), not a bounded series check.
* **Rank over \(\mathbf Q\) is not replaced by rank over \(\mathbf Q_3\).**
  The rational rank comes from the exact global rank certificates; local
  logarithms are used only after that input.
* **Target B is fail-closed.**  Survivor counts or bracket identities alone
  do not constitute an isogeny descent.  All seven gates now pass, including
  the stable-splitting twist, exact rational forward correspondence, and its
  transpose;
  any mismatch makes the certificate fail rather than fall back to the old
  rank result.
* **The Richelot twist is not optional.**  A preliminary certificate used
  the negative, untwisted bracket curve.  Although its factor set was Galois
  stable, its individual correspondence graph was not.  The corrected
  certificate computes the coefficient étale discriminant squareclass
  \(-1\), uses the positive model (28), and verifies rational equations for
  the correspondence itself.
* **The surrounding factor proof is unchanged.**  The physical sign and
  valuation squareclass remain distinct, the factor \(2\) in
  \(1-UV=2(X+1)LMg^2\) is untouched, C025 is not invoked, and the existing
  exceptional-fibre audit remains a dependency.

## 10. Exact replay

Target A can be replayed with

```bash
.venv/bin/python \
  research/proof_simplification_2/c3_p3_chabauty.py

.venv/bin/python -m pytest -q \
  tests/test_c3_p3_chabauty.py
```

The certificate verifies the checksums of its rank and quotient inputs,
recomputes all six residue classes, performs exact Cantor arithmetic for
\(11D\), proves the coefficient congruences and tail bounds used in every
disk, recomputes (17), and writes its own checksum-protected JSON artifact.
The canonical replay uses the existing Schaefer--Stoll rank certificate.
The independently valid Richelot rank input can be tested without
overwriting that canonical artifact by

```bash
.venv/bin/python \
  research/proof_simplification_2/c3_p3_chabauty.py \
  --rank-source richelot \
  --output /tmp/c3_p3_chabauty_richelot.json
```

Target B can be replayed independently of the old descent with

```bash
.venv/bin/python \
  research/proof_simplification_2/richelot_composition_check.py

.venv/bin/python \
  research/proof_simplification_2/richelot_isogeny_descent.py
```

The second command imports and requires the first certificate, recomputes
the finite rank/torsion data, exhausts both \(64\)-class Selmer spaces, and
writes the canonical checksum-protected JSON artifact.  The optional
independent comparison is

```bash
.venv/bin/python \
  research/proof_simplification_2/richelot_isogeny_descent.py \
  --replay-full-descent \
  --output /tmp/richelot_with_old_comparison.json
```

That flag does not alter the default Target B theorem or its dependency
graph.

The Richelot replay uses SymPy exact polynomial arithmetic and PARI through
cypari2.  The canonical artifact records SymPy and cypari2 versions; the
PARI library version is deliberately not hashed because supported
distribution packages differ, while all accepted outputs are exact.  The
Gaussian number-field setup is accepted only after
`bnfcertify(bnf) == 1`.  Local square tests use exact
`nfislocalpower(..., 2)` calls and local Tate pairings use exact
`nfhilbert` symbols.  No database rank, floating-point approximation, or
heuristic class/unit-group output is treated as a proof.

The old C041 proof should continue to be replayed independently with

```bash
.venv/bin/python \
  research/arithmetic_geometry/product_genus2_two_descent.py
.venv/bin/python \
  research/arithmetic_geometry/product_genus2_square_sieve.py
.venv/bin/python \
  research/arithmetic_geometry/product_genus2_p7_formal_log.py
.venv/bin/python \
  research/compact_signed_square/independent_genus2_square_sieve.py
```

## 11. Success level

Target A is Level 1: direct \(p=3\) Chabauty plus an exact integral
Mordell--Weil lattice refinement proves \(C_3(\mathbf Q)\) and removes the
old \(7/23\) square-abscissa sieve/Coleman block from the clean proof.

Target B is a complete, independently replayable Richelot-isogeny descent,
but it does **not** meet the task's Level-2 requirement of a substantially
shorter rank proof: its two smaller \(64\)-class enumerations require a
larger correspondence, twist, local-completeness, and pairing certificate
than the existing descent.  It is therefore recorded as a valid alternative
and not adopted as a replacement dependency.

The overall result is Level 1.  `paper/clean2.tex` uses the direct \(C_3\)
rational-point theorem and retains the shorter Schaefer--Stoll rank
certificate.  The old \(7/23\) square-abscissa machinery remains intact and
reproducible as an independent proof, but is no longer an ancestor of the
theorem in the new clean dependency graph.
