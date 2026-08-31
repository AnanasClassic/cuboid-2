# Exact 2-descent rank certificate

Let

$$
C:\quad y^2=f(x)=(x+1)g(x),\qquad
g(x)=x^4+20x^3+6x^2+4x+1,
$$

and let $J=\operatorname{Jac}(C)$.  This note gives an independently
replayable Schaefer--Stoll 2-descent proving

$$
\dim_{\mathbf F_2}\operatorname{Sel}^{(2)}(\mathbf Q,J)=2,
\qquad \operatorname{rank}J(\mathbf Q)\leq 1.
$$

It does not use LMFDB, Magma, or a precomputed Jacobian rank.  The exact
certificate is `two_descent_rank.py` and uses PARI/GP 2.17.2 through
`cypari2`.  PARI's `bnfcertify` is called, so the class and unit group are
certified unconditionally rather than assumed under GRH.

## 1. The etale algebra

Use

$$
K=\mathbf Q(z),\qquad z^4-2z-1=0,
$$

and put

$$
\theta=8z^3-4z^2+2z-17.
$$

Then $g(\theta)=0$, so the descent algebra is

$$
L=\mathbf Q\times K.
$$

The polynomial $z^4-2z-1$ has discriminant $-688=-2^4\cdot43$
and signature $(2,1)$.  The shift $v=z-1$ satisfies

$$
v^4+4v^3+6v^2+2v-2=0,
$$

which is 2-Eisenstein.  Hence 2 is totally ramified in $K$.  The power
order is maximal: if its index were even, the field discriminant would have
2-adic valuation at most 2, contradicting the lower bound $e-1=3$ for the
different exponent of a totally ramified extension of degree 4.  The only
other possible index prime is 43, but its exponent in the polynomial
discriminant is one.

There is also a short elementary class-number check.  The Minkowski bound is

$$
\frac{4!}{4^4}\frac4\pi\sqrt{688}<4.
$$

The unique prime above 2 is principal because
$N_{K/\mathbf Q}(z-1)=-2$.  There is no prime ideal of norm 3 because
$z^4-2z-1$ has no root modulo 3.  Thus the class number is one.  PARI's
unconditional certification gives the fundamental units

$$
\epsilon_1=-z,\qquad \epsilon_2=z^3+z-1,
\qquad N(\epsilon_1)=N(\epsilon_2)=-1.
$$

## 2. The global bounding group

For an odd-degree hyperelliptic curve, the Kummer map is

$$
\delta:J(\mathbf Q)/2J(\mathbf Q)
\hookrightarrow
H=\ker\!\left(N:L^*/L^{*2}\to\mathbf Q^*/\mathbf Q^{*2}\right).
$$

Since

$$
\operatorname{disc}(f)=-2^{24}\cdot43,
$$

Stoll's finite set is $S=\{2,\infty\}$: the exponent at 43 is only one.
Before imposing the norm condition, the (S)-unit squareclasses in
(L=\mathbf Q\times K) have the four independent unit generators

$$
(-1,1),\quad(1,-1),\quad(1,\epsilon_1),\quad(1,\epsilon_2).
$$

Over $\mathbf Q_2$, $f$ has the rational linear factor and one totally
ramified quartic factor.  There are therefore two valuation-parity
coordinates, one in each factor of (L), but square norm forces them to be
equal.  Thus the ideal-valuation target inside (H) has dimension one.
The point $(1,8)$ gives

$$
\gamma=\delta((1,8)-\infty)=(2,1-\theta),
$$

and $v_2(2)=1$, $v_{\mathfrak p}(1-\theta)=5$; hence $\gamma$ spans
that common valuation-parity direction.  Class number one now shows that
every globally admissible class lies in the five-dimensional span of the
four unit squareclasses and $\gamma$.  The script verifies that all 32
products in this span are distinct.

The norm on this five-dimensional span has one-dimensional image (the sign
class), so its kernel has dimension four.  After imposing square norm, the
following four independent elements form a basis:

$$
\begin{aligned}
h_1&=(1,-1),\\
h_2&=(2,1-\theta),\\
h_3&=(-1,-z),\\
h_4&=(-1,z^3+z-1).
\end{aligned}
$$

The script checks directly that the sixteen products are distinct globally.

## 3. Exact local image at 2

Coordinates on $\mathbf Q_2^*/\mathbf Q_2^{*2}$ use the basis
$(-1,2,5)$.  Coordinates on $K_2^*/K_2^{*2}$ use

$$
(z-1,-1,2,z,2-z,2z-1).
$$

PARI's exact `nfislocalpower` predicate verifies that all 64 products of the
second list are distinct.  Since
$\dim_{\mathbf F_2}K_2^*/K_2^{*2}=4+2=6$, this is a basis.

The script also checks this independently by a finite Hensel certificate.
Here $\pi=z-1$ is a uniformizer and $v_\pi(2)=4$.  It exhausts the 256
unit residues

$$
1+\sum_{i=1}^8 b_i\pi^i\pmod {\pi^9},\qquad b_i\in\{0,1\}.
$$

If $u\equiv y^2\pmod {\pi^9}$, then
$v_\pi(u-y^2)>2v_\pi(2y)=8$, so the strong Hensel lemma lifts $y$ to an
exact square root.  Conversely, every square has such a residue.  This finite
test reproduces both local matrices without calling `nfislocalpower`.

In the resulting nine coordinates, the rows for $h_1,\ldots,h_4$ are

$$
M_G=
\begin{pmatrix}
0&0&0&0&1&0&0&0&0\\
0&1&0&1&0&0&1&0&0\\
1&0&0&0&1&0&1&0&0\\
1&0&0&0&0&1&1&0&0
\end{pmatrix}.
$$

The values

$$
f(1)=64,\quad f(-7)=2^6\cdot393,\quad
f(11)=2^6\cdot7881
$$

are squares in $\mathbf Q_2$, because both odd units are 1 modulo 8.
Thus these three x-coordinates give $\mathbf Q_2$-points.  Their Kummer
rows are

$$
M_2=
\begin{pmatrix}
0&1&0&1&0&0&1&0&0\\
0&1&1&1&1&0&0&1&0\\
1&0&1&0&0&1&0&1&0
\end{pmatrix},
$$

which has rank three.  The standard local dimension formula gives

$$
\dim J(\mathbf Q_2)/2J(\mathbf Q_2)
=(m_2-1)+[\mathbf Q_2:\mathbf Q_2]g=(2-1)+2=3,
$$

so these rows are the complete local image.  Intersecting the row space of
$M_G$ with the row space of $M_2$ leaves exactly the masks

$$
\{0,2,9,11\}=\langle 2,9\rangle,
$$

a two-dimensional subspace.

## 4. Infinity and 43

The three real roots occur in the order

$$
\theta_{\rm low}<-1<\theta_{\rm high}.
$$

Writing negative signs as 1 in the order
$(-1,\theta_{\rm low},\theta_{\rm high})$, the real Kummer image is

$$
\{(0,0,0),(1,0,1)\}.
$$

The four global sign rows are

$$
(0,1,1),\ (0,0,0),\ (1,0,1),\ (1,1,0).
$$

The real condition leaves masks
$\{0,2,4,6,9,11,13,15\}$, so it does not remove either of the two
classes that survived at 2.

Modulo 43,

$$
f(x)=(x-3)^2(x+1)(x+9)(x+17).
$$

Because $v_{43}(\operatorname{disc}f)=1$, Stoll's Proposition 4.6 says
that the Kummer image is exactly the kernel of ideal valuation at 43.  Every
global candidate above has zero valuation there, so the 43-adic condition is
automatic.  The same statement at all other odd primes follows from good
reduction.

## 5. Exact dimension and rank

Both surviving generators are global Kummer images.  Mask 2 is
$\delta((1,8)-\infty)$.  Mask 9 is the rational 2-torsion class supported
on the factor $x+1$; the square relation needed to identify it is

$$
\frac{\theta+1}{\epsilon_2}=(-2z^3+z^2+3)^2.
$$

They are independent in the certified global basis.  Therefore the upper
bound of four elements is attained:

$$
\operatorname{Sel}^{(2)}(\mathbf Q,J)
\cong(\mathbf Z/2\mathbf Z)^2.
$$

The rational factor $x+1$ gives
$\dim_{\mathbf F_2}J(\mathbf Q)[2]=1$, hence

$$
\operatorname{rank}J(\mathbf Q)
\le 2-1=1.
$$

The divisor class $[(0,1)-\infty]$ is not torsion: reduction at the two
good primes 3 and 5 bounds the rational torsion order by
$\gcd(22,28)=2$, while the exact Mumford calculation shows that neither
the class nor its double is zero.  Hence the rank is exactly one.  The exact
sequence defining the 2-Selmer group then also gives

$$
 \operatorname{rank}J(\mathbf Q)=1,
 \qquad \Sha(J/\mathbf Q)[2]=0.
$$

Run the certificate with

```bash
.venv/bin/python research/linear_factor_completion/two_descent_rank.py
```

The final line must be `CERT status = PASS`.
