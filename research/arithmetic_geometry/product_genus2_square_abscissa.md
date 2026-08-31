# Square abscissas on the product genus-two curve

Let

$$
C:R^2=4a^5-8a^2+5a,\qquad
D=[(1,1)-\infty],\qquad T=[(0,0)-\infty].
$$

The exact certificates in this directory prove

$$
\boxed{
  \{P\in C(\mathbf Q):a(P)\in\mathbf Q^{\,2}\}
  =\{\infty,(0,0),(1,1),(1,-1)\}.}
$$

Here infinity is included as the projective point and is not assigned an
affine square coordinate.

## 1. Rank

The Schaefer--Stoll certificate `product_genus2_two_descent.py` uses

$$
L=\mathbf Q\times\mathbf Q[z]/(z^4-16z+20),qquad S=\{2,5,17\}.
$$

It exhausts 8192 S-unit classes, retains 512 square-norm classes, and then
intersects the complete local images:

$$
512\longrightarrow64\longrightarrow8\longrightarrow4.
$$

The last arrow is the explicit local condition at 17.  The four classes are
$0,D,T,D+T$.  Consequently

$$
\dim\operatorname{Sel}_2(J/\mathbf Q)=2,qquad
\operatorname{rank}J(\mathbf Q)=1,qquad
J(\mathbf Q)_{\rm tors}=\langle T\rangle.
$$

In particular $D,T$ are independent modulo 2.  This says that the index of
$\langle D,T\rangle$ is odd; it does **not** silently assert that the index
is one.

## 2. Index-independent Mordell--Weil sieve

Exact Cantor arithmetic gives

$$
\begin{array}{c|c|c}
p&\#J(\mathbf F_p)&\operatorname{ord}(\bar D)\\ \hline
7&42&21\\
23&462&231.
\end{array}
$$

The independent compact certificate recomputes both Jacobian orders from
exhaustive counts of $C(\mathbf F_p)$ and $C(\mathbf F_{p^2})$.

We first remove a possible hidden odd index.  Write

$$
J(\mathbf Q)=\mathbf ZG\oplus\langle T\rangle,qquad D=mG+\delta T.
$$

Modulo-2 independence makes $m$ odd.  Replacing $G$ by $G+\delta T$
then gives $D=mG$.  At either prime put
$N=\operatorname{ord}(\bar D)$ and
$r=\operatorname{ord}(\bar G)$.  We know $r\mid2N$ and

$$
\frac r{\gcd(r,m)}=N.
$$

Because $m$ is odd, $r=2N$ would force the even number
$\gcd(r,m)=2$, impossible.  Hence $r=N$ and $m$ is invertible modulo
$N$.  Thus any global class $nG+eT$ has local coordinates

$$
c_p=nm^{-1}\pmod N,\qquad e\in\{0,1\}.
$$

Since $21\mid231$, its coordinates at 7 and 23 agree modulo 21.  This is
why no generator or odd-saturation assumption is needed.

The complete lists of finite classes represented by points with square
abscissa are

$$
\begin{aligned}
p=7:\quad &(c,e)=(0,0),(\pm1,0),(\pm5,0),(0,1),\\
p=23,\ e=0:\quad
&c=0,\pm1,\pm9,\pm44,\pm51,\pm67,\pm108,
\end{aligned}
$$

and at 23 the only class with $e=1$ is $(0,1)$.  Reducing the second
line modulo 21 gives

$$
c=0,\pm1,\pm2,\pm3,\pm4,\pm9,
$$

which excludes $\pm5$.  Therefore every rational square-abscissa point
reduces at 7 to one of the four disks

$$
\infty,\quad(0,0),\quad(1,1),\quad(1,-1). \tag{1}
$$

## 3. Exact formal logarithm at 7

The formal-log certificate computes $42D$ over $\mathbf Q$ by exact
Cantor arithmetic.  Write its Mumford pair as $(u,v_R)$, using the original
$R$-coordinate, and put $a=4+t$.  The exact leading data are

$$
\begin{array}{c|ccccc}
&[t]u&[1]u&\operatorname{disc}(u)&[a]v_R&v_R(4)\\ \hline
v_7&1&2&2&-1&0\\
\text{unit mod }7&5&3&6&1&6.
\end{array}
$$

Thus, after setting $t=7\tau$, the two branches reduce over
$\mathbf F_{49}$ to

$$
\tau^2+5\tau+3=0,qquad R=\tau+6. \tag{2}
$$

The discriminant in (2) is 6, a nonsquare in $\mathbf F_7$, so these are
the two conjugate branches above $a=4$.  They have opposite R-coordinates
and their sum is the identity in the reduced Jacobian.  This explicitly
explains why $42D$ is in the formal group; no numerical closeness is being
used.

Use the holomorphic basis

$$
\omega_0=da/R,qquad\omega_1=a\,da/R.
$$

After dividing the formal logarithm by 7, the leading coefficient of the
first coordinate is the trace

$$
\sum_i\frac{\tau_i}{\tau_i+6}=2\ne0\pmod7.
$$

For the second coordinate, $a=4+7\tau$, so its leading coefficient is four
times the first.  All higher integral terms vanish modulo 7 after division:
their valuation is at least
$n-v_7(n)-1\ge1$ for $n\ge2$.  Hence

$$
\log(42D)/7\equiv(1,4)\pmod7.
$$

Since $\log(42D)=42\log(D)$ and $42/7=6$ is a 7-adic unit, the same
projective direction holds for $\log(D)$.  Rank one means that the exact
annihilating differential has reduction

$$
\bar\eta=(4-a)\omega_0=(4-a)\frac{da}{R};
$$

equivalently its coefficient vector is $(4,-1)$ against
$(\omega_0,\omega_1)$.

This reduction is nonzero in every disk in (1): at infinity its leading
coefficient is $-1$, at the Weierstrass disk $(0,0)$ it is 4, and at
the two disks above $a=1$ it is 3.  Since $7>2g=4$, the standard
Coleman disk bound gives at most one rational point in each disk.  Each disk
already contains the displayed rational point, proving the boxed theorem.

## Reproduction

Run

```bash
python research/arithmetic_geometry/product_genus2_two_descent.py
python research/arithmetic_geometry/product_genus2_square_sieve.py
python research/arithmetic_geometry/product_genus2_p7_formal_log.py
python research/compact_signed_square/independent_genus2_square_sieve.py
```

The first script requires the optional `cypari2` test dependency.  All four
write checksum-protected JSON artifacts and the test suite replays them.
