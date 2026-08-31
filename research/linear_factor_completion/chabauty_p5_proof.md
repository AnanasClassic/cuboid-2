# Exact (p=5) Chabauty completion

Let

$$
C:\quad w^2=f(t)=t^5+21t^4+26t^3+10t^2+5t+1
               =(t+1)(t^4+20t^3+6t^2+4t+1)
$$

and $J=\operatorname{Jac}(C)$.  This note records the mathematical proof
implemented by `sage_chabauty_p5.py`; the independent rank certificate is
`two_descent_rank.py`.

## 1. Rank and the chosen divisor

The exact Schaefer--Stoll descent proves

$$
\dim_{\mathbf F_2}\operatorname{Sel}^{(2)}(J/\mathbf Q)=2,
\qquad \operatorname{rank}J(\mathbf Q)\leq1.
$$

Exact point counts give

$$
\#J(\mathbf F_3)=22,\qquad \#J(\mathbf F_5)=28.
$$

Hence $J(\mathbf Q)_{\rm tors}$ has order dividing $2$.  Exact Jacobian
arithmetic checks that

$$
D=[(0,1)-\infty]
$$

is neither zero nor killed by $2$, so $D$ has infinite order.  Therefore
$\operatorname{rank}J(\mathbf Q)=1$, and $D$ spans
$J(\mathbf Q)\otimes\mathbf Q_5$.  No assertion that $D$ is a saturated
Mordell--Weil generator is needed.

## 2. The six residue discs

The discriminant is $-2^{24}\cdot43$, so $C$ has good reduction at $5$.
Exact enumeration gives

$$
C(\mathbf F_5)=
\{\infty,(-1,0),(0,\pm1),(1,\pm2)\},
$$

where the last signs are modulo $5$.  The six rational points

$$
\infty,\quad(-1,0),\quad(0,\pm1),\quad(1,\pm8)
$$

reduce bijectively to this set.  Thus it remains only to prove that no one of
these six residue discs contains a second rational point.

## 3. Coleman annihilator

Sage 10.9 computes the four Coleman integrals

$$
\left(\int_D\frac{t^i\,dt}{2w}\right)_{i=0}^3.
$$

Write the first two as $I_0,I_1$.  Their common $5$-adic valuation is
one.  After dividing by $5$, set

$$
c_0=I_1/5,\qquad c_1=-I_0/5,
\qquad
\eta=(c_0+c_1t)\frac{dt}{2w}.
$$

Then $\int_D\eta=0$.  Since $D$ spans
$J(\mathbf Q)\otimes\mathbf Q_5$, $\eta$ annihilates all of
$J(\mathbf Q)$.  The exact (5)-adic output gives

$$
\bar\eta=(1+t)\frac{dt}{2w},
\qquad v_5(c_0-c_1)=1.
$$

The reduction of $\eta$ is nonzero at the four points above $t=0,1$.
At infinity, $dt/(2w)$ has order two and $t\,dt/(2w)$ is a unit, so
$\bar\eta$ is also nonzero there.  The usual one-disc Coleman estimate (or
the identical local power-series argument) gives at most one rational zero
in each of these five discs.

## 4. The exceptional Weierstrass disc

The reduction of $\eta$ vanishes at $P=(-1,0)$, so this disc requires a
separate calculation.  Use $u=w$ and $v=t+1$.  The curve equation becomes

$$
u^2=-16v+48v^2-48v^3+16v^4+v^5.
$$

Since $-16$ is a $5$-adic unit, the integral implicit-function theorem
gives a unique even series

$$
v=v(u^2)\in u^2\mathbf Z_5[[u^2]].
$$

Differentiating $u^2=f(t)$ gives $dt/(2u)=du/f'(t)$, and hence

$$
\eta=h(u)\,du,
\quad
h(u)=\frac{c_0+c_1(-1+v(u^2))}{f'(-1+v(u^2))}
     =\alpha+b_2u^2+b_4u^4+\cdots
$$

with every $b_{2k}\in\mathbf Z_5$ and

$$
\alpha=\frac{c_0-c_1}{-16},\qquad v_5(\alpha)=1.
$$

The first terms, checked symbolically by the script, are

$$
\int_0^u h(s)\,ds
=\alpha u+\frac{6(c_0-c_1)+c_1}{3\cdot256}u^3+O(u^5).
$$

Every point in the residue disc has $u=5z$, $z\in\mathbf Z_5$.  For an
odd term of degree $n\geq3$, division by $25$ after substituting $u=5z$
leaves coefficient valuation at least

$$
n-2-v_5(n)\geq1.
$$

(If $v_5(n)=e>0$, then $n\geq5^e\geq e+3$; the case $e=0$ is
immediate.)  Therefore the local Coleman primitive $G$, normalized by
$G(P)=0$, satisfies

$$
\frac{G(5z)}{25}
=z\left(\frac{\alpha}{5}+5z^2B(z^2)\right),
\qquad B\in\mathbf Z_5[[z^2]].
$$

The expression in parentheses is a unit.  By Strassmann's theorem (indeed,
directly from this factorization), $G(5z)=0$ if and only if $z=0$.
Thus $P=(-1,0)$ is the only rational point in its residue disc.

## 5. Rational points and the (1+4) claim

Combining the six discs gives

$$
C(\mathbf Q)=\{\infty,(-1,0),(0,\pm1),(1,\pm8)\}.
$$

The exact quotient audit maps any rational root of $P_s$, for
$s\in\mathbf Q_{>0}$ and $s\neq1$, to a point of $C(\mathbf Q)$.  For
the four possible $t$-coordinates, the quotient function gives

$$
t=\infty:\ U=2\Rightarrow s=1,
\qquad
t=-1:\ U=-2\Rightarrow s=-1,
$$

while $t=0,1$ are genuine poles and give no finite nonzero $s$.  The only
other denominator $t^2+6t+1$ has no rational zero.  Consequently no
admissible positive rational $s\neq1$ yields a rational root of $P_s$.
This proves claim `C004` once the three exact scripts in this directory have
all returned `PASS`.
