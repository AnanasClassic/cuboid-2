# Elementary 2-isogeny descent for the candidate curve

This note proves, without database data or a black-box Mordell--Weil
calculation, that

$$
E_1:\quad y^2=x^3-5x+4
$$

has rank exactly one and torsion subgroup $\mathbf Z/2\mathbf Z$.  It does not
identify the reciprocal cuboid quotient with $E_1$; that remains a separate
birational-identification problem.

## 1. The 2-isogenous pair and descent maps

Translate $X=x-1$, $Y=y$.  Then

$$
E:\quad Y^2=X(X^2+3X-2).
$$

The point $T=(0,0)$ has order two.  The associated 2-isogenous curve is

$$
E':\quad V^2=U(U^2-6U+17),
$$

with $T'=(0,0)$.  On the complements of their kernels, the isogeny and its
dual are

$$
\phi(X,Y)=
\left(\frac{Y^2}{X^2},\frac{Y(-2-X^2)}{X^2}\right),
$$

$$
\widehat\phi(U,V)=
\left(\frac{V^2}{4U^2},\frac{V(17-U^2)}{8U^2}\right).
$$

They extend by $\phi(O)=\phi(T)=O$ and
$\widehat\phi(O)=\widehat\phi(T')=O$.  Direct substitution verifies the curve
equations and

$$
\widehat\phi\phi=[2]_E,
\qquad
\phi\widehat\phi=[2]_{E'}.
$$

These identities are checked symbolically in
`candidate_544c_rank_descent.py` as well as in the independent candidate
isogeny certificate.

We use the standard descent maps

$$
\begin{aligned}
\alpha_E &:E(\mathbf Q)\longrightarrow \mathbf Q^*/\mathbf Q^{*2},\\
\alpha_E(O)&=1,\qquad \alpha_E(T)=-2,\qquad
\alpha_E(X,Y)=X,\\[2mm]
\alpha_{E'} &:E'(\mathbf Q)\longrightarrow \mathbf Q^*/\mathbf Q^{*2},\\
\alpha_{E'}(O)&=1,\qquad \alpha_{E'}(T')=17,\qquad
\alpha_{E'}(U,V)=U.
\end{aligned}
$$

All values here and below are squareclasses.

### Lemma 1: descent-map kernels

The maps $\alpha_E$ and $\alpha_{E'}$ are homomorphisms, and

$$
\ker\alpha_E=\widehat\phi(E'(\mathbf Q)),
\qquad
\ker\alpha_{E'}=\phi(E(\mathbf Q)).
$$

**Proof.**  First consider the general curve

$$
C_{a,b}: y^2=x(x^2+ax+b).
$$

If a line $y=mx+n$ meets it at three points with nonzero abscissas
$x_1,x_2,x_3$, substitution gives a monic cubic with constant term $-n^2$.
Thus $x_1x_2x_3=n^2$.  Since three collinear points sum to zero, the
abscissa squareclass is multiplicative.  If the line passes through
$(0,0)$, the two nonzero abscissas instead have product $b$; this is exactly
why the value at $(0,0)$ is defined to be $b$.  The identity and tangent
cases follow by the same formulas.  Hence the descent map is a homomorphism.

For our $E$, the first coordinate of $\widehat\phi(U,V)$ is
$(V/(2U))^2$, so the image of $\widehat\phi$ lies in $\ker\alpha_E$.
Conversely, suppose $P=(X,Y)$ has trivial squareclass and $X=w^2\ne0$.
Put $h=Y/w$.  Then

$$
h^2=w^4+3w^2-2.
$$

Set

$$
U=3+2w^2-2h,\qquad V=2Uw.
$$

The product

$$
(3+2w^2-2h)(3+2w^2+2h)=17
$$

shows $U\ne0$.  Exact substitution gives $(U,V)\in E'(\mathbf Q)$ and
$\widehat\phi(U,V)=(X,Y)$.  The point $T$ is not in the kernel because
$-2$ is not a square.  Thus $\ker\alpha_E=\widehat\phi(E'(\mathbf Q))$.
Applying the identical calculation to $E'$ and using the rational scaling
between its second 2-isogenous curve and $E$ proves the other kernel
identity.  Explicitly, the second curve attached to $E'$ is

$$
W^2=Z(Z^2+12Z-32),
$$

and $(Z,W)=(4X,8Y)$ identifies it with $E$.  Under this identification the
dual map back to $E'$ is exactly the displayed map $\phi$.  Therefore the
same square-abscissa construction proves
$\ker\alpha_{E'}=\phi(E(\mathbf Q))$.  ∎

Consequently,

$$
\begin{aligned}
[E(\mathbf Q):\widehat\phi E'(\mathbf Q)]
 &=|\alpha_E(E(\mathbf Q))|,\\
[E'(\mathbf Q):\phi E(\mathbf Q)]
 &=|\alpha_{E'}(E'(\mathbf Q))|.
\end{aligned}
$$

## 2. Valuation restriction

### Lemma 2

On $C_{a,b}:y^2=x(x^2+ax+b)$, every prime occurring to odd exponent in the
squareclass of a nonzero $x\in\mathbf Q$ divides $b$.

**Proof.**  Let $\ell\nmid b$ and $n=\operatorname{ord}_\ell(x)$.
If $n>0$, then $x^2+ax+b$ is an $\ell$-adic unit, so
$\operatorname{ord}_\ell(y^2)=n$ and $n$ is even.  If $n<0$, the term $x^2$
has strictly smaller valuation than $ax$ and $b$.  Hence

$$
\operatorname{ord}_\ell(x^2+ax+b)=2n,
$$

and $\operatorname{ord}_\ell(y^2)=3n$, again forcing $n$ even.  ∎

Equivalently, after writing the squareclass as a squarefree integer $d$, one
has $d\mid b$ up to sign.  The familiar homogeneous space follows directly:
if $x=d(r/s)^2$ in lowest terms, then

$$
N^2=d r^4+a r^2s^2+(b/d)s^4.
$$

No assertion of soluble homogeneous spaces is being inferred from a
resultant: the rational point itself supplies this equation.

## 3. The two exact descent images

For $E$, Lemma 2 leaves only

$$
\alpha_E(E(\mathbf Q))\subseteq\{1,-1,2,-2\}.
$$

Every class occurs:

| point on $E$ | descent class |
|---|---:|
| $O$ | $1$ |
| $(0,0)$ | $-2$ |
| $P=(-1,2)$ | $-1$ |
| $P+T=(2,4)$ | $2$ |

The displayed coordinates satisfy the equation exactly.  Therefore

$$
|\alpha_E(E(\mathbf Q))|=4.
$$

For $E'$, observe that

$$
V^2=U\bigl((U-3)^2+8\bigr).
$$

The second factor is strictly positive over $\mathbf R$.  Thus every
non-torsion affine rational point has $U>0$.  Lemma 2 says that its
squareclass is supported only at 17.  Hence

$$
\alpha_{E'}(E'(\mathbf Q))\subseteq\{1,17\}.
$$

Both classes occur at $O$ and $T'=(0,0)$, respectively, so

$$
|\alpha_{E'}(E'(\mathbf Q))|=2.
$$

## 4. The exact index formula

The rational 2-torsion of $E$ consists exactly of $O,T$.  Indeed, the other
two roots would solve $X^2+3X-2=0$, whose discriminant is 17.  Therefore
$|E(\mathbf Q)[2]|=2$.

Let

$$
A=[E(\mathbf Q):\widehat\phi E'(\mathbf Q)],\qquad
B=[E'(\mathbf Q):\phi E(\mathbf Q)].
$$

The map induced by $\widehat\phi$,

$$
E'(\mathbf Q)/\phi E(\mathbf Q)
\longrightarrow
\widehat\phi E'(\mathbf Q)/2E(\mathbf Q),
$$

is surjective.  Its kernel is generated by the class of $T'$.  This class is
nontrivial: if $T'=\phi(R)$, then
$2R=\widehat\phi(T')=O$, while both rational points in $E[2]$ map to $O$.
Thus the kernel has order two, and

$$
[\widehat\phi E'(\mathbf Q):2E(\mathbf Q)]=B/2.
$$

It follows that

$$
[E(\mathbf Q):2E(\mathbf Q)]=AB/2.
$$

If $r$ is the Mordell--Weil rank, the structure theorem gives

$$
[E(\mathbf Q):2E(\mathbf Q)]
=2^r|E(\mathbf Q)[2]|=2^{r+1}.
$$

Therefore

$$
2^r=\frac{AB}{4}
=\frac{4\cdot2}{4}=2,
$$

and hence

$$
\boxed{\operatorname{rank}E_1(\mathbf Q)=1}.
$$

## 5. Non-torsion point and the complete torsion subgroup

In the original short coordinates, $P=(0,2)$.  Its tangent has slope
$-5/4$, and the duplication formula gives

$$
2P=\left(\frac{25}{16},-\frac{3}{64}\right).
$$

The integral short Weierstrass equation is nonsingular because

$$
4(-5)^3+27(4)^2=-68\ne0.
$$

If $P$ were torsion, the nonzero point $2P$ would also be torsion.  Its
nonintegral coordinates contradict the Nagell--Lutz theorem.  Thus $P$ is
non-torsion, independently confirming the lower bound implicit in the
descent.

Nagell--Lutz also determines the full torsion subgroup.  A torsion point has
integral coordinates and either $y=0$ or $y^2$ divides 68.  The nonzero
square divisors of 68 are 1 and 4.

- For $y=0$, the only rational root of
  $(x-1)(x^2+x-4)$ is $x=1$.
- For $y^2=1$, the polynomial $x^3-5x+3$ has no integer root.
- For $y^2=4$, the equation is $x(x^2-5)=0$, giving only $x=0$ in
  integers; these are $P$ and $-P$, already proved non-torsion.

Therefore

$$
\boxed{E_1(\mathbf Q)_{\mathrm{tors}}=\{O,(1,0)\}
\cong\mathbf Z/2\mathbf Z}.
$$

The proof establishes rank and torsion for the candidate model itself.  It
does not transport them to the cuboid quotient without the still-missing
exact identification map.
