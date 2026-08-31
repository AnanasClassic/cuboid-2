# Exact 2-descent for the product genus-two curve

Let

$$
D_+:R^2=a(4a^4-8a+5),\qquad J=\operatorname{Jac}(D_+),
$$

and define

$$
D=[(1,1)-\infty],\qquad T=[(0,0)-\infty].
$$

The script `product_genus2_two_descent.py` is a complete
Schaefer--Stoll 2-descent.  It uses PARI through `cypari2`, calls
`bnfcertify`, and does not use Magma or a database rank.

## Etale algebra and global classes

Put $z=2a$.  The quartic factor becomes

$$
z^4-16z+20,
$$

whose defining-polynomial discriminant is $2^{14}17$.  The power order
has index 32, so the field discriminant is $2^4 17=272$.  The field has
class number one, signature $(0,2)$, and roots-of-unity group of order
four.  The descent algebra is

$$
L=\mathbf Q\times K,\qquad K=\mathbf Q[z]/(z^4-16z+20).
$$

The required finite prime set is

$$
S=\{2,5,17\}.
$$

There are four rational S-unit squareclasses and nine field S-unit
squareclasses, hence 8192 raw classes.  Exact norm tests leave 512 classes.

## Complete local images

The following x-coordinates give three independent Kummer values spanning
the complete local image at each prime:

$$
\begin{array}{c|c}
p&x\text{-coordinates}\\ \hline
2&1,-4/3,1/4\\
5&1,2,-5\\
17&-56,-50,-49.
\end{array}
$$

PARI's exact local-power predicate is applied at every prime of $K$ above
the rational prime.  The survivor counts are

$$
512\xrightarrow{\mathbf Q_2}64
\xrightarrow{\mathbf Q_5}8
\xrightarrow{\mathbf Q_{17}}4.
$$

The last arrow is essential.  Stopping at 5 gives a false eight-element
upper bound; 17 is not automatic.

In the script's explicit 13-bit S-unit basis the four final masks are

$$
0,\quad96,\quad276,\quad372.
$$

Exact global square tests identify them as

$$
0,\quad D,\quad D+T,\quad T,
$$

respectively.  In particular, $D$ and $T$ are independent in
$J(\mathbf Q)/2J(\mathbf Q)$.

## Rank consequence

The rational linear factor gives
$\dim_{\mathbf F_2}J(\mathbf Q)[2]=1$.  Therefore

$$
\dim\operatorname{Sel}_2(J/\mathbf Q)=2,
\qquad \operatorname{rank}J(\mathbf Q)\le1.
$$

The finite-group certificate shows that the reduction of $D$ at 7 has
order 21, while rational torsion is bounded by the good reductions at 3 and
7 and has order dividing $\gcd(22,42)=2$.  Thus $D$ is non-torsion and

$$
\operatorname{rank}J(\mathbf Q)=1,\qquad
J(\mathbf Q)_{\rm tors}=\langle T\rangle\simeq\mathbf Z/2\mathbf Z,
\qquad \Sha(J/\mathbf Q)[2]=0.
$$

Independence modulo 2 proves only that the index of $\langle D,T\rangle$
is odd.  The final two-prime sieve is explicitly written so that it does not
assume this index is one.
