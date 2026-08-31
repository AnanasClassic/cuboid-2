# Second endpoint layer: the two-inert-prime-power family is closed

Let

$$
p=L^m,\qquad q=R^n,
$$

where $L,R$ are distinct odd primes, $m,n\geq1$, and
$(2/L)=(2/R)=-1$.  The earlier endpoint calculation restricted a
nonuniform quadratic factor to $u,v\in\{0,3,4\}$, but used only the lowest
coefficient modulo $L$ and $R$.  That was not enough: its congruence
systems have infinitely many formal survivors.

The next coefficient is always two powers higher.  If the cleared projection
polynomial vanishes, reducing modulo that next layer gives the stronger
prime-power divisibilities below.  The reverse orientation swaps $p,q$.

| pair | sign $\sigma$ | exact necessary divisibilities |
|---|---:|---|
| $(u,v)=(3,4)$ | $\pm1$ | $p\mid q^2-\sigma,\ q^2\mid p^2-\sigma$ |
| $(u,v)=(0,3)$ | $\pm1$ | $p^2\mid q^6-\sigma,\ q\mid p^6-\sigma$ |
| $(u,v)=(0,4)$ | $\pm1$ | $p^2\mid q^8-\sigma,\ q^2\mid p^8-\sigma$ |

The asymmetry comes from the endpoint multiplicity.  For example, in the
$e=6$ orientation the $P$-endpoint contains $q^6-\sigma$ once, while
the $Q$-endpoint contains $(p^6-\sigma)^2$.  Divisibility of the endpoint
by $p^2$ or $q^2$ therefore gives $p^2\mid q^6-\sigma$ and
$q\mid p^6-\sigma$, respectively.  After those target factors are removed,
the exact cofactors are signed pure powers of the opposite variable, so
$\gcd(p,q)=1$ loses no valuation.  The script checks these factorizations,
multiplicities, cofactors, and exponent gaps.

## The $e=2$ branches

For $\sigma=1$, suppose

$$
p\mid q^2-1,\qquad q^2\mid p^2-1.
$$

The second divisibility gives $p>q$.  Since $p$ is an odd prime power and
$\gcd(q-1,q+1)=2$, all of $p$ divides one of $q-1,q+1$.  But then
$p\leq q+1$, contradicting $p>q$ for two odd integers.

For $\sigma=-1$, suppose

$$
p\mid q^2+1,\qquad q^2\mid p^2+1.
$$

Again $p>q$.  Put $c=(q^2+1)/p$, so $1\leq c\leq q-1$.  Modulo $q^2$,
$pc\equiv1$ and $p^2\equiv-1$, hence $q^2\mid p+c$.  If $c=1$, then
$p+c=q^2+2$, strictly between $q^2$ and $2q^2$.  If $c\geq2$, then

$$
0<p+c=\frac{q^2+1}{c}+c
\leq\frac{q^2+1}{2}+q-1<q^2
$$

because $q\geq3$.  Both cases contradict $q^2\mid p+c$.  The reverse
orientation is identical.

## Full-projection positivity for negative $e=6$ and both $e=8$ signs

After removing its boundary monomial, every relevant branch polynomial has
only even powers of $P,Q$.  Put

$$
P^2=U+9,\qquad Q^2=V+9.
$$

For negative $e=6$, the full 71-term projection becomes a polynomial in
$U,V$ with 269 nonzero coefficients, all strictly positive.  For each sign
of $e=8$, it has 441 strictly positive coefficients.  Since odd prime
powers satisfy $P,Q\geq3$, these branch polynomials cannot vanish.  This is
additional information from the full projection, not another endpoint
congruence.

## The remaining positive $e=6$ branch

Use the orientation

$$
p^2\mid q^6-1,\qquad q\mid p^6-1,
$$

and write $q=R^n$.  If $R\ne3$, the four cyclotomic factors of
$p^6-1$ are pairwise coprime at $R$.  Thus all $R$-adic valuation lies
in one factor and

$$
q\leq p^2+p+1.
$$

If $R=3$, LTE gives

$$
v_3(p^6-1)=v_3(p^2-1)+1,
$$

so $q\leq3(p^2-1)$.

Let $F(p,q)$ be the normalized positive-$e=6$ projection branch.  For
either bound $B(p)$, make the exact change

$$
p=U+3,\qquad q=\frac{3+B(p)W}{1+W}.
$$

The cleared polynomial

$$
(1+W)^{24}F\!\left(U+3,\frac{3+B(U+3)W}{1+W}\right)
$$

has 1619 nonzero coefficients, all strictly positive, for both
$B=p^2+p+1$ and $B=3(p^2-1)$.  This covers $3\leq q<B(p)$ by
$W=(q-3)/(B(p)-q)\geq0$.  The endpoint $q=B(p)$ is the coefficient of
$W^{24}$, itself a polynomial in $U$ with strictly positive
coefficients.  Hence the branch cannot vanish.  Swapping $p,q$ closes the
other orientation.

Therefore all nonuniform pairs are excluded.  Combined with the existing
uniform-pair theorem, this proves:

> **Two-inert-prime-power theorem.** If $p$ and $q$ are powers of
> distinct odd primes at which $2$ is a quadratic nonresidue, then the
> $2+3$ factorization cannot occur.

This is not a proof for general $p,q$: when either integer has several
prime divisors, one global quadratic factor may choose different Newton pairs
at different primes.  The exact certificate is
research/global_descent/second_endpoint_layer.py.  Its JSON records
coefficient counts, extrema, and SHA-256 digests of every
positive-coefficient table.
