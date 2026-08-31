# Red-team and two-prime extension

## Local valuations of both coefficients

Let the integral quadratic factor be

$$
X^2+A X+B=(X-\alpha)(X-\beta).
$$

At a prime $\ell\mid pq$, divide valuations by
$k=v_\ell(pq)$.  The root valuations are
$0,0,2,4,4$.  Hence the possible pairs and coefficient valuations are:

| root pair | $v(B)/(2k)$ | $v(A)/k$ |
|---|---:|---:|
| $(0,0)$ | 0 | at least 0 |
| $(0,2)$ | 1 | exactly 0 |
| $(0,4)$ | 2 | exactly 0 |
| $(2,4)$ | 3 | exactly 2 |
| $(4,4)$ | 4 | at least 4 |

Exactness in unequal-slope rows follows from the ultrametric inequality.
There is no upper bound in either equal-slope row: the two roots can cancel
to arbitrary order.  `new_local_A_B_audit.py` records the table and explicit
cancellation families.

The same global quadratic factor need not select a uniform pair type.  The
exact witness

$$
(X-1)(X-25)(X-9)(X-3^4 5^4)^2
$$

has root-valuation multiset $\{0,0,2,4,4\}$ at both 3 and 5, while its
quadratic factor $(X-1)(X-25)$ selects $(0,0)$ at 3 and $(0,2)$ at 5.
Thus Newton data, including both $A$ and $B$, cannot force uniformity.
This is a no-go result for that local argument only; the witness is not a
Sharipov polynomial.

## A genuine two-prime family

Let $r\ne3$ be prime with $r\equiv3,5\pmod8$, and let $n\ge1$.  Then

$$
P_{(3/r^n)^2}(x)
$$

has no rational quadratic divisor.  Reciprocity gives the same result for
$P_{(r^n/3)^2}$.

At both primes, the slope-zero residual quadratic is irreducible, reducing
the normalized local indices to $\{0,3,4\}$.  Equal index pairs are already
excluded by the ten exact uniform resultants.  For each of the twelve signed,
nonuniform branches, `new_two_prime_family.py` substitutes

$$
s=P^2/Q^2,\qquad b=\pm P^{2u}/Q^{2v}
$$

into $\operatorname{Res}_a(R_1,R_0)$.  It extracts the exact lowest
$P$-coefficient and lowest $Q$-coefficient.  A nonzero endpoint
coefficient modulo the corresponding prime is the unique term of minimum
valuation, so the resultant cannot vanish.  Factoring the opposite endpoint
integers shows that the union of possible inert exceptions is exactly
$\{5,13\}$.  Every signed local branch at these two residual primes is
then evaluated exactly and is nonzero.  The exact coefficient polygons after
setting $P=3,Q=r^n$ have a unique minimum for every $n\ge2$ (indeed for
$n\ge1$ in three of the four branches); the remaining $r=13,n=1$ value
is checked directly.  Therefore every inert prime power $r^n$, with
$r\ne3$, is excluded.  The finite residual evaluation closes a certified
endpoint argument; it is not extrapolated into a bounded-search claim.

Reproduce with:

```bash
.venv/bin/python research/global_descent/new_local_A_B_audit.py
.venv/bin/python research/global_descent/new_two_prime_family.py
```
