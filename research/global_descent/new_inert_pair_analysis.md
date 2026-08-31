# Exact endpoint analysis for two inert prime powers

Put

$$
p=L^m,\qquad q=R^n,
$$

where $L,R$ are distinct odd primes and
$(2/L)=(2/R)=-1$.  Local residual irreducibility restricts the normalized
Newton indices to

$$
u,v\in\{0,3,4\}.
$$

The diagonal cases $u=v$ are already excluded by the uniform resultant
theorem.  For every one of the twelve signed nonuniform branches, exact
factorization of the lowest endpoint coefficients gives the same canonical
necessary system:

$$
R^{en}\equiv\sigma\pmod L,\qquad
L^{em}\equiv\sigma\pmod R,
$$

where

$$
e=2|u-v|\in\{2,6,8\},
\qquad
\sigma=\begin{cases}+1,&b>0,\\-1,&b<0.\end{cases}
$$

`new_inert_pair_endpoint.py` reconstructs the remainder equations and the
resultant, extracts all endpoints, and verifies that their squarefree parts
are exactly $X^e-\sigma$.

Quadratic reciprocity gives real but incomplete progress:

- every negative branch requires $L\equiv R\equiv5\pmod8$, since $-1$
  must be a quadratic residue;
- in the surviving negative $e=2,6$ branches, the 2-primary component of
  the relevant residue has order exactly 4.  Hence

  $$
  m\equiv n\equiv1\pmod2,
  \qquad
  \left(\frac LR\right)=\left(\frac RL\right)=-1.
  $$

  Indeed, the powered base is a quadratic nonresidue; an even exponent
  $m$ or $n$ would make it a square.  Since both primes are
  $1\pmod4$, quadratic reciprocity makes the two symbols equal;
- the negative $e=8$ branches are impossible: $x^8=-1$ would give an
  element of order divisible by 16, hence $16\mid L-1$, incompatible with
  an inert prime;
- when $m=n=1$, the positive $e=2$ branch is impossible.  If $L<R$,
  then $R\mid L^2-1=(L-1)(L+1)$ forces $R=L+1$, impossible for distinct
  odd primes.

The remaining systems cannot be removed by endpoint valuations and
reciprocity alone.  This limitation is exact:

- for any distinct primes, choosing $m=R-1$ and $n=L-1$ satisfies every
  positive endpoint system by Fermat's theorem;
- $(L,R,m,n)=(5,13,1,1)$ satisfies both negative systems with $e=2,6$.
- already with $m=n=1$, the pair $(3,13)$ satisfies positive $e=6$,
  while $(3,5)$ satisfies positive $e=8$.

Thus the residual factorization problem for two inert prime powers is reduced
to the five explicit systems

$$
\begin{array}{c|c}
b>0&e=2,6,8,\\
b<0&e=2,6\text{ and }L\equiv R\equiv5\pmod8.
\end{array}
$$

These congruences are necessary, not sufficient: the full resultant or the
second remainder equation must still be used.  Promoting them to a general
two-prime theorem would be unjustified.

In particular, the displayed survivor $(5,13,1,1)$ only survives the
lowest-endpoint test.  Exact substitution in the full projection is nonzero
for all four negative $e=2,6$ branches, so it is not a resultant point and
does not define a quadratic factor.

## Subsequent full-projection closure

The no-go above remains important: endpoint congruences and reciprocity alone
do not close the family.  The later certificate
`second_endpoint_layer.py` goes beyond them.  It uses the two-power gap to the
next coefficient, then exact positive-coefficient charts of the **full**
projection.  All five survivor systems are thereby excluded, proving that no
quadratic factor exists when $p,q$ are powers of two distinct inert odd
primes.  See `second_endpoint_layer.md` for the proof and its explicit scope.
