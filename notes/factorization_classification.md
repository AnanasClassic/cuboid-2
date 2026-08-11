# Complete factorization classification

Let `K=Q`, let `P(x)=P_s(x)`, and let `Q(u)=P(u^2)`.  In the cuboid domain
`s>0`, so `P(0)=-s^5 != 0` and all polynomials below are monic.

## Reducible `P`

Factor `P` into monic irreducibles over `K`.  Since `deg P=5`, if there is more
than one factor, a factor has degree at most two: otherwise two distinct
factors would already have total degree at least six.  Hence reducibility of
`P` produces either a rational linear factor (`1+4`) or a monic quadratic
factor (`2+3`).  Partitions such as `1+1+3` and `1+2+2` are already included.

## Irreducible `P`

Let `alpha` be a root and put `E=K(alpha)`.  Capell's composition theorem says
that `P(u^2)` is irreducible over `K` exactly when `u^2-alpha` is irreducible
over `E`.  In characteristic zero the latter fails exactly when
`alpha=beta^2` for some `beta in E`.

If this occurs, `K(beta)=E`: it contains `alpha=beta^2`, while `beta` already
belongs to `E`.  Therefore the minimal polynomial `R(u)` of `beta` is monic,
irreducible, and has degree five.  Its conjugates square to the roots of `P`,
so

```text
P(u^2) = R(u) * (-R(-u)).
```

Both factors are irreducible quintics.  Conversely such a symmetric split is
a nontrivial factorization.  Thus, after `1+4` and `2+3` are excluded, the
only remaining mechanism is symmetric `5+5`.

Finally, `Q_{p,q}` is primitive and monic in `Z[t]`; Gauss's lemma equates
factorization over `Q` and `Z`.  The invertible scaling `u=t/q^2` and the
nonzero scalar `q^20` preserve reducibility.  The excluded fibers `s=0` and
`s=1` correspond respectively to a zero parameter and `p=q`, neither of which
is admissible.

