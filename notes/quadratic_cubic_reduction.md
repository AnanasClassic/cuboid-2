# Exact quadratic--cubic reduction

Take `D(x)=x^2+a*x+b`.  Exact Euclidean division gives

```text
P_s(x) mod D(x) = R1(s,a,b)*x + R0(s,a,b),
R1 = b^2 + u(s,a)b + v(s,a),
R0 = m(s,a)b^2 + n(s,a)b - s^5.
```

The canonical expanded polynomials are generated in
`artifacts/polynomials.json`.  They are reconstructed from `P_s`, not copied
from a resultant.

Define

```text
L = n - m*u,
C = m*v + s^5.
```

The exact polynomial identity

```text
R0 - (L*b-C) = m*R1
```

shows that on `R1=0` the second condition is `L*b-C=0`.  If `L != 0`, then
`b=C/L`; substitution into `R1=0` is equivalent to

```text
F(s,a) = C^2 + u*L*C + v*L^2 = 0.
```

This is a two-way lift, not merely a one-way resultant: `F=0`, `L!=0`, and
`b=C/L` imply both remainder equations.  SymPy independently verifies
`Resultant_b(R1,R0)=F`, with

```text
deg_s F = 16, deg_a F = 10, total degree = 17,
F(1,a) = -a^4(a-2)^6.
```

For `L=C=0`, two independent eliminations were checked.  Eliminating `s`
yields `(a-2)^6` times an irreducible degree-21 polynomial over `Q`.
Eliminating `a` yields

```text
64*(s-1)^3*(s+1)^3*H_21(s).
```

The leading coefficient of `H_21` is nonzero modulo 13 and its values at all
13 residues are nonzero, which is an explicit certificate that it has no
rational root.  The remaining fibers give `a=2`, `b=1`.  Hence the complete
rational degenerate locus in factor data is
`(s,a,b)=(1,2,1),(-1,2,1)`.
