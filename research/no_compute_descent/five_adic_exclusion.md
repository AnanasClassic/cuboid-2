# Exact 5-adic exclusion in the fifth-power norm descent

Assume that a rational quadratic factor exists.  By the translated Newton
argument in `README.md`, write

```text
p^2+q^2 = delta*r^5,   delta in {1,2},
```

and suppose `5^m | r`, `m>=1`.  This note proves a contradiction over `Q_5`.

## The exact local unit class

The Gaussian parametrization has the form

```text
p+i*q = kappa*alpha^5,
```

where `kappa` is a Gaussian unit in the opposite-parity case and is
`(1+i)` times a Gaussian unit in the odd--odd case.  Choose the split
embedding `Q(i) -> Q_5` for which `v_5(alpha)=m`.  Put

```text
P = p+i*q,  Pbar = p-i*q,
d = (p^2+q^2)/q^2 = 5^(5m)*d0.
```

Since `q=(P-Pbar)/(2i)`, exact algebra gives

```text
d0 = -4 * (P/5^(5m))/Pbar * (1-P/Pbar)^(-2).
```

The first quotient is a fifth power times `kappa/kappa_bar`.  The latter is
one of `+1,-1,+i,-i`, hence is itself a fifth power.  Moreover
`v_5(P/Pbar)=5m>=5`.  The fifth-power map sends `1+5*Z_5` onto
`1+25*Z_5`; equivalently this follows from the 5-adic logarithm.  Therefore
`(1-P/Pbar)^(-2)` is a fifth power.  Consequently

```text
d0 = -4*h^5
```

for some `h in Z_5^*`.

## Eisenstein after the final translation

Use the exact expansion

```text
P_{-1+d}(-1+y) =
    y^5
  + d*(3-2*d)*y^4
  + d*(-56+60*d-18*d^2+d^3)*y^3
  + d*(144-192*d+80*d^2-8*d^3-d^4)*y^2
  - 4*d*(40-68*d+42*d^2-11*d^3+d^4)*y
  + 4*d*(d-2)^4.
```

Set `y=5^m*h*Y` and divide by `5^(5m)*h^5`.  The resulting monic quintic
`G(Y)` has the following exact valuation bounds:

```text
coefficient of Y^4: at least 4m,
coefficient of Y^3: at least 3m,
coefficient of Y^2: at least 2m,
coefficient of Y:   at least m+1.
```

Thus all four intermediate coefficients are divisible by `25`.  Its constant
coefficient is

```text
-16*(d-2)^4 = -256  (mod 25),
```

because `v_5(d)>=5`.

Now put `Y=Z+1`.  The nonleading coefficients of `(Z+1)^5` are divisible by
`5`, all perturbation terms above are divisible by `25`, and

```text
G(1) = 1-256 = -255 = -5 (mod 25).
```

Hence `G(Z+1)` is 5-Eisenstein.  It is irreducible over `Q_5`, contradicting
the assumed rational quadratic factor.

## Conclusion

In every hypothetical counterexample,

```text
gcd(r,5)=1.
```

Together with the residual-binomial theorem, every prime divisor `ell` of
`r` must therefore satisfy

```text
ell = 9 (mod 20),
```

or

```text
ell = 1 (mod 20) and 2 is a fifth power modulo ell.
```
