# Reciprocal geometry and the square-parameter pullback

The exact reciprocal identity is

```text
P_s(x) = -s^5*x^5*P_(1/s)(1/x).
```

On quadratic-factor data it induces

```text
tau(s,a,b) = (1/s, a/b, 1/b).
```

Off the degenerate locus, `b=C/L`, so this also gives a rational involution on
the plane obstruction model.  Useful invariants include

```text
U=s+1/s, V=b+1/b, W=a+a/b,
J=(s-1/s)(b-1/b),  J^2=(U^2-4)(V^2-4).
```

## Genus audit

Exact calculation gives

```text
Disc_x(P_s) = 2^11*s^9*(s-1)^12*(s+1)^4*H_6(s),
H_6=s^6+15s^5-1585s^4+3052s^3-1585s^2+15s+1,
Disc(H_6)=-120976582094426834375000000.
```

The six simple roots of `H_6`, together with the local Newton forms at
`s=0,-1,infinity`, give total ramification 32 on the degree-10 two-subset
resolvent.  Riemann--Hurwitz gives genus 7.  The local forms are replayed in
`src/geometry_audit.py`.

The reciprocal involution has twelve fixed normalization points according to
the branch audit (ten above `s=1`, two above `s=-1`), giving quotient genus 1.
The point `(s,a,b)=(0,6,1)` descends rationally, so this quotient is elliptic.
No Weierstrass model, rank bound, or complete rational-point list has yet been
certified.

## Imposing `s=z^2`

The square pullback is not elliptic.  The valuations above zero and infinity
produce eight branch points in the double cover of the genus-7 curve, hence

```text
genus(F(z^2,a)=0 after normalization) = 17.
```

The reciprocal involution has two lifts, with quotient genera 4 and 8; the
deck quotient returns the genus-7 curve.  Therefore the square condition does
not reduce the problem to the elliptic quotient.  The genus-4 quotient plus
complete lift checks is the most promising next target.

The fixed-point and quotient-genus calculation is presently labelled
CONDITIONALLY VERIFIED because it has one exact implementation but no second
independent normalization computation.
