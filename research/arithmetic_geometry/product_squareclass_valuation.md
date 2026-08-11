# Product-character valuation descent

On the translated copy of

\[
E_1:Y^2=X^3-5X+4
\]

put

\[
h=X+1,\qquad k=(Y+2)/X.
\]

Away from the separately audited zeros and poles, the product of the first
two cuboid square characters is a square exactly when

\[
z^2=2kh. \tag{1}
\]

Here \(h\) is a local elliptic coordinate; it is **not** the original cuboid
parameter customarily denoted \(s\).  Substituting \(Y=kX-2\) in the
equation of \(E_1\), then writing \(X=h-1\), gives

\[
h^2-(k^2+2)h+(k^2+4k-4)=0. \tag{2}
\]

## Valuations

Let \(\ell\) be odd.  If \(v_\ell(k)<0\), the Newton polygon of (2) gives
\(v_\ell(h)\in\{0,2v_\ell(k)\}\).  If \(v_\ell(k)>0\), its constant term
is an \(\ell\)-adic unit and both roots are units.  Equation (1) therefore
forces \(v_\ell(k)\) to be even in every case.

At 2 the discriminant of (2) is

\[
\Delta=k^4-16k+20.
\]

If \(v_2(k)=0\), then \(\Delta\equiv5\pmod8\), impossible for a square.  If
\(v_2(k)\ge2\), then \(v_2(\Delta)=2\) and
\(\Delta/4\equiv5\pmod8\), again impossible.  For negative valuation the
same Newton polygon as above shows that \(v_2(h)\) is even; (1) then says
that \(v_2(k)\) is odd.  The only remaining nonnegative case is
\(v_2(k)=1\).  Consequently

\[
k=2\epsilon u^2,\qquad h=\epsilon v^2,\qquad
\epsilon\in\{+1,-1\}. \tag{3}
\]

## The negative sign is impossible

For \(\epsilon=-1\), treating (2) as a quadratic in \(u^2\) gives the
necessary square equation

\[
W^2=-(v^2+2)(v^4+v^2-4). \tag{4}
\]

Write \(v=m/n\) in lowest terms.  Then the integer

\[
-(m^2+2n^2)(m^4+m^2n^2-4n^4)
\]
would be a square.  If \(m,n\) are odd it is 6 modulo 8.  If \(m\) is odd
and \(n\) even, it is 3 or 7 modulo 8 according as \(v_2(n)=1\) or at least
2.  If \(m\) is even and \(n\) odd, its 2-adic valuation is respectively 5
or 3 according as \(v_2(m)=1\) or at least 2.  Every case is impossible.

## The positive genus-two quotient

For \(\epsilon=+1\), the discriminant condition is

\[
r^2=4u^8-8u^2+5. \tag{5}
\]

Putting \(a=u^2\) and \(R=ur\) maps (5) to

\[
D_+:\quad R^2=4a^5-8a^2+5a. \tag{6}
\]

Thus the remaining product-character problem is precisely to classify the
rational points of \(D_+\) whose abscissa is a rational square.  The exact
symbolic identities and the complete parity table are replayed by
`product_squareclass_valuation.py`.
