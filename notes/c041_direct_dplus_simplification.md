# Direct $p=3$ proof of C041 on $D_+$

## Status

The direct genus-two route succeeds.  Put

$$
D_+:\quad R^2=a(4a^4-8a+5),\qquad
J=\operatorname{Jac}(D_+),
$$

and

$$
D=[(1,1)-\infty],\qquad T=[(0,0)-\infty].
$$

The existing exact Schaefer--Stoll certificate proves

$$
\operatorname{rank}J(\mathbf Q)=1,\qquad
J(\mathbf Q)_{\rm tors}=\langle T\rangle\simeq\mathbf Z/2\mathbf Z,
$$

with $D,T$ independent modulo $2$.  Using that input, exact local
arithmetic at $3$, and only the small integral saturation fact

$$
\#J(\mathbf F_7)=42,\qquad \operatorname{ord}(\bar D)=21,
$$

the new certificate proves directly that

$$
\boxed{
\{P\in D_+(\mathbf Q):a(P)\in\mathbf Q^2\}
=\{\infty,(0,0),(1,1),(1,-1)\}.}
\tag{1}
$$

This is Success Level B.  In `paper/clean3.tex` it also gives Level C:
the recommended proof is no longer routed through the genus-three curve
$C_3$, and the paper is at most five pages.

The exact replay is

```text
research/proof_simplification_3/dplus_p3_square_abscissa.py
research/proof_simplification_3/dplus_p3_square_abscissa.json
tests/test_dplus_p3_square_abscissa.py
```

No bounded search or finite-precision $3$-adic approximation occurs.

## 1. Projective classification of square-abscissa disks

Write

$$
g(a)=4a^4-8a+5,
\qquad R^2=a\,g(a).
$$

Let $a\in\mathbf Q_3$ be a square.

### 1.1 Positive valuation

If $a\ne0$ and $v_3(a)>0$, then $a=u^2$ for some
$u\in\mathbf Q_3$, and

$$
\left(\frac Ru\right)^2=g(a).
$$

But $a\in3\mathbf Z_3$ gives

$$
g(a)\equiv5\equiv2\pmod3,
$$

which is a nonsquare unit.  This is impossible.  Thus the only
square-abscissa point with $v_3(a)>0$, allowing $a=0$, is $(0,0)$.

### 1.2 Unit abscissa

If $v_3(a)=0$, a square unit satisfies $a\equiv1\pmod3$.  The curve
equation then gives

$$
R^2\equiv1\pmod3,\qquad R\equiv\pm1\pmod3.
$$

Hence the point lies in one of the disks of $(1,1)$ and $(1,-1)$.
The other two affine disks of $D_+(\mathbf F_3)$, centered at
$(2,\pm1)$, are real curve disks but cannot contain a square abscissa.

### 1.3 Negative valuation and infinity

If $v_3(a)<0$, the term $4a^5$ has strictly least valuation in the
right side.  Therefore

$$
2v_3(R)=5v_3(a),
$$

so $v_3(a)$ is even.  The rational function

$$
t=\frac{2a^2}{R}
\tag{2}
$$

satisfies

$$
v_3(t)=-\frac12v_3(a)>0.
$$

It is a uniformizer at infinity.  Since the hyperelliptic model has odd
degree $5$, its smooth projective completion has exactly one point at
infinity.  Thus every negative-valuation square abscissa lies in that one
disk.

Combining the three cases, every point relevant to (1) lies in precisely one
of

$$
\infty,\quad(0,0),\quad(1,1),\quad(1,-1).
\tag{3}
$$

This is a projective $3$-adic classification, not merely the observation
that finite-field squares are $0$ or $1$.

## 2. Direct $D_+$ annihilator

Use

$$
\omega_0=\frac{da}{R},\qquad
\omega_1=\frac{a\,da}{R}.
$$

Exact Cantor arithmetic computes $11D$.  After shifting $a=1+x$, its
Mumford support polynomial is $x^2+bx+c$, with

$$
\begin{array}{c|ccc}
 &b&c&b^2-4c\\ \hline
v_3&1&2&4\\
\text{unit modulo }3&2&1&1.
\end{array}
\tag{4}
$$

The reduction of the support is the principal divisor

$$
(1,1)+(1,-1)-2\infty=\operatorname{div}(a-1).
$$

Divided formal integration of $\omega_0,\omega_1$, with universal
power-difference and inverse-square-root coefficient bounds, gives

$$
\lambda=\frac{\log_1D}{\log_0D}\equiv7\pmod{27},
\qquad
v_3(\lambda-1)=1,
\qquad
v_3(\log_0D)=2.
\tag{5}
$$

Thus the rank-one annihilator on $D_+$ is

$$
\eta_D=(\lambda-a)\frac{da}{R}.
\tag{6}
$$

Equations (4)--(6) are replayed inside the new certificate without using a
genus-three point, quotient, rank, or differential.  The present
implementation shares only hardened exact Cantor, finite-Jacobian, and
universal-tail routines with the PR \#6 module; it imports no $C_3$
artifact or theorem.

## 3. The two disks at $a=1$

Do not assume that $D$ is primitive.  After a torsion shift write

$$
J(\mathbf Q)=\mathbf ZG\oplus\langle T\rangle,\qquad D=mG.
$$

Independence of $D,T$ modulo $2$ makes $m$ odd.  At $7$,

$$
\#J(\mathbf F_7)=42,\qquad\operatorname{ord}(\bar D)=21.
$$

If $q=\operatorname{ord}(\bar G)$, then

$$
\frac{q}{\gcd(q,m)}=21,\qquad q\mid42.
$$

The alternative $q=42$ would make $m$ even.  Hence

$$
q=21,\qquad\gcd(m,21)=1,
\tag{7}
$$

so $3\nmid m$, and (5) gives $v_3(\log_0G)=2$.

Let $P=(1,\rho)$, $\rho=\pm1$, and let $Q\in D_+(\mathbf Q)$ be in
the same residue disk.  For some $n\in\mathbf Z$, $e\in\{0,1\}$,

$$
[Q-P]=nG+eT,\qquad\log T=0.
$$

With $x=a(Q)-1$,

$$
\int_P^Q\omega_0=n\log_0G\in9\mathbf Z_3.
$$

The exact local primitive satisfies

$$
H_0(x)=x\cdot\mathbf Z_3^\times
\quad\text{for every }x\in3\mathbf Z_3,
$$

so $x\in9\mathbf Z_3$.  Put $x=9z$.  From (5)--(6),

$$
\frac1{27}\int_P^Q\eta_D
\equiv c_\rho z\pmod3,\qquad c_\rho\ne0.
\tag{8}
$$

All omitted terms in (8) are controlled uniformly by

$$
2n-2-v_3(n)\ge1,\qquad
2n-3-v_3(n)\ge1
\quad(n\ge2).
$$

Strassmann therefore gives $z=0$.  Each $a=1$ disk contains only its
known rational point.

The small $p=7$ input in (7) is an integral index/saturation lemma.  It is
not a residue sieve and does not use a square-abscissa table, a $7$-adic
logarithm, or Coleman integration at $7$.

## 4. The Weierstrass disk at $(0,0)$

The coordinate $a$ is not a uniformizer at $(0,0)$.  For

$$
F(a,R)=R^2-a\,g(a),
$$

one has

$$
\frac{\partial F}{\partial a}(0,0)=-5\in\mathbf Z_3^\times.
$$

Thus $R$ is a valid local parameter.  No formal Coleman expansion is
needed: if $a=u^2\ne0$ in this disk, then

$$
(R/u)^2=g(a)\equiv2\pmod3,
$$

a contradiction.  Therefore $(0,0)$ is the only square-abscissa point in
its disk.

## 5. Infinity

Put $w=1/a$ and use the rational uniformizer (2).  The curve equation gives
the exact relation

$$
w=t^2\left(1-2w^3+\frac54w^4\right).
\tag{9}
$$

Its derivative with respect to $w$ at $(t,w)=(0,0)$ is $1$.
The formal implicit-function theorem over $\mathbf Z_3$ therefore gives a
unique $3$-integral series

$$
w=t^2-2t^8+\frac54t^{10}+O(t^{12}).
\tag{10}
$$

Using $R=2/(w^2t)$ and $da=-w^{-2}dw$, (6) becomes

$$
\eta_D=
\frac{t}{2w}(1-\lambda w)\,dw.
\tag{11}
$$

Equations (9)--(11) show that $\eta_D/dt\in\mathbf Z_3[[t]]$ has constant
term $1$.  If $\mathcal F$ is its primitive from infinity, then

$$
\frac{\mathcal F(3z)}3\equiv z\pmod3.
\tag{12}
$$

The universal tail estimate is

$$
n-1-v_3(n)\ge1\qquad(n\ge2);
$$

thus (12) is not a truncated-series assumption.  Infinity is the only
rational point in its disk, hence certainly the only square-abscissa point
there.

Together, Sections 3--5 prove (1).

## 6. Exact dependency comparison

### Original clean C041

```text
Schaefer--Stoll descent
  -> 7/23 index-independent MW sieve
  -> p=7 formal logarithm
  -> p=7 Coleman disk bound
  -> C041.
```

### PR #6 genus-three C041

```text
Schaefer--Stoll descent
  -> rank E1
  -> Jac(C3) ~ E1 x Jac(D+)
  -> p=3 genus-three annihilator and six disks
  -> p=7 integral 3-saturation
  -> C3(Q)
  -> C041.
```

### Direct $D_+$ C041

```text
Schaefer--Stoll descent
  -> direct p=3 D+ annihilator
  -> square-abscissa disk classification
  -> p=7 integral 3-saturation only in the a=1 disks
  -> C041.
```

The recommended clean proof no longer depends on:

* $C_3$;
* $\operatorname{rank}E_1(\mathbf Q)=1$;
* the isogeny
  $\operatorname{Jac}(C_3)\sim E_1\times\operatorname{Jac}(D_+)$;
* a genus-three annihilator-dimension argument;
* the two $C_3$ infinity disks;
* the four $C_3$ affine disks.

Those results remain valid independent theorems and certificates.

## 7. Failure modes and final level

* Merely reducing a square modulo $3$ is incomplete; positive, zero, and
  negative valuations and the projective point must be separated.
* At $(0,0)$, $a$ is not a local parameter.  The proof uses $R$ and
  the unit derivative $-5$.
* At infinity, $1/a$ is not itself a uniformizer.  The proof uses the
  rational function $t=2a^2/R$.
* The $p=7$ step cannot currently be removed.  Without (7), the unknown
  Mordell--Weil index could be divisible by $3$, and
  $v_3(\log_0G)=2$ would not follow.  Therefore Level D is not claimed.
* All formal-series uniqueness statements use universal coefficient
  integrality and valuation inequalities, not a fixed truncation.
* C025, bounded searches, fingerprints, and generic-open exceptional-fibre
  arguments remain absent.

The final result is Level C: direct $D_+$ proof (Level B) plus a
warning-free `paper/clean3.tex` of at most five pages.  The theorem remains
fully proved, and all previous C041 routes remain independently runnable.

## 8. Replay

```bash
.venv/bin/python \
  research/proof_simplification_3/dplus_p3_square_abscissa.py

PYTHONDONTWRITEBYTECODE=1 .venv/bin/python -m pytest -q \
  tests/test_dplus_p3_square_abscissa.py

PYTHONDONTWRITEBYTECODE=1 PYTHONOPTIMIZE=1 \
  .venv/bin/python -m pytest -q \
  tests/test_dplus_p3_square_abscissa.py
```
