# Linear-factor completion audit

This directory closes the independent-computation gap in claim `C004`
without using the original Magma transcript.

For

\[
C:\quad w^2=t^5+21t^4+26t^3+10t^2+5t+1,
\]

the public LMFDB record is `11008.a.176128.1`.  The exact change of variables

\[
X=\frac{t-1}{2(t+1)},\qquad
Y=-\frac{w}{(t+1)^3}
\]

gives its simplified model

\[
Y^2=16X^5+8X^4-8X^3-4X^2+1.
\]

LMFDB marks the Mordell--Weil group as provably
`Z + Z/2Z`, the 2-Selmer rank as `2`, and the displayed six rational points
as complete.  This is an independent database computation, but its stated
provenance is Michael Stoll's Magma implementation, so it is corroboration,
not a Sage-only rank certificate.

## Exact 2-descent: the rank premise is discharged

Run

```bash
.venv/bin/python research/linear_factor_completion/two_descent_rank.py
```

This is an explicit Schaefer--Stoll descent in

\[
\mathbb Q\times\mathbb Q[z]/(z^4-2z-1).
\]

It uses PARI's unconditional `bnfcertify` and exact local-square tests, exports
the complete global and local matrices, and proves

\[
\dim_{\mathbf F_2}\operatorname{Sel}^{(2)}(J/\mathbb Q)=2,
\qquad \operatorname{rank}J(\mathbb Q)\leq1.
\]

The global norm-kernel bound has dimension four.  Its exact intersection
with the complete \(2\)-adic Kummer image consists of four elements (dimension
two); the real condition preserves these four, and the condition at 43 is
automatic because the discriminant has 43-adic valuation one.  Two independent
survivors are the Kummer images of `(1,8)-infinity` and the rational
2-torsion point, so the upper bound is attained.  See
`two_descent_proof.md` for the proof and the interpretation of every matrix.

## Sage Coleman certificate

Run

```bash
sage -python research/linear_factor_completion/sage_chabauty_p5.py
```

Together with `two_descent_rank.py`, the script proves exactly, without
Magma, that

\[
C(\mathbb Q)=\{\infty,(-1,0),(0,\pm1),(1,\pm8)\}.
\]

It verifies all of the following:

1. `p=5` is a prime of good reduction and `#C(F_5)=6`.
2. The six known rational points reduce bijectively to `C(F_5)`.
3. `#J(F_3)=22` and `#J(F_5)=28`, so rational torsion has order at most
   `2`; the divisor `[(0,1)-infinity]` is not 2-torsion and is therefore
   infinite.
4. Sage's independent Coleman integration computes the annihilating
   differential modulo `5` as `(1+t)dt/(2w)`.
5. That differential is nonzero in five residue discs.  In the remaining
   disc, centred at the finite Weierstrass point `(-1,0)`, the local parameter
   `u=w=5z` gives the exact Strassmann form

   ```text
   G(5z)/25 = z*(unit + 5*z^2*Z_5[[z^2]]).
   ```

   Hence that disc also contains only its known rational point.

Consequently the Coleman function has at most one zero in every residue disc,
and every residue disc already contains one of the six known rational points.
No Mordell--Weil saturation hypothesis is needed: any nonzero point spans
`J(Q) tensor Q_5` when the rank is at most one.
The full local argument, including the exceptional-disc valuation inequality,
is written out in `chabauty_p5_proof.md`.

## Exact exceptional lift table

The root-to-curve map in arXiv:2601.04241v2 uses

\[
U(t)=\frac{2(t^5+6t^4+30t^3+16t^2+9t+2)}
{t(t-1)^2(t^2+6t+1)},\qquad U=s+s^{-1}.
\]

The complete rational-point list gives:

| point(s) on `C` | quotient value | lift to `s` | cuboid status |
|---|---:|---:|---|
| `t = infinity` | `U = 2` | `s = 1` | excluded `p=q` |
| `t = -1` | `U = -2` | `s = -1` | not positive |
| `t = 0`, `w = +/-1` | pole of `U` | no finite nonzero `s` | none |
| `t = 1`, `w = +/-8` | pole of `U` | no finite nonzero `s` | none |

The remaining denominator `t^2+6t+1` has no rational root.  The omitted
quotient singular branch `U=2` is exactly `s=1`; it is excluded before the
slope parameter `t=(V+2)/(U-2)` is introduced.  Thus no admissible positive
rational-square parameter is lost at a denominator or exceptional point.

The descent above supplies that rank bound independently.  Consequently, when
`sage_chabauty_p5.py` prints its final `PASS` line, the two scripts together
give an unconditional, Magma-free determination of the rational points; there
is no Mordell--Weil saturation or rank premise left.

The pure-Python exact prerequisites (including the quotient resultant, square
identities, finite-field counts, torsion gcd, and exceptional lifts) replay as

```bash
.venv/bin/python research/linear_factor_completion/exact_prerequisites.py
```
