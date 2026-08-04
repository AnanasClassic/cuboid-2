# A density-99.998% theorem for the `2+3` case

Write

```text
Q_{p,q}(t) = H_{p,q}(t^2),  H_{p,q}(X) in Z[X].
```

`H` is monic of degree five.  If it has a quadratic factor over `Q`, Gauss's
lemma gives a monic quadratic factor in `Z[X]`.  Reducing modulo any prime
preserves its degree and divisibility.  Therefore a residue class for which
`H mod ell` has no monic quadratic divisor is an unconditional obstruction.

For nonzero `lambda mod ell`, weighted homogeneity gives

```text
H_{lambda*p,lambda*q}(lambda^4 X) = lambda^20 H_{p,q}(X),
```

so the condition depends only on `(p:q) in P^1(F_ell)`.  A compact
seven-prime certificate has the exact exhaustive counts:

| ell | all projective classes | obstructed | residual |
|---:|---:|---:|---:|
| 41 | 42 | 20 | 22 |
| 71 | 72 | 44 | 28 |
| 83 | 84 | 44 | 40 |
| 97 | 98 | 56 | 42 |
| 101 | 102 | 64 | 38 |
| 113 | 114 | 64 | 50 |
| 137 | 138 | 84 | 54 |

For primitive integer pairs, `(p,q) mod ell` is nonzero and its projective
class is uniform on `P^1(F_ell)`.  Chinese remaindering makes these local
conditions independent for the finite prime set.  The factors at primes not
in the set cancel when conditioning on global coprimality (equivalently, use
Möbius inversion before taking the box limit).  Thus the residual natural
density among positive primitive pairs is

```text
(22/42)(28/72)(40/84)(42/98)(38/102)(50/114)(54/138)
  = 1375/517293.
```

The compact excluded density is `515918/517293`.  Running the same exhaustive
calculation for every prime at most 97 strengthens the result to

```text
excluded = 5689139917/5689253052 = 99.9980114261...%,
residual = 113135/5689253052.
```

The diagonal `p=q` has density zero, so removing it does not change the result.

`src/modular_sieve.py` checks every monic quadratic by exact remainder.  The
test suite independently factors each quintic over `F_ell` with SymPy and
compares the full obstructed class sets for all 25 primes.
