# Minimal proof dependency graph

## Scope

This note records the logical ancestors of C042 in the completed tree at
commit `c2b8edd`.  An arrow `A -> B` means that the proof of `B` uses `A`;
it does not mean merely that `A` appeared earlier in the research history.
The graph was reconstructed from the theorem proofs and their exact
certificates, not from filenames.

The simplification is presentational.  It does not remove a genuine
mathematical premise, weaken the theorem, or make C025 a premise.

## Exact claim-level DAG

```text
C001 normalization/scaling -----------+
C002 Gauss lemma ---------------------+--> C003 factorization classification
                                             |
                                             +------------------------------+
                                                                            |
C031 exact 2-descent for the 1+4 curve --> C029 rational points on that curve
                                             |
                                             +--> C004 exclude 1+4 ----------+
                                                                            |
C005 exact symmetric 5+5 Sturm certificate ---------------------------------+
                                                                            |
C012 signed-square constant                                                  |
  |                                                                         |
  v                                                                         |
C035 lossless compact signed-square locus                                    |
  |                                                                         |
  v                                                                         |
C039 common reciprocal quotient and exact C8 <-> E1 transport                |
  |                                                                         |
  v                                                                         |
C040 common-character valuation descent -----------+                         |
  |                                               |                         |
  |                      C041 square-abscissa theorem                         |
  |                                               |                         |
  +----------------------+------------------------+                         |
                         v                                                  |
                  exact exceptional-fibre audit                             |
                         |                                                  |
                         v                                                  |
                  C010 exclude 2+3 -----------------------------------------+
                                                                            |
                                                                            v
                                                   C042 irreducibility theorem
```

Thus C040 and C041 are parallel inputs to the final `2+3` exclusion: C040
reduces an admissible factor to a square-abscissa point on `D+`, while C041
classifies those points.  C041 does not depend on C040 as an arithmetic
statement about `D+`.

The exceptional-fibre audit is written inside
`notes/quadratic_cubic_completion.md` and replayed across C035, C039,
`product_character_simplification.py`, and the final lift table.  It has no
separate claim number, but it is a proof-critical node.

C041 has the following internal, computer-assisted DAG:

```text
Schaefer--Stoll 2-descent at 2,5,17
    -> rank(J)=1, torsion=<T>, D and T independent modulo 2
    -> index-independent finite Jacobian arithmetic at 7 and 23
    -> four surviving square-abscissa residue disks at 7
    -> exact 7-adic log direction (1,4)
    -> Coleman uniqueness in those four disks
    -> C041.
```

The independent `F_p/F_(p^2)` implementation is a cross-check of the finite
Jacobian orders and class tables.  It is not a logically additional premise.

## Proof-critical claims

| Claim | Role in the final proof |
|---|---|
| C001 | Relates `Q_{p,q}` to the normalized `P_s` under invertible scaling. |
| C002 | Moves between rational and integral monic factorizations. |
| C003 | Proves that only `1+4`, `2+3`, and symmetric `5+5` must be excluded. |
| C004 | Excludes `1+4`. |
| C005 | Excludes symmetric `5+5` by the pinned exact Sturm replay. |
| C010 | Excludes `2+3`. |
| C012 | Forces the physical constant sign `B=+d^2` or `B=-d^2`. |
| C029, C031 | Supply the rational-point and rank proofs used by C004. |
| C035 | Gives a lossless compact model, inverse, and denominator audit for both physical signs. |
| C039 | Gives the common `C8` quotient and exact two-way transport to `E1`, including all exceptional fibres. |
| C040 | Keeps the factor `2`, separates the valuation sign from the physical sign, excludes the negative valuation class, and maps the positive class to `D+` with square abscissa. |
| C041 | Classifies the square-abscissa points on `D+`; the separate exceptional-fibre audit excludes their lifts. |
| C042 | Combines the three factorization exclusions. |

C020 is a valid reformulation/consequence of the completed `2+3` argument,
but C042 needs only C010.  C024 (rank and torsion of `E1`) is not used by the
common-character descent or C041; C039 uses `E1` only as an explicitly
certified curve model.

## Valid results that are not ancestors of C042

The following proved or machine-verified claims are mathematically useful but
unnecessary for the final implication:

- C006--C007: the older resultant reconstruction and degenerate locus;
- C009, C013, C014: finite congruence sieves and the proof that no fixed
  finite sieve can be complete;
- C015, C017--C019: genus-four/reciprocal quotient calculations and the
  genus-33 three-character covers;
- C020: the simultaneous-character reformulation, redundant once C010 is
  stated;
- C021--C022, C026--C027, C034: prime-power, special two-prime, endpoint,
  and two-inert-prime-power families;
- C023--C024: the Frobenius fingerprint and independent arithmetic of the
  candidate elliptic curve;
- C028, C030, C032--C033: the older compact invariant and subresultant
  exception audits.  They are valuable independent red-team checks, but the
  C035/C039 route has its own complete inverse-denominator audit;
- C036--C038: Kummer and low-degree/ambient-automorphism no-go results.

These results should remain in the repository as research notes and
certificates.  Removing them from the main exposition does not retract them.

The following are also not proof dependencies and must retain their
conservative status:

- C008 and C016 are conditionally verified geometry statements;
- C011 is bounded computational evidence only;
- C025 is open.  The completed proof bypasses the direct normalization of
  `H(q,A)=0` through C035 and C039.

## Audit of the historical topics named in the task

| Topic in the frozen paper | Dependency status | Disposition in `paper/clean.tex` |
|---|---|---|
| Prime-power axis families | Valid side theorem (C021) | Remove. |
| Special two-prime family | Valid side theorem (C022) | Remove. |
| Endpoint restriction theorems | Valid necessary conditions (C026--C027) | Remove. |
| Two-inert-prime-power theorem | Valid side theorem (C034) | Remove. |
| Density sieve through 137 | Valid finite-density theorem (C013) | Remove. |
| Genus-33 three-character covers | Valid construction (C019) | Remove.  The final proof uses only the two common characters. |
| Kummer obstruction/no-go material | Valid negative result (C036--C038) | Remove. |
| Direct-normalization attempts | C025 remains open; no-go records are valid | Remove except for one sentence explicitly saying C025 is not used. |

## What can be removed from `paper/main.tex`

The following complete theorem blocks can be dropped without changing the
proof:

1. `Prime-power axis family`;
2. `A two-prime family`;
3. `Endpoint restrictions for two inert prime powers`;
4. `Two inert prime powers`;
5. the density theorem and its finite-sieve limitation paragraph;
6. `Reciprocal three-character descent`;
7. `Subresultant exception`;
8. `Arithmetic of the fingerprint candidate`.

The standalone signed-square theorem, linear-factor theorem, compact
transport, common-character descent, square-abscissa theorem, and final
factorization argument remain mathematically necessary.  In the clean paper,
the compact transport and common-character descent are nested inside one
consolidated `2+3 reduction` theorem so that `C8`, the Cayley coordinates,
and the translated `(k,h)` coordinates do not become top-level reader state.
Their exact identities and all exceptional fibres remain in the proof and
certificate appendix.

## Quantitative presentation count

The frozen paper has 13 theorem environments before its final theorem.  Eight
of those are historical or redundant blocks listed above.  The clean paper
uses five antecedent theorem/proposition blocks:

1. factorization reduction;
2. `1+4` exclusion;
3. signed-square lemma;
4. consolidated `2+3` reduction;
5. square-abscissa classification;

the `5+5` certificate is stated inside the final proof.  Thus the number of
top-level antecedent theorem blocks falls from **13 to 5**.  The internal
claim-level DAG above is unchanged; presentation consolidation is not a
claim that the exact transport or exceptional-fibre certificates disappeared.
