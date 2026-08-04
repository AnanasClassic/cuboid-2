# Claim ledger

| ID | Status | Claim | Evidence / dependency |
|---|---|---|---|
| C001 | PROVED | `Q_{p,q}(t)=q^20 P_s(t^2/q^4)` with `s=(p/q)^2`. | `src/symbolic_reduction.py` |
| C002 | PROVED | Reducibility over `Q` and `Z` is equivalent for monic `Q_{p,q}`. | Gauss's lemma; `notes/factorization_classification.md` |
| C003 | PROVED | It suffices to exclude `1+4`, `2+3`, and symmetric `5+5`. | Gauss + Capell proof in `notes/factorization_classification.md` |
| C004 | CONDITIONALLY VERIFIED | No `1+4` split for positive rational `s != 1`. | Algebra checked exactly; rational-point completeness depends on the unrerun Magma--Chabauty transcript of arXiv:2601.04241v2. |
| C005 | MACHINE-VERIFIED | No irreducible `5+5` split for admissible `p,q`. | Exact replay of arXiv:2601.04240 Script 02; `scripts/replay_5plus5.sh`. |
| C006 | MACHINE-VERIFIED | Exact `R0,R1,L,C,F` reconstruction and `Resultant_b(R1,R0)=F`. | `src/symbolic_reduction.py`, `artifacts/polynomials.json` |
| C007 | MACHINE-VERIFIED | Rational degenerate locus is exactly `(s,a)=(1,2),(-1,2)`. | Exact resultant, irreducible degree-21 cofactor, and gcd specialization. |
| C008 | CONDITIONALLY VERIFIED | The degree-17 plane model has geometric genus 7 and reciprocal quotient genus 1; the square pullback has genus 17. | Published Magma genus plus exact reciprocal/fixed-point audit; `notes/square_parameter_pullback.md`. |
| C009 | MACHINE-VERIFIED | All primes at most 97 exclude quadratic factors on a union of density `5689139917/5689253052`. | `src/modular_sieve.py`, independent SymPy factorization tests, JSON certificate. |
| C010 | OPEN | No admissible rational-square point on the residual `2+3` locus exists. | Exact remaining obstruction. |
| C011 | COMPUTATIONAL EVIDENCE | The eight height-bounded points in arXiv:2601.07899v2 are complete. | Only searched through `H=10^9`; explicitly a conjecture in the paper. |
| C012 | PROVED | The constant of a hypothetical integral quadratic factor is `B=+d^2` or `B=-d^2`. | Newton-polygon proof, including primes 2 and 3; `notes/signed_square_descent.md`. |
| C013 | MACHINE-VERIFIED | Respecting the fixed sign of `B`, odd primes at most 137 exclude density `3917894203934863/3917894203948032`. | Two independent exact algorithms; `src/signed_square_sieve.py`, JSON certificate, regression test. |
| C014 | PROVED | No finite fixed set of reduction primes can exhaust the remaining case. | The infinite family `p=0, q=1` modulo their product survives with divisor `X^2`; `notes/signed_square_descent.md`. |
| C015 | MACHINE-VERIFIED | Exact equations and generic maps for the genus-four plane quotient and its bielliptic plane quotient. | `research/arithmetic_geometry/derive_genus4_quotient.py`, sparse artifact, tests. |
| C016 | CONDITIONALLY VERIFIED | The normalizations of the displayed quotient models have genera 4 and 1 with the stated six branch points. | Riemann--Hurwitz/local branch audit; pending a second normalization system. |

Statuses are deliberately not upgraded from transcripts or bounded searches.
