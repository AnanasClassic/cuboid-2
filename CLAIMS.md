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

Statuses are deliberately not upgraded from transcripts or bounded searches.
