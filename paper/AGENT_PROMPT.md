Rewrite the paper in `paper/` from scratch so that it is a rigorous, self-contained mathematical proof of Sharipov's second cuboid conjecture that follows the Lean formalization in `lean/Cuboid2/` step by step. Deliver a complete, compiling LaTeX article in ONE session.

## Hard constraints

1. **Subagent models.** Every `Agent` call you make MUST pass `model: "opus"` (or `model: "sonnet"` for purely mechanical tasks such as extracting a polynomial from a Lean file). Never spawn a subagent without an explicit `model` parameter, and never use `model: "fable"`. This is a quota constraint, not a quality preference.
2. **Do not modify anything under `lean/`, `research/`, `src/`, `tests/`, `scripts/`.** The Lean development is the source of truth; the paper adapts to it, never the other way round.
3. **No mathematics that is not in Lean.** Every theorem, lemma and proposition in the paper must correspond to one or more Lean theorems in the import closure of `lean/Cuboid2/Main.lean`, and must carry the Lean name (in a footnote or a `\leanref{}` macro). If you cannot find the Lean theorem for a claim, do not write the claim. Standard textbook facts (Mordell–Weil, reduction map is a homomorphism, formal group torsion-freeness, Fermat's `a^4+b^4=c^2`) may be cited from the literature; say in Chapter 7 which of these Lean proves from scratch.
4. **Do not print large data.** Polynomials with more than ~15 terms (except the 29-term curve C8) are described by degree, term count and Lean file, not printed. Finite certificates (`decide`/`native_decide`) are described in one sentence each (what set is enumerated, what is checked). Target: 12–15 pages of main text + 2–5 pages of appendix.
5. **No fabricated references.** Bibliography entries only for sources you can identify precisely: Sharipov arXiv:1108.5348 and arXiv:1201.1229; Asiryan arXiv:2601.04240 and arXiv:2601.04241; Asiryan–Rathbun arXiv:2601.07899; Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106; Capell's criterion — cite only if you can identify the exact source, otherwise attribute the idea as "classical" and prove it in full (Lean does). mathlib: cite the repository at the pinned revision from `lean/lakefile.toml`.
6. Do not commit or push. Leave the result in the working tree.

## Read first (in this order)

1. `paper/REWRITE_PLAN.md` — the chapter plan. Follow its structure and page budget exactly.
2. `paper/lean_route/01_linear_quartic.md`, `02_quadratic_cubic_front.md`, `03_gaussian_descent.md`, `04_gaussian_local_37.md`, `05_five_five_and_shell.md` — file-by-file digests of the Lean proof with all formulas and Lean theorem names. These are your primary source. When a digest and a Lean file disagree, the Lean file wins; check the Lean source for every formula you print.
3. `lean/Cuboid2/Main.lean`, `lean/FORMALIZATION_STATUS.md`, `lean/README.md` — the public theorem and the trust model.
4. `paper/clean3.tex` — the OLD paper. Reuse only its LaTeX preamble style and the statement of the polynomial. Its proofs of the 1+4, 2+3-core and 5+5 cases are NOT what Lean proves and must not be carried over (see REWRITE_PLAN.md §2 for the list of what to drop).

## Deliverables

- `paper/sharipov.tex` — the new article (single file, `article` class, `amsthm`, a `\leanref{name}` macro that typesets the Lean theorem name in small monospace, `thebibliography` inline). Chapters as in REWRITE_PLAN.md §1: Introduction; Reduction to three factorization types; No rational root (1+4); Quadratic factor I: reduction to the octic curve; Quadratic factor II: rational points on r²=4u⁸−8u²+5; Symmetric 5+5 case; Proof of the main theorem and the Lean formalization; Appendix A (paper statement ↔ Lean theorem ↔ file table); Appendix B (one-line summary per finite certificate, plus the single printed table of the 22 λ-adic descent obstructions).
- `paper/sharipov.pdf` — compiled with `pdflatex` twice (or `latexmk -pdf`), zero errors, no undefined references, no overfull boxes wider than 10pt in displayed math.
- Move `paper/main.tex`, `clean.tex`, `clean2.tex`, `clean3.tex` to `paper/archive/`.
- Update `README.md` "Start here" to point at `paper/sharipov.tex` instead of `clean3.tex`; update `HANDOFF.md` and `STATUS.md` only where they say `clean3.tex` is the recommended proof (one-line edits, do not rewrite these files).

## Working method

- Write chapters in this order: 2, 3, 6, 4, 5, 1, 7, appendices (easy elementary chapters first, the Gaussian core last, the introduction when you know what you are introducing).
- For each chapter, before writing, open the relevant Lean files and confirm every formula you intend to print by reading the Lean definition (e.g. `grep -n "def reciprocalQuotientC8" -A 12`). Print formulas exactly as Lean defines them, after converting to standard notation.
- Use subagents (with `model: "opus"`) in parallel for independent verification tasks: e.g. one agent extracts and double-checks all printed polynomials of Chapter 4 against the Lean sources; another builds the Appendix A table by grepping every `\leanref{}` in the draft and confirming each name exists in `lean/Cuboid2/` with `grep -rn "theorem <name>\|def <name>"`. Do not delegate the writing of mathematical prose to subagents; write it yourself.
- Two signs must never be conflated in Chapter 4: the "physical sign" ε in b = εd² (constant of the quadratic factor) and the valuation sign in k = 2εu², h = εv². Use different letters (σ for the physical sign, ε for the valuation sign).
- Chapter 5: both embeddings ℚ(i)→ℚ₃₇ (i ↦ 6 and i ↦ 31) are essential twice (paired abscissae, and the 17 ≠ 19 separation); the visible point P=(2,2) is NOT assumed to generate — saturation at 2, 3, 7, 37 is part of the proof; there is no p-adic elliptic logarithm, the argument is the norm inequality on the formal parameter t = −x/y. Do not "simplify" this into a Chabauty-style statement that Lean does not prove.
- Chapter 6: the first-contact lemma needs strict positivity of the sample fibre, and the critical identity carries (s−1)^10, so s = 1 is a cut with samples 4/5 and 2 on either side. Say this.
- Do not use D₊: R² = 4a⁵−8a²+5a anywhere; in Lean it is only an interface equivalent to the octic curve.

## Final checks before you stop

1. `cd paper && pdflatex -interaction=nonstopmode sharipov.tex && pdflatex -interaction=nonstopmode sharipov.tex` — exit 0; grep the log for `Undefined`, `Error`, `Overfull`.
2. Every `\leanref{name}` resolves: script it — extract all names, `grep -rn` each in `lean/Cuboid2/`, report any miss, fix.
3. Every theorem/lemma/proposition environment has at least one `\leanref{}`.
4. Page count of main text (before appendices) between 12 and 16.
5. `git status` shows changes only under `paper/`, `README.md`, `HANDOFF.md`, `STATUS.md`.
6. Final message: page count, list of chapters with their Lean anchors, anything you could not verify, and the exact commands you ran.
