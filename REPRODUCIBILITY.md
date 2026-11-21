# Replaying the historical formalization

The reference revision is `9b0e8517e00609ec364cef3860b0962d6ac5f568`. The final paper revision is `d162753f5bd41a21131a5ff9c6bea09ab7dbc9c0`. At both revisions the Git tree of `lean/` is `26d2f1b36ff28017a54c229affcf9b3c1b17b643`. The reproduction script and Lean workflow blobs are respectively `1b6b36dc5134480e488dc29c21f4e894a2b1b5fa` and `709ae7a6f3607bc3b2a4f439ea582fa76f7624f2`.

Install [elan](https://github.com/leanprover/elan) and Git. Use a new checkout. For the preserved private copy, substitute the local bundle path for the GitHub URL. Historical GitHub links require access to the repository while it is private.

```bash
git clone https://github.com/AnanasClassic/cuboid-2.git cuboid-replay
cd cuboid-replay
git checkout --detach 9b0e8517e00609ec364cef3860b0962d6ac5f568
test -z "$(git status --porcelain)"
test ! -e lean/.lake
(
  cd lean
  lean --version
  lake --version
  lake exe cache get
)
unset CUBOID_SKIP_BUILD LAKE_BIN LEAN_PATH
export LEAN_NUM_THREADS=0
bash scripts/reproduce_lean.sh complete
```

Lean is pinned to `v4.33.0`, compiler commit `d8b18978322de05a8f3dba51ef03cf5461676c17`, with Lake `5.0.0-src+d8b1897`. The pinned mathlib commit is `db584cd6d46c92f209a44c0f1c829460d327499d`. Keep `lean/lake-manifest.json` to resolve all nine package revisions. `lake exe cache get` obtains ordinary upstream dependency binaries, as in CI. Preserve the initial empty project build directory to ensure every project proof on the verification path is re-elaborated. The worker setting matches the low-memory historical CI job. A full replay requires network access to acquire the toolchain, dependencies and upstream cache, plus local storage and running time.

To compile every tracked Lean module, including research modules outside the default library root, run the additional command below from the repository root. These targets have a distinct status from the default public theorem and its dependency closure.

```bash
(
  cd lean
  git ls-files -- '*.lean' | sed -e 's/\.lean$//' -e 's|/|.|g' -e 's/^/+/' | xargs lake build
)
```

The proof uses three foundational axioms and generated closed native computation certificates. In the pinned Lean implementation, each native certificate adds an axiom of the form `decide P = true` after compilation and evaluation. The runtime, compiler and supplied arithmetic implementations participate in this step. The default strict script prints the transitive axioms of the final theorem and rejects unexpected names, project-specific declarations and placeholders. Inspect the actual axiom names and the code in `Cuboid2/Main.lean`, `Cuboid2/Polynomial.lean`, and `Cuboid2/AxiomAudit.lean` when interpreting the result. A successful exit and the final strict-audit message certify completion of the replay under this trust model.

[Historical GitHub Actions run](https://github.com/AnanasClassic/cuboid-2/actions/runs/33671888493) · [Historical Lean sources](https://github.com/AnanasClassic/cuboid-2/tree/9b0e8517e00609ec364cef3860b0962d6ac5f568/lean) · [Pinned mathlib](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d) · [Native evaluation implementation](https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/Lean/Meta/Native.lean)

## Independent replay on 21 November 2026

A new arm64 macOS checkout of the signed CI commit ran the full script with an initially empty project build directory, the pinned compiler and the official mathlib dependency cache. It started at 01:32:44 UTC and finished at 02:51:36 UTC with exit status 0. Lake reported 8,833 tasks. This run used two task workers. The transitive axiom names of the main theorem matched the September CI list exactly.

A second Lean probe checked the public type over ℤ[X], its degree 10, and the actual types of the generated axioms. The quadratic-factor proof uses all 174 closed native computation axioms. The linear-factor and symmetric-factor proofs each use only the three foundational axioms. To repeat this probe, use its absolute file path from this release with `lake env lean /absolute/path/to/IndependentAudit.lean` inside the built historical checkout's `lean/` directory. [Probe source](evidence/IndependentAudit.lean) · [Recorded result](evidence/verification-record.json)

After the strict replay, Lake built all 145 tracked Lean modules at the same commit, including the 18 outside the default target. The explicit build exited successfully (8,850 Lake tasks), and all 145 project module files had compiled outputs. The public theorem’s project import closure contains 112 modules.

The compiled tables for the 145 project modules contain 8,534 declarations, including 218 generated native computation axioms. The inspector found zero other axiom declarations and zero explicit kernel opaque declarations in those tables. After building all modules, repeat the module-level inspection with `lake env lean /absolute/path/to/ModuleDeclarations.lean` from the same directory. [Module inspector](evidence/ModuleDeclarations.lean)
