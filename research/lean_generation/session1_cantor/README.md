# Session 1 specialized `D+` Cantor certificate

`generate_dplus_cantor.py` independently computes the exact rational chain

```text
D → 2D → 4D → 8D → 10D → 11D
```

on `R² = 4a⁵ - 8a² + 5a`, starting from
`D = [(1,1)-∞]`.  It uses only `fractions.Fraction` and its local
univariate-polynomial kernel.  Each addition must have coprime generalized
Cantor factor `d = 1`; every intermediate pair, exact quotient, Bézout
identity, composition congruence, and reduction identity is stored in
`dplus_cantor_trace.json`.

The source calculation is
`research/proof_simplification_2/c3_p3_chabauty.py::multiple_11D_data`.
That calculation uses the isomorphic monic model with ordinate `R/2`.
The final original-model coefficients agree exactly with the pinned
`dplusElevenDRaw` constants checked by
`Cuboid2.DPlus.GlobalMumfordCertificate`.  The comparison script also checks
the canonical checksum and identical `11D` metadata in the direct artifact
`research/proof_simplification_3/dplus_p3_square_abscissa.json`.

`Cuboid2.DPlus.CantorTrace` is generated from the same JSON.  Lean rechecks
all polynomial identities and makes the last reduction land on the existing
`dplusElevenD`; the public quotient-presentation endpoint is
`dplusCantorClass_eleven_generator`.

Regenerate with:

```sh
python3 research/lean_generation/session1_cantor/generate_dplus_cantor.py \
  --output research/lean_generation/session1_cantor/dplus_cantor_trace.json \
  --lean-output lean/Cuboid2/DPlus/CantorTrace.lean
```

Compare the result directly with the original SymPy calculation with:

```sh
python3 -B research/lean_generation/session1_cantor/verify_external_11d.py
```
