# Literature audit (2026-08-04)

## Primary sources

- R. Sharipov, [Perfect cuboids and irreducible polynomials](https://arxiv.org/abs/1108.5348), v1, 2011.
- R. Sharipov, [A note on the second cuboid conjecture. Part I](https://arxiv.org/abs/1201.1229), v1, 2012.
- V. Asiryan, [Non-Existence of Quintic Factorization](https://arxiv.org/abs/2601.04240), v1, 2026.
- V. Asiryan, [Non-Existence of Linear--Quartic Factorization](https://arxiv.org/abs/2601.04241), current v2, 2026.
- V. Asiryan and R. L. Rathbun, [Computational Evidence Against Quadratic--Cubic Factorization](https://arxiv.org/abs/2601.07899), current v2, 2026.

No later second-cuboid follow-up or separate public code repository was found.
The executable material is embedded in the arXiv TeX appendices.

Current source-tarball SHA-256 values are:

```text
1108.5348   1c9cd4ed725c4550365a0d6c3a40aff042beb1d95d36e32d74fa7add8d490789
1201.1229   dd27faedb54ae6c67978a225b5c5e0af3309a3e0e01fa1fc297e4fa154c3d48c
2601.04240  96d7e4b7d3cb75af238a0ca8cd143a8d555daf6ac9e8c2cc94a099b5aea04760
2601.04241v2 fb2bd65e0667f3504e65ee5f0d461fa8180bf2e5a631d8665dd9efae90fc355b
2601.07899v2 404cef5ad9655f382cab2e1a6e8b16a47b24201bf3d6bafa8bdae4c0d17a6396
```

## Findings

Sharipov's 2011 paper formulates the second conjecture and checks bounded
instances; it does not prove irreducibility.  The 2012 Part I paper supplies
integer-root structure and special prime-parameter exclusions, not general
irreducibility.  Both distinguish the intermediate conjecture from the full
perfect-cuboid problem.

The 2026 `5+5` proof has no detected logical gap.  Symmetry is forced by UFD;
all divisions use `r!=0`; the resultant is only necessary, so spurious points
cannot invalidate the exclusion.  Its exact SymPy discriminant factorization,
rational-root checks, positive-root isolation, and seven Sturm counts were
replayed successfully under SymPy 1.14.0.

For `1+4`, all transformations, inversion identities, resultants,
parametrization, square conditions, and exceptional denominators were checked
exactly.  The final rational-point list depends on a Magma computation.  The
current Magma handbook states that `Chabauty(P)` saturates the subgroup and
returns all rational points in rank one, so the transcript is logically
appropriate; it was not independently rerun here.

For `2+3`, v1 searched through height `10^7`; current v2 changes this to
`10^9`, with the same eight reported points.  Search snippets quoting `10^7`
refer to v1.  The paper explicitly labels completeness as a conjecture.

Warning: arXiv's experimental HTML drops leading digits in several displayed
coefficients (`10` may appear as `0`, and `-14` as `-4`).  The TeX/PDF source,
not the HTML extraction, is authoritative.

