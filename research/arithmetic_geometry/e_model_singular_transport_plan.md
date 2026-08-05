# Singular normalization-to-Weierstrass transport

Status: **INPUT PREPARED, NOT EXECUTED**.

This route avoids `FunctionField.maximal_order()`.  It is deliberately split
between a Singular projective-divisor computation and Sage's exact smooth
plane-cubic constructor.

## Why `norid,normap` alone are not a projective certificate

For the ordinary total-degree projective closure of `H(q,A)`, the degree-18
part is

```text
361*Q^8*B^10.
```

Thus the line at infinity meets the plane model at both `[1:0:0]` and
`[0:1:0]`, with nontrivial branch multiplicities.  The ring `Ri/norid`
returned by `normal.lib` for the affine `(q,A)` chart normalizes only that
affine chart.  Homogenizing `norid` is not, without a new smoothness or
normality check at infinity, the normalization of the complete curve.

The safe use of the affine normalization is therefore as an independent
function-field cross-check through `normap`, not as an assumed projective
completion.  The optional combined Singular input does precisely that and
keeps the projective boundary explicit.

## Exact projective route

Let `P=[6:6/7:1]`.  The generated Singular program checks `H(P)=0` and that
one of the three projective partial derivatives is nonzero at `P`.  It then
uses `brillnoether.lib::RiemannRochBN` on the original singular plane model.
That procedure explicitly supports a singular *plane* curve: internally it
uses the Gorenstein adjoint ideal before computing the divisor space.

The checks are:

1. `dim L(2P)=2` and `dim L(3P)=3`.
2. The three common numerators returned for `L(3P)` define the complete
   linear-system map `phi : C --> P^2`.
3. `paraplanecurves.lib::invertBirMap(phi,C)` returns the image ideal and a
   homogeneous inverse `psi=[Q:B:Z]`.
4. The image ideal is principal of degree three.
5. Both projective compositions are reduced to zero modulo the source and
   target ideals.
6. The source and inverse base loci and the divisor `psi[3]=0` are emitted
   exactly and are required to be projectively finite.  The affine formulas
   are only

   ```text
   q = psi[1]/psi[3],   A = psi[2]/psi[3]
   ```

   away from that recorded divisor.
7. In the optional combined run, the same formulas are substituted through
   `normal.lib`'s `normap` and reduced modulo `norid`.

The Sage stage verifies that the degree-three image is geometrically smooth;
hence its geometric genus is `(3-1)(3-2)/2=1`.  It then calls
`EllipticCurve_from_cubic(..., morphism=True)`, composes the inverse cubic map
with the Singular map, and preserves the common affine denominator.

Relevant primary software documentation/source:

- [Singular `normal`](https://www.singular.uni-kl.de/Manual/4-4/sing_1470.htm)
- [Singular `brillnoether.lib` source](https://github.com/Singular/Singular/blob/f8e2789a17d3566f0ba24ff39046c81f5bd5f617/Singular/LIB/brillnoether.lib)
- [Singular `invertBirMap`](https://www.singular.uni-kl.de/Manual/4-4/sing_1734.htm)
- [Sage `EllipticCurve_from_cubic`](https://doc.sagemath.org/html/en/reference/arithmetic_curves/sage/schemes/elliptic_curves/constructor.html#sage.schemes.elliptic_curves.constructor.EllipticCurve_from_cubic)

## Frozen inputs and exact commands

Fast projective route:

```bash
python research/arithmetic_geometry/e_model_singular_rr_cubic.py \
  --output research/arithmetic_geometry/e_model_singular_rr_cubic.sing \
  --metadata research/arithmetic_geometry/e_model_singular_rr_cubic_input.json
Singular --random=1 -q \
  research/arithmetic_geometry/e_model_singular_rr_cubic.sing \
  | tee certificates/e_model_singular_rr_cubic.log
sage -python \
  research/arithmetic_geometry/e_model_sage_from_singular_cubic.py \
  --transcript certificates/e_model_singular_rr_cubic.log \
  --output certificates/e_model_singular_cubic_certificate.json
```

Combined run with the independent affine `norid,normap` round trip:

```bash
python research/arithmetic_geometry/e_model_singular_rr_cubic.py \
  --include-affine-normalization-cross-check \
  --output research/arithmetic_geometry/e_model_singular_normal_rr_cubic.sing \
  --metadata research/arithmetic_geometry/e_model_singular_normal_rr_cubic_input.json
Singular --random=1 -q \
  research/arithmetic_geometry/e_model_singular_normal_rr_cubic.sing \
  | tee certificates/e_model_singular_normal_rr_cubic.log
sage -python \
  research/arithmetic_geometry/e_model_sage_from_singular_cubic.py \
  --transcript certificates/e_model_singular_normal_rr_cubic.log \
  --output certificates/e_model_singular_normal_cubic_certificate.json
```

Frozen SHA-256 values are stored in the two `*_input.json` files.  Until a
Singular transcript reaches `CERT singular_rr_cubic_finished=OK` and the Sage
consumer exits successfully, no normalization, cubic, Weierstrass, or
transport claim should be promoted.

Even after that success, the saturated exceptional ideals in the transcript
must be split into closed points and matched with normalization branches before
using the transport for a *global* rational-point classification.  The two
composition checks certify the dense-open birational correspondence; they do
not silently assign values at a rational-map base locus.
