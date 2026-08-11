# Completion red-team certificates

`q1_exception_certificate.py` closes the denominator-zero branch of the
linear-subresultant inverse used to reconstruct `B`.  It constructs
`F_T(T,A)=G(T^2,A)` and `Q1(T,A)` from the canonical genus-four artifact,
factors `Res_A(F_T,Q1)` exactly, and multiplies the factorization back.

The only rational roots are `T=-1,0,1`, corresponding respectively to
`z=0`, `s=1`, and the `z=infinity` boundary.  Hence `Q1` cannot vanish for an
admissible rational-square cuboid parameter.

Reproduce with:

```bash
.venv/bin/python research/completion_redteam/q1_exception_certificate.py
PYTHONPATH=research/completion_redteam \
  .venv/bin/python -m pytest -q \
  research/completion_redteam/test_q1_exception_certificate.py
```
