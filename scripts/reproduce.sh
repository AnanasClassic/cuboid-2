#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"

# Several exact certificates share frozen polynomial definitions through the
# repository namespace.  Make direct script execution behave the same way as
# pytest and `python -m`, including in a clean checkout.
export PYTHONPATH="${repo_dir}${PYTHONPATH:+:${PYTHONPATH}}"

python_bin="${PYTHON_BIN:-python3}"

# SymPy 1.14 may auto-select python-flint when it is present in the host
# environment.  Its nmod elements are intentionally unordered, while SymPy's
# factor-list canonicalizer still sorts them.  Pin the pure-Python ground type
# before any interpreter starts so reproduction is backend-independent.
export SYMPY_GROUND_TYPES="${SYMPY_GROUND_TYPES:-python}"

"$python_bin" src/symbolic_reduction.py --export artifacts/polynomials.json
"$python_bin" research/symbolic_algebra/derive_quadratic_reduction.py \
  --output artifacts/quadratic_reduction_independent.json
"$python_bin" src/geometry_audit.py
"$python_bin" research/symbolic_algebra/independent_sieve_check.py
"$python_bin" src/modular_sieve.py \
  --primes 41 71 83 97 101 113 137 \
  --output certificates/modular_sieve_7primes.json
"$python_bin" src/modular_sieve.py \
  --scan-through 97 \
  --output certificates/modular_sieve_primes_le_97.json
"$python_bin" src/signed_square_sieve.py \
  --scan-through 137 \
  --output certificates/signed_square_sieve_primes_le_137.json
"$python_bin" research/symbolic_algebra/independent_signed_sieve_check.py
"$python_bin" research/symbolic_algebra/reciprocal_square_quotient.py \
  --output artifacts/reciprocal_square_quotient.json
"$python_bin" research/symbolic_algebra/reciprocal_b_quotient.py \
  --output artifacts/reciprocal_b_quotient.json
"$python_bin" research/arithmetic_geometry/reciprocal_b_branch_audit.py \
  --output artifacts/reciprocal_b_branch_audit.json
"$python_bin" research/arithmetic_geometry/new_three_square_character_covers.py \
  --output research/arithmetic_geometry/new_three_square_character_covers.json
"$python_bin" research/arithmetic_geometry/character_kummer_obstruction.py \
  --output research/arithmetic_geometry/character_kummer_obstruction.json
"$python_bin" research/arithmetic_geometry/derive_genus4_quotient.py
"$python_bin" research/arithmetic_geometry/e_model_dihedral_descent.py
"$python_bin" research/quotient_transport/derive_invariant_compact_v.py
"$python_bin" research/quotient_transport/classify_transport_exceptions.py
"$python_bin" research/global_descent/inert_prime_power_family.py
"$python_bin" research/global_descent/new_local_A_B_audit.py
"$python_bin" research/global_descent/new_two_prime_family.py
"$python_bin" research/global_descent/new_inert_pair_endpoint.py
"$python_bin" research/global_descent/second_endpoint_layer.py
"$python_bin" research/compact_signed_square/compact_signed_square.py \
  --output research/compact_signed_square/compact_signed_square.json
"$python_bin" research/compact_signed_square/reciprocal_quotient/derive.py \
  --output research/compact_signed_square/reciprocal_quotient/reciprocal_quotient.json
"$python_bin" research/arithmetic_geometry/low_degree_transport.py \
  --output research/arithmetic_geometry/low_degree_transport.json
"$python_bin" research/arithmetic_geometry/product_character_simplification.py \
  --output research/arithmetic_geometry/product_character_simplification.json
"$python_bin" research/arithmetic_geometry/product_squareclass_valuation.py \
  --output research/arithmetic_geometry/product_squareclass_valuation.json
"$python_bin" research/arithmetic_geometry/product_genus2_two_descent.py \
  --output research/arithmetic_geometry/product_genus2_two_descent.json
"$python_bin" research/arithmetic_geometry/product_genus2_square_sieve.py \
  --output research/arithmetic_geometry/product_genus2_square_sieve.json
"$python_bin" research/arithmetic_geometry/product_genus2_p7_formal_log.py \
  --output research/arithmetic_geometry/product_genus2_p7_formal_log.json
"$python_bin" research/compact_signed_square/independent_genus2_square_sieve.py \
  --output research/compact_signed_square/independent_genus2_square_sieve.json
"$python_bin" research/proof_simplification/c041_structure.py \
  --output research/proof_simplification/c041_structure.json
"$python_bin" research/frobenius_audit/frobenius_burnside.py
"$python_bin" research/frobenius_audit/candidate_544c_check.py
"$python_bin" research/frobenius_audit/candidate_544c_rank_descent.py
"$python_bin" research/arithmetic_geometry/e_model_candidate_544c.py
"$python_bin" research/arithmetic_geometry/e_model_plane_discriminant.py
"$python_bin" research/arithmetic_geometry/e_model_low_degree_no_go.py \
  --output research/arithmetic_geometry/e_model_low_degree_no_go.json
"$python_bin" research/linear_factor_completion/exact_prerequisites.py
"$python_bin" research/linear_factor_completion/two_descent_rank.py
"$python_bin" research/completion_redteam/q1_exception_certificate.py
"$python_bin" -m pytest -q
PYTHONPATH=research/completion_redteam \
  "$python_bin" -m pytest -q \
  research/completion_redteam/test_q1_exception_certificate.py
PYTHONPATH=research/mw_square_sieve \
  "$python_bin" -m pytest -q research/mw_square_sieve/test_core.py
