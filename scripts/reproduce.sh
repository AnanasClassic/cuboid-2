#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"

python_bin="${PYTHON_BIN:-python3}"

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
"$python_bin" -m pytest -q
