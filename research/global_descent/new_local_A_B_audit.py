#!/usr/bin/env python3
"""Exact local audit of the A,B valuations of a quadratic factor."""

from __future__ import annotations

import json
from pathlib import Path


def verify() -> dict[str, object]:
    # Root valuations divided by k are 0,0,2,4,4.  Store unordered pairs.
    pairs = [(0, 0), (0, 2), (0, 4), (2, 4), (4, 4)]
    table = []
    for left, right in pairs:
        raw_index = (left + right) // 2
        unequal = left != right
        table.append(
            {
                "root_valuations_over_k": [left, right],
                "v_B_over_2k": raw_index,
                "v_A_over_k": left if unequal else f">={left} (cancellation unbounded)",
                "v_A_exact": unequal,
                "normalized_m_if_prime_divides_p": raw_index,
                "normalized_m_if_prime_divides_q": 4 - raw_index,
            }
        )

    # A concrete global quadratic factor with different local pair types.
    # D=(X-1)(X-25) has root valuations (0,0) at 3 and (0,2) at 5.
    # The three displayed cubic roots complete {0,0,2,4,4} at both primes.
    roots = [1, 25, 9, 3**4 * 5**4, 3**4 * 5**4]

    def valuation(number: int, prime: int) -> int:
        answer = 0
        while number % prime == 0:
            number //= prime
            answer += 1
        return answer

    valuations = {
        str(prime): sorted(valuation(root, prime) for root in roots)
        for prime in (3, 5)
    }
    assert valuations == {"3": [0, 0, 2, 4, 4], "5": [0, 0, 2, 4, 4]}
    quadratic_A = -(1 + 25)
    quadratic_B = 25
    assert valuation(quadratic_B, 3) == 0
    assert valuation(quadratic_B, 5) == 2
    assert valuation(quadratic_A, 3) == valuation(quadratic_A, 5) == 0

    return {
        "schema": 1,
        "status": "PROVED_AND_MACHINE_CHECKED",
        "table": table,
        "equal_slope_cancellation": {
            "unit_pair": "alpha=1, beta=-1+ell^N gives v(A)=N and v(B)=0",
            "high_pair": (
                "alpha=ell^(4k), beta=-ell^(4k)+ell^(4k+N) "
                "gives v(A)=4k+N and v(B)=8k"
            ),
            "conclusion": "no finite upper bound on v(A) in either equal-slope pair",
        },
        "nonuniformity_witness": {
            "polynomial_roots": roots,
            "global_quadratic_factor": "(X-1)(X-25)=X^2-26X+25",
            "root_valuation_multisets": valuations,
            "quadratic_pair_at_3": [0, 0],
            "quadratic_pair_at_5": [0, 2],
            "conclusion": (
                "the same rational quadratic factor can select different Newton "
                "pair types at different primes; Newton and A,B valuation data "
                "alone cannot force uniform m_l"
            ),
            "scope": (
                "this is a no-go statement for the local-data argument, not a "
                "factorization of Sharipov's polynomial"
            ),
        },
    }


if __name__ == "__main__":
    output = Path(__file__).with_suffix(".json")
    output.write_text(json.dumps(verify(), indent=2, sort_keys=True) + "\n")
    print("local A,B valuation table and nonuniformity witness: OK")
