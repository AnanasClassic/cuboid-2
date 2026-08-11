from research.arithmetic_geometry.product_genus2_p7_formal_log import (
    verify as verify_formal_log,
)
from research.arithmetic_geometry.product_genus2_square_sieve import (
    verify as verify_sieve,
)
from research.compact_signed_square.independent_genus2_square_sieve import (
    verify as verify_independent,
)


def test_combined_square_abscissa_theorem_inputs_agree():
    sieve = verify_sieve()
    formal = verify_formal_log()
    independent = verify_independent()
    expected = [[0, 0], [0, 1], [1, 0], [20, 0]]
    assert sieve["compatible_classes_mod_7"] == expected
    assert independent["compatible_classes"] == expected
    assert formal["annihilator_nonzero_on_surviving_disks"] is True
    assert formal["surviving_disks"] == [
        "infinity",
        "(0,0)",
        "(1,1)",
        "(1,-1)",
    ]
