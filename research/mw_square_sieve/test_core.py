from research.mw_square_sieve.core import (
    CongruenceSet,
    generalized_crt_pair,
    intersect_congruences,
)


def test_generalized_crt_pair_coprime_and_noncoprime() -> None:
    assert generalized_crt_pair(1, 4, 3, 6) == (9, 12)
    assert generalized_crt_pair(1, 4, 2, 6) is None
    assert generalized_crt_pair(-1, 5, 1, 3) == (4, 15)


def test_intersection_is_exact() -> None:
    current = CongruenceSet(4, frozenset({0, 1}))
    result = intersect_congruences(current, 6, {1, 3})
    assert result.modulus == 12
    assert result.residues == frozenset({1, 9})
    for integer in range(-100, 101):
        expected = integer % 4 in {0, 1} and integer % 6 in {1, 3}
        assert (integer % result.modulus in result.residues) == expected


def test_empty_is_absorbing() -> None:
    result = intersect_congruences(CongruenceSet.empty(7), 10, {1, 3})
    assert result.modulus == 70
    assert not result.residues


def test_guard_never_truncates_silently() -> None:
    try:
        intersect_congruences(
            CongruenceSet.all_integers(), 10, range(10), max_survivors=3
        )
    except OverflowError as error:
        assert "exceeded 3" in str(error)
    else:
        raise AssertionError("the exact survivor guard did not fire")


def test_all_small_intersections_against_brute_force() -> None:
    for first_modulus in range(1, 10):
        for second_modulus in range(1, 10):
            first = {value for value in range(first_modulus) if value % 3 != 2}
            second = {value for value in range(second_modulus) if value % 2 == 1}
            result = intersect_congruences(
                CongruenceSet(first_modulus, frozenset(first)),
                second_modulus,
                second,
            )
            for integer in range(2 * result.modulus):
                expected = (
                    integer % first_modulus in first
                    and integer % second_modulus in second
                )
                assert (integer % result.modulus in result.residues) == expected
