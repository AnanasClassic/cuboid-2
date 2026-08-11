from research.linear_factor_completion import exact_prerequisites
from research.linear_factor_completion import two_descent_rank


def test_linear_factor_exact_prerequisites():
    # The routine intentionally proves only the exact algebraic and local
    # prerequisites.  Its final printed premise, rank J_C(Q) <= 1, is closed
    # by the separate certified 2-descent test below.
    exact_prerequisites.main()


def test_linear_factor_certified_two_descent():
    two_descent_rank.main()
