"""Pure-Python exact congruence core for the Mordell--Weil sieve.

The arithmetic-geometry driver is a Sage script, but the logical heart of the
finite sieve is deliberately kept independent of Sage.  A global integer
``n`` surviving conditions modulo ``m_i`` must lie in the generalized-CRT
intersection computed here.  Empty output is therefore an exhaustive finite
certificate, while nonempty output is only a residual congruence set.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd, lcm
from typing import Iterable


@dataclass(frozen=True)
class CongruenceSet:
    """A finite union of residue classes modulo ``modulus``."""

    modulus: int
    residues: frozenset[int]

    def __post_init__(self) -> None:
        if self.modulus <= 0:
            raise ValueError("modulus must be positive")
        normalized = frozenset(int(value) % self.modulus for value in self.residues)
        object.__setattr__(self, "residues", normalized)

    @classmethod
    def all_integers(cls) -> "CongruenceSet":
        return cls(1, frozenset({0}))

    @classmethod
    def empty(cls, modulus: int = 1) -> "CongruenceSet":
        return cls(modulus, frozenset())


def generalized_crt_pair(r: int, modulus_r: int, a: int, modulus_a: int) -> tuple[int, int] | None:
    """Combine two possibly non-coprime congruences exactly.

    Return ``(value, lcm(modulus_r, modulus_a))`` or ``None`` when the two
    congruences are incompatible.
    """

    if modulus_r <= 0 or modulus_a <= 0:
        raise ValueError("CRT moduli must be positive")
    r %= modulus_r
    a %= modulus_a
    common = gcd(modulus_r, modulus_a)
    difference = a - r
    if difference % common:
        return None
    reduced_a = modulus_a // common
    if reduced_a == 1:
        k = 0
    else:
        inverse = pow(modulus_r // common, -1, reduced_a)
        k = (difference // common * inverse) % reduced_a
    combined_modulus = lcm(modulus_r, modulus_a)
    return (r + modulus_r * k) % combined_modulus, combined_modulus


def intersect_congruences(
    current: CongruenceSet,
    condition_modulus: int,
    allowed_residues: Iterable[int],
    *,
    max_survivors: int | None = None,
) -> CongruenceSet:
    """Intersect a congruence union with a new periodic condition.

    ``max_survivors`` is a computational guard only.  Hitting it raises an
    exception; it never returns a truncated set that could be mistaken for a
    proof certificate.
    """

    if condition_modulus <= 0:
        raise ValueError("condition modulus must be positive")
    allowed = frozenset(int(value) % condition_modulus for value in allowed_residues)
    target_modulus = lcm(current.modulus, condition_modulus)
    if not current.residues or not allowed:
        return CongruenceSet.empty(target_modulus)

    common = gcd(current.modulus, condition_modulus)
    buckets: dict[int, list[int]] = {}
    for value in allowed:
        buckets.setdefault(value % common, []).append(value)

    survivors: set[int] = set()
    for residue in current.residues:
        for allowed_residue in buckets.get(residue % common, ()):
            answer = generalized_crt_pair(
                residue, current.modulus, allowed_residue, condition_modulus
            )
            if answer is None:  # Defensive; the bucket already checked compatibility.
                continue
            value, modulus = answer
            if modulus != target_modulus:
                raise AssertionError("generalized CRT returned the wrong modulus")
            survivors.add(value)
            if max_survivors is not None and len(survivors) > max_survivors:
                raise OverflowError(
                    f"exact CRT intersection exceeded {max_survivors} survivors"
                )
    return CongruenceSet(target_modulus, frozenset(survivors))
