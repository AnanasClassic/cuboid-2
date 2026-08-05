"""Deterministic exact-arithmetic backend for the regression suite.

SymPy 1.14 can auto-select python-flint when it is installed.  Its ``nmod``
elements are deliberately unordered, but SymPy's finite-field factor-list
canonicalizer still attempts to sort them.  Select SymPy's pure-Python exact
ground types before any test module imports SymPy.  ``scripts/reproduce.sh``
sets the same variable for standalone certificate drivers.
"""

from __future__ import annotations

import os


os.environ.setdefault("SYMPY_GROUND_TYPES", "python")
