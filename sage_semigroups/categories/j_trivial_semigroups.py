r"""
J-trivial semigroups

Module merged in #18265.
"""

from sage.misc.lazy_import import LazyImport

class JTrivialSemigroups:
    Finite = LazyImport('sage_semigroups.categories.finite_j_trivial_semigroups', 'FiniteJTrivialSemigroups')
