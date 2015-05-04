"""
TESTS:

We test that the sage categories have been properly monkey patched.

    sage: Semigroups().Finite().parent_class.is_r_trivial
    <unbound method FiniteSemigroups.parent_class.is_r_trivial>
    sage: Semigroups().Finite().parent_class.is_r_trivial.__module__
    'sage_semigroups.categories.finite_semigroups'
"""

import sage_semigroups.categories.finite_semigroups

