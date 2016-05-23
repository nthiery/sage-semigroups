"""
TESTS:

We test that the sage categories have been properly monkey patched.

    sage: import sage_semigroups
    sage: Semigroups().Finite().parent_class.is_r_trivial
    <unbound method FiniteSemigroups.parent_class.is_r_trivial>
    sage: Semigroups().Finite().parent_class.is_r_trivial.__module__
    'sage_semigroups.categories.finite_semigroups'
"""
from recursive_monkey_patch import monkey_patch
import sage_semigroups
import sage
print "Loading sage-semigroups and patching its features into Sage's library"
monkey_patch(sage_semigroups, sage)
