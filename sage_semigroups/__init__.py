"""
Sage-Semigroups's initialization

Loading this module initializes the library by monkey patching its
features into the Sage library::

    sage: import sage_semigroups

We test that the sage categories have been properly monkey patched::

    sage: Semigroups().Finite().parent_class.is_r_trivial
    <unbound method FiniteSemigroups.parent_class.is_r_trivial>
    sage: Semigroups().Finite().parent_class.is_r_trivial.__module__
    'sage_semigroups.categories.finite_semigroups'
"""
from recursive_monkey_patch import monkey_patch
import sage_semigroups
import sage
# TODO: do we want this? Should this list the features that are being patched?
print "Loading sage-semigroups and patching its features into Sage's library"
monkey_patch(sage_semigroups, sage)
