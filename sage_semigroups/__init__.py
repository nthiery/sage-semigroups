"""
Sage-Semigroups's initialization

Loading this module initializes the library by monkey patching its
features into the Sage library::

    sage: import sage_semigroups
    Loading sage-semigroups and patching its features into Sage's library:
    Monkey patching sage.categories.finite_semigroups.FiniteSemigroups.ParentMethods.is_r_trivial
    Monkey patching sage.categories.finite_semigroups.FiniteSemigroups.parent_class.is_r_trivial
    Monkey patching sage.categories.h_trivial_semigroups.HTrivialSemigroups.Finite
    Monkey patching sage.categories.h_trivial_semigroups.HTrivialSemigroups.Finite_extra_super_categories
    Monkey patching sage.categories.truc
    Monkey patching sage.monoids.catalog
    Monkey patching sage.monoids.rees_matrix_monoid

We test that the sage categories have been properly monkey patched::

    sage: Semigroups().Finite().parent_class.is_r_trivial
    <class 'sage_semigroups.misc.sage_unittest.IsMethod'>
    sage: Semigroups().Finite().parent_class.is_r_trivial.__module__
    'sage_semigroups.categories.finite_semigroups'
"""
import sys
import logging
from recursive_monkey_patch import monkey_patch

import sage
# TODO: do we want this? Should this list the features that are being patched?
print("Loading sage-semigroups and patching its features into Sage's library:")
monkey_patch(sys.modules[__name__], sage, log_level=logging.INFO)
