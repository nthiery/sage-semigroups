r"""
`sage-semigroups <https://github.com/nthiery/sage-semigroups>`_: A semigroup (representation) theory library for SageMath

Loading this module initializes the sage-semigroups library. Some of
the features are extensions of existing classes or modules of the Sage
library, and directly inserted (monkey patched) there::

    sage: import sage_semigroups
    Loading sage-semigroups and patching its features into Sage's library: ...

Others are added to the global namespace, like the new catalog of
semigroups::

    sage: semigroups
    <module 'sage_semigroups.monoids.catalog' from '...'>
    sage: semigroups.AperiodicReesMatrixMonoid
    <class 'sage_semigroups.monoids.rees_matrix_monoid.AperiodicReesMatrixMonoid'>


TESTS:

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
sage_semigroups = sys.modules[__name__]
import misc, categories, monoids
monkey_patch(sage_semigroups.misc, sage.misc, log_level=logging.INFO)
monkey_patch(sage_semigroups.categories, sage.categories, log_level=logging.INFO)
monkey_patch(sage_semigroups.monoids, sage.monoids, log_level=logging.INFO)

# Insert the content of sage_semigroups.all in the global name space
import all
from sage.repl.user_globals import initialize_globals
initialize_globals(sage_semigroups.all)

# Some traces of an attempt
from sage.repl.ipython_extension import SageCustomizations
all = SageCustomizations.all_globals()
all.foo = 3

"""
At this stage, the insertion in the global name space works in the
doctest where the library is imported, but is reinitialized in later
doctests::

    sage: semigroups
"""
