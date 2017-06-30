r"""
Example of finite h trivial monoids

EXAMPLES::

    sage: import sage_semigroups # random
    sage: Monoids().HTrivial().Finite().example()
    The finite H-trivial monoid of order preserving maps on {1, 2, 3}
"""
#*****************************************************************************
#  Copyright (C) 2011-2017 Nicolas M. Thiery <nthiery at users.sf.net>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************

import operator
from sage.categories.monoids import Monoids
from sage.sets.family import Family
from sage.rings.semirings.non_negative_integer_semiring import NN
from sage.monoids.automatic_semigroup import AutomaticMonoid
from sage.sets.finite_set_maps import FiniteSetMaps
from sage.sets.integer_range import IntegerRange
#from sage.combinat.j_trivial_monoids import SubFiniteMonoidsOfFunctions
from sage.rings.integer import Integer
##########################################################################

class MonoidOfOrderPreservingMaps(AutomaticMonoid):
    """
    Finite `H`-trivial monoid of order preserving maps

    INPUT:

     - ``n`` -- a non negative integer

    Constructs the finite `H`-trivial monoid of the maps f on the chain
    `\{1 < \cdots < n \}` such that `i\leq j \Right arrow f(i)\leq f(j)`.

    EXAMPLES::

        sage: P = Monoids().HTrivial().Finite().example(); P
        The finite H-trivial monoid of order preserving maps on {1, 2, 3}
        sage: P.monoid_generators()    # should be monoid_generators
        Finite family {1: 113, 2: 122, -2: 133, -1: 223}
        sage: TestSuite(P).run()
    """
    def __init__(self, n = 3, action="left"):
        r"""
        EXAMPLES::

            sage: from sage_semigroups.categories.examples.finite_h_trivial_monoids import MonoidOfOrderPreservingMaps
            sage: p = MonoidOfOrderPreservingMaps(4)
            sage: TestSuite(p).run()
        """
        assert n in NN
        domain    = IntegerRange(Integer(1),Integer(n+1))
        index_set = IntegerRange(Integer(1),Integer(n))
        ambient_monoid = FiniteSetMaps(domain, action=action)
        def pi(i):
            return ambient_monoid.from_dict(dict([(k, k) for k in domain if k != i+1]+[(i+1,i)]))
        def opi(i):
            return ambient_monoid.from_dict(dict([(k, k) for k in domain if k != i  ]+[(i,i+1)]))
        piopi = Family(dict([ [ i,  pi(i) ] for i in index_set] +
                            [ [-i, opi(i) ] for i in index_set]))

        AutomaticMonoid.__init__(self, piopi,
            ambient_monoid, one=ambient_monoid.one(), mul=operator.mul,
            category=Monoids().HTrivial().Finite().FinitelyGenerated() &
                     Monoids().Transformation().Subobjects()
            )

    def _repr_(self):
        r"""
        EXAMPLES::

            sage: Monoids().HTrivial().Finite().example()
            The finite H-trivial monoid of order preserving maps on {1, 2, 3}
        """
        return "The finite H-trivial monoid of order preserving maps on %s"%self.domain()

    class Element(AutomaticMonoid.Element):

        def _repr_(self):
            r"""
            EXAMPLES::

                sage: M = Monoids().HTrivial().Finite().example(); M
                The finite H-trivial monoid of order preserving maps on {1, 2, 3}
                sage: M.an_element()
                113
            """
            return ''.join(repr(self(i)) for i in self.codomain())

Example = MonoidOfOrderPreservingMaps
