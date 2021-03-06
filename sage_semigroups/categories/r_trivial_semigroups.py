r"""
R-Trivial semigroups
"""
#*****************************************************************************
#  Copyright (C) 2009-2010 Florent Hivert <florent.hivert at univ-rouen.fr>
#                2009-2017 Nicolas M. Thiery <nthiery at users.sf.net>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************

from sage.misc.misc import attrcall
from sage.misc.sage_unittest import _test_method_from_is
from sage.categories.category_with_axiom import CategoryWithAxiom
from sage.categories.semigroups import Semigroups

import sage_semigroups

class RTrivialSemigroups:
    def example(self, alphabet=('a','b','c')):
        """
        Returns an example of (finite) right trivial semigroup

        .. SEEALSO:: :meth:`Category.example`

        EXAMPLES::

            sage: S = Semigroups().RTrivial().example(); S
            An example of a finite semigroup: the left regular band generated by ('a', 'b', 'c', 'd')
            sage: S.category()
            Category of finite r trivial semigroups
        """
        from sage.categories.examples.finite_semigroups import LeftRegularBand
        return LeftRegularBand(alphabet=alphabet,
                               category=Semigroups().RTrivial().Finite().FinitelyGenerated())

    class Finite(CategoryWithAxiom):

        class ParentMethods:

            _test_r_trivial = _test_method_from_is(sage_semigroups.categories.finite_semigroups.FiniteSemigroups.ParentMethods.is_r_trivial)

            def index_of_regular_j_class(self, idempotent):
                """
                Returns the index that should be used for an idempotent in the transversal

                In this implementation, each idempotent e is indexed
                by the subset of the indices `i` of the generators
                `s_i` such that `es_i=e` (that is `s_1` acts by `1` on
                the corresponding simple module).

                .. SEEALSO:: :meth:`FiniteSemigroups.ParentMethods.j_transversal_of_idempotents`

                EXAMPLES::

                    sage: S = Semigroups().RTrivial().example(alphabet=('a','b','c')); S
                    An example of a finite semigroup: the left regular band generated by ('a', 'b', 'c')
                    sage: S.category()
                    Category of finite r trivial monoids
                    sage: a,b,c = S.semigroup_generators()
                    sage: S. index_of_regular_j_class(a*c)
                    (0, 2)

                This is used to index the transversal of idempotents::

                    sage: sorted(S.j_transversal_of_idempotents().keys())
                    [(0,), (0, 1), (0, 1, 2), (0, 2), (1,), (1, 2), (2,)]

                """
                s = self.semigroup_generators()
                return tuple(i for i in s.keys() if idempotent * s[i] == idempotent)
