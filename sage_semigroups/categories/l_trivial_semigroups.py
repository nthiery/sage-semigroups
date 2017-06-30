r"""
L-Trivial semigroups
"""
#*****************************************************************************
#  Copyright (C) 2009-2010 Florent Hivert <florent.hivert at univ-rouen.fr>
#                2009-2017 Nicolas M. Thiery <nthiery at users.sf.net>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************

from sage.categories.category_with_axiom import CategoryWithAxiom

class LTrivialSemigroups:

    class Finite(CategoryWithAxiom):

        class ParentMethods:

            def index_of_regular_j_class(self, idempotent):
                """
                Returns the index that should be used for an idempotent in the transversal

                In this implementation, each idempotent e is indexed
                by the subset of the indices `i` of the generators
                `s_i` such that `es_i=e` (that is `s_1` acts by `1` on
                the corresponding simple module).

                .. seealso:: :meth:`FiniteSemigroups.ParentMethods.j_transversal_of_idempotents`

                .. todo::

                    This is mostly a duplicate of
                    :meth:`RTrivialMonoids.Finite.ParentMethods.j_transversal_of_idempotents`

                    Instead this should be generalized to
                    DASemigroups.Finite, by testing if idempotent *
                    s[i] is in the same J-class. And recycled to build
                    the corresponding simple module.

                EXAMPLES::

                    TODO!
                """
                s = self.semigroup_generators()
                return tuple(i for i in s.keys() if s[i] * idempotent == idempotent)
