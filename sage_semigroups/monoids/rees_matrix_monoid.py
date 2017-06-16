r"""
Rees Matrix Monoids

::

    sage: import sage_semigroups
    Loading sage-semigroups and patching its features into Sage's library: ...
"""
#*****************************************************************************
#  Copyright (C) 2009-2010 Florent Hivert <florent.hivert at univ-rouen.fr>
#                2009-2017 Nicolas M. Thiery <nthiery at users.sf.net>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************

from copy import copy
from sage.categories.monoids import Monoids
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.parent import Parent
from sage.structure.element_wrapper import ElementWrapper
from sage.sets.family import Family
from sage.rings.integer import Integer

class AperiodicReesMatrixMonoid(UniqueRepresentation, Parent):
    """
    INPUT:

     - ``P`` -- an `n\times m` matrix with `0`/`1` coefficients

    This construct the aperiodic Rees matrix monoid with (transpose)
    sandwich matrix given by mat. Setting `I=\{0,\dots,n\}` and
    `J=\{0,\dots,m\}`, this is the monoid on `I\times J\cup\{0,1\}`
    with product rule given by `(i,j) (i',j') = P[i,j] (i,j')`
    (plus the usual rule for `0` and `1`).

    If all rows and column of `P` contain at least one `1`, then the
    obtained monoid is regular.

    EXAMPLES::

        sage: from sage_semigroups.monoids.rees_matrix_monoid import AperiodicReesMatrixMonoid
        sage: P = matrix([[0,0,0,0,1],[0,1,1,0,0],[1,0,0,1,0],[1,0,0,0,1]]); P
        [0 0 0 0 1]
        [0 1 1 0 0]
        [1 0 0 1 0]
        [1 0 0 0 1]
        sage: M = AperiodicReesMatrixMonoid(P)
        sage: M.cardinality()
        22
        sage: M.list()
        [0,
         (0, 0), (0, 1), (0, 2), (0, 3), (0, 4),
         (1, 0), (1, 1), (1, 2), (1, 3), (1, 4),
         (2, 0), (2, 1), (2, 2), (2, 3), (2, 4),
         (3, 0), (3, 1), (3, 2), (3, 3), (3, 4),
         1]


    A regular Rees matrix monoid has exactly three `J`-classes, which
    are regular::

        sage: M.j_classes()
        [[0],
         [(1, 3), (3, 0), (2, 1), (0, 3), (1, 2),
          (3, 3), (2, 2), (1, 1), (3, 2), (0, 0),
          (0, 4), (1, 4), (2, 3), (1, 0), (0, 1),
          (3, 1), (0, 2), (2, 0), (3, 4), (2, 4)],
         [1]]

    Used to be:

        Family ({1},
                {(0, 1), (3, 2), (1, 3), (3, 0), (0, 4), (2, 1), (0, 0), (2, 3), (1, 4), (0, 3), (1, 0), (1, 2), (0, 2), (3, 3), (3, 1), (1, 1), (2, 0), (2, 2), (3, 4), (2, 4)},
                {0})

    The eggbox picture for the middle `J`-class is `P`, if one labels
    appropriately the rows and columns::

        sage: M.eggbox_picture(1)        # known to fail currently
        [1 0 0 1 0]
        [1 0 0 0 1]
        [0 1 1 0 0]
        [0 0 0 1 0]

    TESTS::

        sage: M.category()
        Category of finitely generated finite enumerated aperiodic monoids
        sage: TestSuite(M).run()
    """
    @staticmethod
    def __classcall__(cls, mat):
        mat = copy(mat)
        mat.set_immutable()
        return super(AperiodicReesMatrixMonoid, cls).__classcall__(cls, mat)

    def __init__(self, mat):
        """
        TESTS::

            sage: from sage_semigroups.monoids.rees_matrix_monoid import AperiodicReesMatrixMonoid
            sage: M = AperiodicReesMatrixMonoid(matrix(3,3,1))
            sage: TestSuite(M).run()
        """
        self._m = mat.nrows()
        self._n = mat.ncols()
        self._mat = mat
        Parent.__init__(self, category=Monoids().Aperiodic().Finite().FinitelyGenerated())

    def cardinality(self):
        return Integer(2 + self._m * self._n)

    def semigroup_generators(self):
        return Family(self.list())

    def __iter__(self):
        yield self.zero()
        for i in range(self._m):
            for j in range(self._n):
                yield self._element_constructor_((i,j))
        yield self.one()

    def one(self):
        return  self._element_constructor_(True)

    def zero(self):
        return  self._element_constructor_(False)

    def product(self, x, y):
        r"""
        The product of this semigroup, as per
        :meth:`Semigroups.ParentMethods.product`.

        EXAMPLES::

            sage: from sage_semigroups.monoids.rees_matrix_monoid import AperiodicReesMatrixMonoid
            sage: P = matrix([[0,0,0,0,1],[0,1,1,0,0],[1,0,0,1,0],[1,0,0,0,1]]); P
            [0 0 0 0 1]
            [0 1 1 0 0]
            [1 0 0 1 0]
            [1 0 0 0 1]
            sage: M = AperiodicReesMatrixMonoid(P)

            sage: P[2,3]
            1
            sage: M((1,3)) * M((2,4))   # indirect doctest
            (1, 4)

            sage: P[1,4]
            0
            sage: M((2,4)) * M((1,3))
            0

            sage: M.one() * M.one()
            1
            sage: M((1,3)) * M.zero()
            0
            sage: M((1,3)) * M.one()
            (1, 3)
        """
        if x.is_zero() or y.is_zero():
            return self.zero()
        if x.is_one(): return y
        if y.is_one(): return x
        (i,k) = x.value
        (l,j) = y.value
        if self._mat[l,k]:
            return self._element_constructor_((i,j))
        else:
            return self.zero()

    class Element(ElementWrapper):

        def is_zero(self):
            return self.value is False

        def is_one(self):
            return self.value is True

        def _repr_(self):
            if self.value is True:
                return "1"
            if self.value is False:
                return "0"
            else:
                return repr(self.value)
