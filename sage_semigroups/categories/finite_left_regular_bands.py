r"""
Categories for finite left regular bands

EXAMPLES::

    sage: import sage_semigroups
    Loading sage-semigroups and patching its features into Sage's library: ...

"""

from sage.categories.category import Category
from sage.categories.algebra_functor import AlgebrasCategory
from sage.categories.monoids import Monoids
from sage.misc.cachefunc import cached_method, cached_function
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.parent import Parent
from sage.structure.element_wrapper import ElementWrapper
from sage.sets.set import Set
from sage.rings.rational_field import QQ

class FiniteLeftRegularBands(Category):
    @cached_method
    def super_categories(self):
        # TODO: generalize, we should allow LRB semigroups as well
        # from sage.categories.semigroups import Semigroups
        # return [Semigroups().HTrivial().Finite()]
        return [Monoids().HTrivial().Finite()]

    class ParentMethods:
        def __iter__(self):
            from sage.combinat.backtrack import TransitiveIdeal
            return TransitiveIdeal(self.succ_generators(side = "right"), [self.one()]).__iter__()

        @cached_method
        def succ_generators(self, side="right"):
            r"""
            Returns a function that takes an element of the semigroup and
            returns the list of elements obtained by multiplying it on the
            given side by the generators of the semigroup.
            """
            def m(x):
                return [(x * y if self=='right' else y * x) for y in self.semigroup_generators()]
            return m

        @cached_method
        def j_poset(self):
            from sage.combinat.posets.posets import Poset
            cmp = lambda X, Y : self.j_lequal(X[0], Y[0])
            return Poset((map(Set, self.j_classes()), cmp), facade=True)

        def j_lequal(self, x, y):
            return bool(x * y == x)

        def support_lattice(self):
            from sage.combinat.posets.lattices import LatticePoset
            return LatticePoset(self.j_poset())

        def minimal_ideal(self):
            return self.support_lattice().bottom()

        def interval(self, x, jclass):
            return tuple([z for z in self if x*z == z and self.j_lequal(jclass[0],z)])

        def restriction(self, jclass):
            # EXPERIMENTAL!
            return subsemigroup(self, self.interval(self.one(),jclass))
            #return self.subquotient(self.interval(self.one(),jclass),
            #        category = self.category().Subquotients())

        @cached_method
        def r_poset(self):
            from sage.combinat.posets.posets import Poset
            return Poset((self, self.r_lequal), facade=True)

        def r_lequal(self, x, y):
            return bool(y*x == x)

        def faces_of(self, x):
            r"""
            The set of faces of `x`. This is an upper order filter in
            the `R`-poset.
            """
            return self.r_poset().principal_order_filter(x)

        def _test_idempotents(self, **options):
            tester = self._tester(**options)
            tester.assertTrue(all(x * x == x for x in self),
                    "not all elements of self are idempotent")

        def _test_left_regularity(self, **options):
            tester = self._tester(**options)
            tester.assertTrue(all(x * y * x == x * y for x in self
                                                     for y in self),
                                  "semigroup does not satisfy xyx=xy")

        def is_geometric(self):
            r"""
            A left regular band is **geometric** if the right stabilizers of
            all its elements are commutative.
            """
            # TODO: could be more efficient
            for x in self:
                stab = [y for y in self if y*x == x]
                if any(a*b != b*a for a in stab for b in stab):
                    return False
            return True

        # BHR random walk methods
        def transition_matrix(self, distribution):
            r"""
            EXAMPLES::

                sage: from sage_semigroups.monoids.free_left_regular_band import FreeLeftRegularBand
                sage: F = FreeLeftRegularBand(('a', 'b', 'c')); F
                Free left regular band generated by ('a', 'b', 'c')
                sage: dist = dict((a,1) for a in F.semigroup_generators())
                sage: sorted(dist.items())
                [('a', 1), ('b', 1), ('c', 1)]
                sage: T = F.transition_matrix(dist)
                sage: T
                [1 0 1 0 1 0]
                [0 1 1 0 1 0]
                [1 0 1 0 0 1]
                [1 0 0 1 0 1]
                [0 1 0 1 1 0]
                [0 1 0 1 0 1]
                sage: T * T.transpose()
                [3 2 2 1 1 0]
                [2 3 1 0 2 1]
                [2 1 3 2 0 1]
                [1 0 2 3 1 2]
                [1 2 0 1 3 2]
                [0 1 1 2 2 3]

            """
            from sage.modules.free_module_element import vector
            from sage.matrix.constructor import matrix
            C = sorted(self.minimal_ideal())
            R = vector(distribution.values()).base_ring()
            T = matrix(R, len(C))
            for (i,c) in enumerate(C):
                for (j,d) in enumerate(C):
                    T[i,j] = sum(distribution[x] for x in distribution if x*c == d)
            return T

        def eigenvalues(self, distribution):
            evalues = {}
            L = self.support_lattice()
            for X in L:
                evalues[X] = 0
                for Y in L.principal_order_filter(X):
                    evalues[X] += sum(distribution.get(y, 0) for y in Y)
            return evalues

        def stationary_distribution(self, distribution):
            r"""
            Return the stationary distribution of the random walk, as a
            dictionary keyed by the set compositions that are the chambers.

            EXAMPLES::

                sage: from sage_semigroups.monoids.free_left_regular_band import FreeLeftRegularBand
                sage: F = FreeLeftRegularBand(('a', 'b', 'c'))
                sage: dist = dict((a,1) for a in F.semigroup_generators())
                sage: sorted(F.stationary_distribution(dist).items())
                [('abc', 1/6), ('acb', 1/6), ('bac', 1/6), ('bca', 1/6), ('cab', 1/6), ('cba', 1/6)]

            """
            from sage.symbolic.ring import SR
            eig = sum(distribution.values())
            T = self.transition_matrix(distribution)
            K = (T - eig * T.parent().one()).left_kernel()
            basis = K.basis_matrix()
            if basis.is_zero():
                u = K([1]*K.degree())
            elif basis.nrows() > 1:
                u = sum(basis)
            else:
                u = basis[0]
            u = 1/sum(u) * u
            if u.base_ring() == SR:
                from sage.arith.misc import factor
                u = map(factor, u)
            return dict(zip(self.minimal_ideal(), u))

        def restricted_stationary_distributions(self, distribution, ring=QQ):
            A = self.algebra(ring)
            stat_dists = {}
            for X in self.support_lattice():
                resX = self.restriction(X)
                res_dist = {}
                for x in distribution:
                    y = resX.retract(x)
                    if y is not None:
                        res_dist[y] = distribution[x]
                sdX = resX.stationary_distribution(res_dist)
                stat_dists[X] = A.sum_of_terms((resX.lift(x),sdX[x]) for x in sdX)
            return stat_dists

        def restricted_distribution(self, X, distribution):
            resX = self.restriction(X)
            res_dist = {}
            for x in distribution:
                y = resX.retract(x)
                if y is not None:
                    res_dist[y] = distribution[x]
            return res_dist

        def restricted_distributions(self, distribution):
            #res_dists = {}
            #for X in self.support_lattice():
            #    resX = self.restriction(X)
            #    res_dist = {}
            #    for x in distribution:
            #        y = resX.retract(x)
            #        if y is not None:
            #            res_dist[y] = distribution[x]
            #    res_dists[X] = res_dist
            #return res_dists

            res_dists = {}
            for X in self.support_lattice():
                res_dists[X] = self.restricted_distribution(X, distribution)
            return res_dists

        def idempotent_decomposition(self, distribution, ring=QQ):
            r"""

            EXAMPLES::

                sage: from sage_semigroups.monoids.free_left_regular_band import FreeLeftRegularBand
                sage: F = FreeLeftRegularBand(('a', 'b'))
                sage: dist = dict((a,1) for a in F.semigroup_generators())
                sage: F.idempotent_decomposition(dist)
                {{''}: B[''] - B['a'] + 1/2*B['ab'] - B['b'] + 1/2*B['ba'],
                 {'a'}: B['a'] - B['ab'],
                 {'b'}: B['b'] - B['ba'],
                 {'ab', 'ba'}: 1/2*B['ab'] + 1/2*B['ba']}

            The (unsigned) Eulerian idempotents are obtained from the
            probability distribution on set compositions that assigns the
            weight `\binom(n,i)` to the set compositions with i blocks::

                sage: from sage_semigroups.monoids.set_compositions_monoid import SetCompositionsMonoid
                sage: n = 3
                sage: S = SetCompositionsMonoid(n)
                sage: dist = dict( (I, binomial(n, len(I.value))) for I in S )
                sage: e = S.idempotent_decomposition(dist)
                sage: e == S.algebra(QQ).primitive_orthogonal_idempotents("all")
                True

            """
            stat_dists = self.restricted_stationary_distributions(distribution, ring=ring)
            A = self.algebra(ring)
            return A.primitive_orthogonal_idempotents(stat_dists.__getitem__)

        # bilinear forms
        @cached_method
        def directed_faces(self):
            return [(x, c) for c in self.minimal_ideal() for x in self.faces_of(c)]
            #return [(x, c) for x in self for c in self.minimal_ideal() if x * c == c]

        def bilinear_form_on_directed_faces(self):
            directed_faces = self.directed_faces()
            IndexSet = dict((xc, i) for (i, xc) in enumerate(directed_faces))
            m = {}
            for (x, c) in directed_faces:
                for (y, d) in directed_faces:
                    if y * c == d and x * d == c:
                        m[IndexSet[x,c], IndexSet[y,d]] = 1
                    else:
                        m[IndexSet[x,c], IndexSet[y,d]] = 0
            from sage.matrix.all import matrix
            return matrix(QQ, m)

    class Algebras(AlgebrasCategory):
        class ParentMethods:
            @cached_method
            def product_on_basis(self, g1, g2):
                return self.monomial(g1*g2)

            def primitive_orthogonal_idempotents(self, jclassreps="simple"):
                r"""
                Return a complete system of primitive orthogonal idempotents
                for the left regular band algebra.

                INPUT:

                - ``jclassreps`` -- function or string (default: "simple).
                  The function must return a linear combination of elements in
                  a given J-class. The strings are shorthands for functions:
                  - "simple" -- returns a single element from each J-class;
                  - "all" -- normalized sum of all the elements of J-class.

                """
                e = {}
                S = self.basis().keys()
                L = S.support_lattice()
                if jclassreps == "simple":
                    jclassreps = self._j_class_representative_simple
                elif jclassreps == "all":
                    jclassreps = self._j_class_representative_all
                elif isinstance(jclassreps, tuple):
                    jclassreps = jclassreps.__getitem__
                for X in L.linear_extension():
                    x = jclassreps(X)
                    ideal = L.principal_order_ideal(X)
                    ideal.remove(X)
                    e[X] = x - x * self.sum(e[Y] for Y in ideal)
                return e

            def _j_class_representative_simple(self, X):
                r"""
                Helper function for :meth:`primitive_orthogonal_idempotents`:
                returns an element indexed by a single element from the J-class
                indexed by ``X`` of the underlying left regular band.
                """
                S = self.basis().keys()
                return self.basis()[S.j_class_representative(X)]

            def _j_class_representative_all(self, X):
                r"""
                Helper function for :meth:`primitive_orthogonal_idempotents`:
                returns the normalized sum of all the elements of the J-class
                indexed by ``X`` of the underlying left regular band.
                """
                R = self.base_ring()
                scalar = R(1) / R(len(X))
                return scalar * self.sum(self.basis()[x] for x in X)

##############################
#  HACK: Subsemigroup class  #
##############################
@cached_function
def subsemigroup(semigroup, subsemigroup_elements):
    class MyHackedSubSemigroupClass(UniqueRepresentation, Parent):
        def _element_constructor_(self, x):
            return self.retract(self.ambient()(x))

        def __init__(self, subsemigroup_elements, category = None):
            if category is None:
                category = semigroup.category().Subquotients()
            Parent.__init__(self, category = category)
            self._sselts = subsemigroup_elements

        def semigroup_generators(self):
            return [self.element_class(self, x) for x in self._sselts]

        def _repr_(self):
            return "subsemigroup of %s" % self.ambient()

        def ambient(self):
            return semigroup

        def lift(self, x):
            assert x in self
            return x.value

        def an_element(self):
            return self.semigroup_generators()[0]

        # HACK ... retract should return None if not possible
        def retract(self, x):
            assert x in self.ambient()
            y = self.element_class(self, x)
            if y not in self.semigroup_generators():
                return None
            else:
                return y

        class Element(ElementWrapper):
            pass

    return MyHackedSubSemigroupClass(subsemigroup_elements)

