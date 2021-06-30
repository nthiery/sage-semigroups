"""
This is a completely experimental file ! use at your own risks !!!

::

    sage: import sage_semigroups # random
"""

import operator
from sage.misc.cachefunc import cached_method
from sage.monoids.automatic_semigroup import AutomaticMonoid
from sage.sets.family import Family
from sage.sets.finite_set_maps import FiniteSetMaps

from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.element import Element as Element_sage
from sage.categories.monoids import Monoids
from sage.categories.semigroups import Semigroups

from sage.calculus.var import var

from sage.sets.finite_set_maps import FiniteSetEndoMaps_N, FiniteSetEndoMaps_Set
from sage.sets.finite_set_map_cy import FiniteSetEndoMap_N, FiniteSetEndoMap_Set


#######################################################################
# Monoid of standard (type A) 0-Hecke


class HeckeMonoid(AutomaticMonoid):
    """
    The 0-Hecke monoid of a Coxeter group

    EXAMPLES::

        sage: from sage.monoids.j_trivial_monoids import *
        sage: H = HeckeMonoid(['A',3])
        sage: pi = H.semigroup_generators(); pi
        sage: pi
        Finite family {1: [1], 2: [2], 3: [3]}
        sage: H.cardinality()
        24
        sage: TestSuite(H).run()
    """

    @staticmethod
    def __classcall__(cls, W):
        """
        EXAMPLES::

            sage: from sage.monoids.j_trivial_monoids import *
            sage: HeckeMonoid(['A',3]).cardinality()
            24
        """
        from sage.categories.coxeter_groups import CoxeterGroups
        if W not in CoxeterGroups():
            from sage.combinat.root_system.weyl_group import WeylGroup
            W = WeylGroup(W)  # CoxeterGroup(W)
        return super(PiMonoid, cls).__classcall__(cls, W)

    def __init__(self, W):
        self.lattice = W.domain()
        self.W = W
        from sage.sets.finite_set_maps import FiniteSetMaps
        ambient_monoid = FiniteSetMaps(self.W, action="right")
        pi = self.W.simple_projections(length_increasing=True).map(ambient_monoid)
        category = Monoids().JTrivial().Finite() & Monoids().Transformation().Subobjects()
        AutomaticMonoid.__init__(self, pi, ambient_monoid,
                                 one=ambient_monoid.one(), mul=operator.mul,
                                 category=category)
        self.domain = self.W
        self.codomain = self.W
        # This would requires add_cache-nt.patch from the Sage-Combinat queue
        # self.cache_element_methods(["rank"])

    def quiver_index_iterator(self):
        """
        EXAMPLES::

            sage: from sage.monoids.j_trivial_monoids import *
            sage: HeckeMonoid(WeylGroup(["A",2])).quiver_index()
            [({1}, {2}), ({2}, {1})]
            sage: HeckeMonoid(WeylGroup(["A",3])).quiver_index()
            [({1}, {2}), ({2}, {1}), ({2}, {3}), ({2}, {1, 3}), ({3}, {2}), ({1, 3}, {2}), ({1, 2}, {1, 3}), ({1, 3}, {1, 2}), ({1, 3}, {2, 3}), ({2, 3}, {1, 3})]

        They are indeed all distinct::

            sage: len(set(HeckeMonoid(WeylGroup(["A",3])).quiver_index()))
            10
        """
        from sage.sets.set import Set
        S = Set(self.W.index_set())
        pi = self.semigroup_generators()
        for size_A in range(len(S) - 1):
            for A in S.subsets(size=size_A):
                SminusA = S.difference(A)
                for J in SminusA.subsets():
                    if J.cardinality() == 0:
                        continue
                    SminusAJ = SminusA.difference(J)
                    for K in SminusAJ.subsets():
                        if K.cardinality() == 0:
                            continue
                        if any(pi[j] * pi[k] == pi[k] * pi[j]
                               for j in J for k in K):
                            continue
                        yield A.union(J), A.union(K)

    def quiver_index(self):
        """
        EXAMPLES::

            sage: quiver(WeylGroup(["A",2]))
            [({1}, {2}), ({2}, {1})]
            sage: quiver(WeylGroup(["A",3]))
            [({1}, {2}), ({2}, {1}), ({2}, {3}), ({2}, {1, 3}), ({3}, {2}), ({1, 3}, {2}), ({2}, {3}), ({3}, {2}), ({1}, {2}), ({2}, {1})]
            sage: [ len(quiver_index(WeylGroup(["A",n])))/2 for n in range(1,8) ]
            [0, 1, 5, 16, 44, 112, 272]
        """
        return list(self.quiver_index_iterator())

    def quiver_element(self, JK):
        """
        EXAMPLES::

            sage: from sage.monoids.j_trivial_monoids import *
            sage: H = HeckeMonoid(['A',3])
            sage: H.cardinality()
            sage: H.quiver_element(([1,2],[1,3]))
        """
        J, K = JK
        pi = self.semigroup_generators()
        piJ = self.prod(pi[j] for j in J).pow_omega()
        piK = self.prod(pi[k] for k in K).pow_omega()
        return piJ * piK

    def quiver_elements(self):
        """
            sage: from sage.monoids.j_trivial_monoids import *
            sage: H = HeckeMonoid(['A',3])
            sage: H.cardinality()
            sage: H.quiver_elements()
        """
        return Family(self.quiver_index(), self.quiver_element)

    def _repr_(self):
        return "zero_hecke monoid for type %s" % self.W.cartan_type()


PiMonoid = HeckeMonoid

#######################################################################
# Monoid of standard (type A) NDPF


class NDPFMonoid(AutomaticMonoid):
    """
    EXAMPLES::

        sage: from sage.monoids.j_trivial_monoids import *
        sage: p = NDPFMonoid(3)
        sage: TestSuite(p).run()
    """
    def __init__(self, n, action="right"):
        ambient_monoid = FiniteSetMaps(range(1, n + 1), action=action)

        def pii(i):
            return ambient_monoid.from_dict({j: j - 1 if j == i + 1 else j
                                             for j in range(1, n + 1)})
        pi = Family(range(1, n), pii)
        category = Monoids().JTrivial().Finite() & Monoids().Transformation().Subobjects()
        AutomaticMonoid.__init__(self, pi, ambient_monoid,
                                 one=ambient_monoid.one(), mul=operator.mul,
                                 category=category)

    def _repr_(self):
        return "The monoid of Non Decreasing Parking Functions on %s" % self.domain()

#######################################################################
# Monoid of type B NDPF


class NDPFMonoidB(AutomaticMonoid):
    """
    EXAMPLES::

        sage: from sage.monoids.j_trivial_monoids import *
        sage: p = NDPFMonoidB(3)
        sage: TestSuite(p).run()
    """
    def __init__(self, n):
        ambient_monoid = FiniteSetMaps(list(range(-n, 0)) +
                                       list(range(1, n + 1)),
                                       action="right")
        pi = Family(range(1, n),
                    lambda j: ambient_monoid.from_dict(dict(
                        [(i, i) for i in range(1, n + 1) if i != j + 1] +
                        [(j + 1, j)] +
                        [(i, i) for i in range(-n, 0) if i != -j] +
                        [(-j, -j - 1)])))
        category = Monoids().JTrivial().Finite() & Monoids().Transformation().Subobjects()
        AutomaticMonoid.__init__(self, pi, ambient_monoid,
                                 one=ambient_monoid.one(), mul=operator.mul,
                                 category=category)


##########################################################################
# Monoid of contracting function of a poset !
# Beware not always j-trivial
class ContractingMonoidPoset(AutomaticMonoid):
    """
    EXAMPLES::

        sage: from sage.monoids.j_trivial_monoids import *
        sage: p = ContractingMonoidPoset(Posets.IntegerPartitions(4))
        sage: TestSuite(p).run()
        Failure in _test_j_trivial:
        ...
        AssertionError: Non trivial j class: ...
        ------------------------------------------------------------
        The following tests failed: _test_j_trivial
    """
    def __init__(self, poset):
        self.poset = poset
        support = poset.list()
        ambient_monoid = FiniteSetMaps(support, action="right")

        def genij(ij):
            (i, j) = ij
            return ambient_monoid.from_dict({k: i if k == j else k
                                             for k in support})
        index = map(tuple, poset.cover_relations())  # index elems must be hashable
        self.pi = Family(index, genij)
        category = Monoids().JTrivial().Finite() & Monoids().Transformation().Subobjects()
        AutomaticMonoid.__init__(self, self.pi, ambient_monoid,
                                 one=ambient_monoid.one(), mul=operator.mul,
                                 category=category)

    class Element(AutomaticMonoid.Element):

        def is_weakly_increasing(self):
            poset = self.parent().poset
            return all(poset.is_lequal(self(i), self(j))
                       for (i, j) in poset.cover_relations())

##########################################################################
# Monoid of NDPF of a poset !

# TODO: make this into just a function?


class NDPFMonoidPoset(AutomaticMonoid):
    """
    EXAMPLES::

        sage: from sage.monoids.j_trivial_monoids import *
        sage: M = NDPFMonoidPoset(Posets.IntegerPartitions(4))
        sage: M
        NDPF monoid of Poset ([[(4,), (3, 1)], [(4,), (2, 2)], [(3, 1), (2, 1, 1)], [(2, 2), (2, 1, 1)], [(2, 1, 1), (1, 1, 1, 1)]])
        sage: M._test_j_trivial()
        sage: time M.quiver().graphviz_to_file_named("quivers/bla.dot") # not tested
        sage: os.system("/usr/bin/dot -Tpdf -o quivers/bla.pdf quivers/bla.dot") # not tested
    """
    def __init__(self, poset):
        ambient_monoid = ContractingMonoidPoset(poset)
        self._poset = poset
        gens = Family([p for p in ambient_monoid if p.is_weakly_increasing()])
        category = Monoids().JTrivial().Finite() & Monoids().Transformation().Subobjects()
        AutomaticMonoid.__init__(self, gens, ambient_monoid,
                                 one=ambient_monoid.one(), mul=operator.mul,
                                 category=category)

        self.rename("NDPF monoid of Poset (%s)" % (self._poset.cover_relations()))

##########################################################################
# Compatible semi-group associated to the monoid of NDPF of a poset !


def compatible_semi_group(poset):
    M = NDPFMonoidPoset(poset)
    return CompatibleSemiGroup(M)

##########################################################################
# Compatible semi-group associated to a j-trivial monoid.
# WARNING : This is not always a semi-group


class CompatibleSemiGroup(UniqueRepresentation, Parent):
    """
    sage: from sage.monoids.j_trivial_monoids import *
    sage: MC = compatible_semi_group(Posets.IntegerPartitions(4))
    sage: TestSuite(MC).run()
    sage: MC.zero()
    0
    sage: MC._test_associativity()

    sage: for p in Posets(3):
    ...    print p.cover_relations()
    ...    compatible_semi_group(p)._test_associativity()
    []
    [[1, 2]]
    [[0, 1], [0, 2]]
    [[0, 1], [1, 2]]
    [[0, 2], [1, 2]]

    """
    def __init__(self, jmonoid):
        assert (jmonoid in Monoids().JTrivial().Finite())
        self.jmonoid = jmonoid
        Parent.__init__(self, category=Semigroups().Finite())

    def zero(self):
        return self._element_constructor_(None)

    def __contains__(self, x):
        return x.parent() is self

    @cached_method
    def product(self, xm, ym):
        assert(xm in self)
        assert(ym in self)
        if xm.is_zero() or ym.is_zero():
            return self.zero()
        x = xm.lift()
        y = ym.lift()
        if x.symbol("right") == y.symbol("left"):
            xy = x * y
            if (x.symbol("left") == xy.symbol("left") and
                    y.symbol("right") == xy.symbol("right")):
                return self._element_constructor_(xy)
        return self.zero()

    def _repr_(self):
        return "The compatible monoid associated with %s" % (self.jmonoid)

    def an_element(self):
        return self._element_constructor_(self.jmonoid.an_element())

    def __iter__(self):
        yield self.zero()
        for x in self.jmonoid:
            yield self._element_constructor_(x)

    def _element_constructor_(self, x):
        return self.element_class(self, x)

    class Element(Element_sage):  # UniqueRepresentation
        # The extra zero element is represented by None.
        def __init__(self, parent, ambient_element=None):
            Element_sage.__init__(self, parent)
            self.ambient_element = ambient_element

        def lift(self):
            if self.is_zero():
                raise ValueError("Zero cannot be lifted")
            return self.ambient_element

        def is_zero(self):
            return self.ambient_element is None

        def _repr_(self):
            if self.is_zero():
                return "0"
            return "%s" % (self.ambient_element)

##########################################################################
# Idempotent generated sub-monoid of a monoid


def IdempotentGeneratedSubMonoid(monoid):
    category = Monoids().JTrivial().Finite()
    assert monoid in category  # Should be generalized!
    if monoid in Monoids().Transformation().Subobjects():
        category = category & Monoids().Transformation().Subobjects()
    return monoid.submonoid(monoid.idempotents(),
                            category=category)


def check_conj_q_matrix(M):
    """
    sage: from sage.monoids.j_trivial_monoids import *
    sage: for p in Posets(3):
    ...       check_conj_q_matrix(NDPFMonoidPoset(p))
    ([1], 1, 1)
    (
    [1 0]
    [0 1], 2, 2
    )
    (
    [1 0 0 0]
    [0 1 0 0]
    [0 0 1 0]
    [0 0 0 1], 4, 4
    )
    (
    [1 0 0 0]
    [0 1 q 0]
    [0 0 1 0]
    [0 0 0 1], q + 4, q + 4
    )
    ([1], 1, 1)
    """
    msage = M.cartan_matrix(var('q'))
    rsage = sum(sum(msage))
    mmup = M.cartan_matrix_mupad(var('q'))
    rmup = sum(sum(mmup))
    assert (rmup == rsage), "Conjecture False "
    return msage, rsage, rmup


#######################################################################
# NDPF monoid of a poset, fast version


class NDPFMonoidPosetNew(FiniteSetEndoMaps_N):
    """
    ..warning: The poset is supposed to be supported by range(n)

    EXAMPLES::

        sage: from sage.monoids.j_trivial_monoids import *
        sage: P = Posets(3)[3]
        sage: M = NDPFMonoidPosetNew(P)
        sage: M.cardinality()
        5
        sage: TestSuite(M).run()
    """
    def __init__(self, poset):
        Parent.__init__(self, category=Monoids().JTrivial().Finite())
        self._m = len(poset)
        self._n = len(poset)
        self._action = "right"
        self._poset = poset
        self._size = 0

    def _repr_(self):
        return "NDPF of Poset %s" % (self._poset.cover_relations())

    def cardinality(self):
        return self._cardinality_from_iterator()

    def an_element(self):
        """
        sage: F = FiniteSetMaps(4)
        sage: F.an_element()
        [3, 2, 1, 0]
        """
        return self.one()

    @cached_method
    def list(self):
        return list(self._iter_())

    def __iter__(self):
        return iter(self.list())

    def _iter_(self):
        """
        sage: from sage.monoids.j_trivial_monoids import *
        sage: P = Posets(4)[14]
        sage: M = NDPFMonoidPosetNew(P)
        sage: M.cardinality()
        14
        sage: TestSuite(M).run()

        sage: P = Posets(4)[0]
        sage: M = NDPFMonoidPosetNew(P)
        sage: M.cardinality()
        1
        sage: TestSuite(M).run()

        sage: for p in Posets(4):
        ...      print NDPFMonoidPoset(p).cardinality(), NDPFMonoidPosetNew(p).cardinality()
        1 1
        2 2
        4 4
        8 8
        10 10
        9 9
        5 5
        13 13
        1 1
        2 2
        1 1
        4 4
        2 2
        1 1
        14 14
        2 2

        sage: P = Posets(5)[42]
        sage: %time M = NDPFMonoidPosetNew(P)
        sage: %time M.cardinality()
        28
        sage: TestSuite(M).run()
        """
        poset = self._poset
        p2int = poset._element_to_vertex
        int2p = poset._vertex_to_element
        linext = poset.linear_extension()
        stack = [[poset.minimal_elements()[0]]]
        res = self.one().__copy__()
        while len(stack) > 0:
            try:
                image = stack[-1].pop(0)
            except IndexError:
                stack.pop()
            else:
                i = len(stack)
                res[p2int(linext[i - 1])] = p2int(image)
                if i == len(linext):
                    res2 = res.__copy__()
                    res2.set_immutable()
                    self._size += 1
                    if self._size % 100 == 0:
                        print("Size ... %i ..." % (self._size))
                    yield res2
                else:
                    el = linext[i]
                    lst = [im for im in poset.principal_order_ideal(el)
                           if all(poset.is_lequal(int2p(res[p2int(pred)]), im)
                                  for pred in poset.lower_covers_iterator(el))]
                    stack.append(lst)

    def check_element(self, el):
        """
        Check that an element belongs to self.

        INPUT:

        - ``el`` : an instance of ``self.element_class``

        OUTPUT:

        ``None`` : an exception is raised if ``el`` is incorrect.

        EXAMPLES::

            sage: from sage.monoids.j_trivial_monoids import *
            sage: M = NDPFMonoidPosetNew(Posets(4)[14])
            sage: for x in M: x.check()
            sage: M([0, 1, 2, 2])
            [0, 1, 2, 2]
            sage: M([0, 1, 2, 1])
            Traceback (most recent call last):
            ...
            AssertionError: [0, 1, 2, 1] is not nondecreasing
            sage: M([0, 2, 2, 2])
            Traceback (most recent call last):
            ...
            AssertionError: [0, 2, 2, 2] is not regressive
            sage: M([0, 2, 2])
            Traceback (most recent call last):
            ...
            AssertionError: Wrong number of values

        TESTS::

            sage: NDPFMonoidPosetNew(Posets.AntichainPoset(3))([0,1,2])
            [0, 1, 2]
        """
        poset = self._poset
        p2int = poset._element_to_vertex
        int2p = poset._vertex_to_element
        for i in range(len(el)):
            assert int2p(el[i]) <= int2p(i), "%s is not regressive" % el
            for pred in poset.lower_covers_iterator(int2p(i)):
                assert int2p(el[p2int(pred)]) <= int2p(el[i]), "%s is not nondecreasing" % el

    Element = FiniteSetEndoMap_N


class NDPFMonoidPosetNewSet(FiniteSetEndoMaps_Set):
    """
    EXAMPLES::

        sage: from sage.monoids.j_trivial_monoids import *
        sage: P = Posets(3)[3]
        sage: M = NDPFMonoidPosetNewSet(P)
        sage: M.cardinality()
        5
        sage: TestSuite(M).run()
    """
    def __init__(self, poset):
        FiniteSetEndoMaps_Set.__init__(self, poset, action="right",
                                       category=Monoids().JTrivial().Finite())
        self._poset = poset
        self._size = 0

    def _repr_(self):
        return "NDPF of Poset %s" % (self._poset.cover_relations())

    def cardinality(self):
        return self._cardinality_from_iterator()

    def an_element(self):
        """
        sage: from sage.monoids.j_trivial_monoids import *
        sage: P = Posets(3)[3]
        sage: M = NDPFMonoidPosetNewSet(P)
        sage: M.an_element()
        map: 0 -> 0, 1 -> 1, 2 -> 2
        """
        return self.one()

    @cached_method
    def list(self):
        return list(self._iter_())

    def __iter__(self):
        return iter(self.list())

    def _iter_(self):
        """
        sage: from sage.monoids.j_trivial_monoids import *
        sage: P = Posets(4)[14]
        sage: M = NDPFMonoidPosetNewSet(P)
        sage: M.cardinality()
        14
        sage: TestSuite(M).run()

        sage: P = Posets(4)[0]
        sage: M = NDPFMonoidPosetNewSet(P)
        sage: M.cardinality()
        1
        sage: TestSuite(M).run()

        sage: for p in Posets(4):
        ...      print NDPFMonoidPoset(p).cardinality(), NDPFMonoidPosetNewSet(p).cardinality()

        sage: P = Posets(5)[42]
        sage: %time M = NDPFMonoidPosetNewSet(P)
        sage: %time M.cardinality()
        28
        sage: TestSuite(M).run()
        """
        poset = self._poset
        linext = poset.linear_extension()
        stack = [[poset.minimal_elements()[0]]]
        res = self.one().__copy__()
        while len(stack) > 0:
            try:
                image = stack[-1].pop(0)
            except IndexError:
                stack.pop()
            else:
                i = len(stack)
                res.setimage(linext[i - 1], image)
                if i == len(linext):
                    res2 = res.__copy__()
                    res2.set_immutable()
                    self._size += 1
                    if self._size % 100 == 0:
                        print("Size ... %i ..." % (self._size))
                    yield res2
                else:
                    el = linext[i]
                    lst = [im for im in poset.principal_order_ideal(el)
                           if all(poset.is_lequal(res(pred), im)
                                  for pred in poset.lower_covers_iterator(el))]
                    stack.append(lst)

    def check_element(self, el):
        """
        Check that an element belongs to self.

        INPUT:

        - ``el`` : an instance of ``self.element_class``

        OUTPUT:

        ``None`` : an exception is raised if ``el`` is incorrect.

        EXAMPLES::

            sage: from sage.monoids.j_trivial_monoids import *
            sage: M = NDPFMonoidPosetNewSet(Posets(4)[14])
            sage: for x in M: x.check()
            sage: M([0, 1, 2, 2])
            [0, 1, 2, 2]
            sage: M([0, 1, 2, 1])
            Traceback (most recent call last):
            ...
            AssertionError: [0, 1, 2, 1] is not nondecreasing
            sage: M([0, 2, 2, 2])
            Traceback (most recent call last):
            ...
            AssertionError: [0, 2, 2, 2] is not regressive
            sage: M([0, 2, 2])
            Traceback (most recent call last):
            ...
            AssertionError: Wrong number of values

        TESTS::

            sage: NDPFMonoidPosetNewSet(Posets.AntichainPoset(3))([0,1,2])
            [0, 1, 2]
        """
        poset = self._poset
        for i in poset:
            assert el(i) <= i, "%s is not regressive" % el
            for pred in poset.lower_covers_iterator(i):
                assert el(pred) <= el(i), "%s is not nondecreasing" % el

    Element = FiniteSetEndoMap_Set


"""
TIMING comparison::

sage: sage: P = Posets.ChainPoset(5)

sage: from sage.monoids.j_trivial_monoids import *
sage: sage: M = NDPFMonoidPosetNew(P)
sage: sage: MS = NDPFMonoidPosetNewSet(P)
sage: M
NDPF of Poset [[0, 1], [1, 2], [2, 3], [3, 4]]
sage: MS
NDPF of Poset [[0, 1], [1, 2], [2, 3], [3, 4]]

sage: %time TestSuite(M).run(verbose=True)    # not tested
sage: %time TestSuite(MS).run(verbose=True)   # not tested
"""
