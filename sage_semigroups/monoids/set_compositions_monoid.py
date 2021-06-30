r"""
Monoid of set compositions

EXAMPLES::

    sage: import sage_semigroups
    Loading sage-semigroups and patching its features into Sage's library: ...

"""
from sage.combinat.partition import Partitions
from sage.combinat.permutation import Permutations
from sage.misc.cachefunc import cached_method
from sage.modules.free_module_element import vector
from sage.rings.rational_field import QQ
from sage.sets.set import Set
from sage.structure.element_wrapper import ElementWrapper
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation


class SetCompositionsMonoid(UniqueRepresentation, Parent):
    r"""
    EXAMPLES::

        sage: from sage_semigroups.monoids.set_compositions_monoid import SetCompositionsMonoid
        sage: [SetCompositionsMonoid(n).cardinality() for n in range(6)]
        [1, 1, 3, 13, 75, 541]

    """
    def __init__(self, underlyingset):
        from sage.rings.integer import Integer
        if isinstance(underlyingset, (int, Integer)):
            underlyingset = range(1, underlyingset + 1)
        self._underlying_set = Set(underlyingset)
        from sage_semigroups.categories.finite_left_regular_bands import FiniteLeftRegularBands
        Parent.__init__(self, category=FiniteLeftRegularBands().FinitelyGenerated())

    def underlying_set(self):
        return self._underlying_set

    def _repr_(self):
        return "Monoid of set compositions of %s" % (self.underlying_set(),)

    # def __iter__(self):
    #     for osp in OrderedSetPartitions(self.underlying_set()):
    #         yield self(self.Element.wrapped_class(osp))

    # @cached_method
    def product(self, x, y):
        assert x in self
        assert y in self
        new_composition = []
        for B in x.value:
            for C in y.value:
                BintC = B.intersection(C)
                if BintC:
                    new_composition.append(BintC)
        return self(self.Element.wrapped_class(new_composition))

    @cached_method
    def one(self):
        return self(self.Element.wrapped_class([self.underlying_set()]))

    @cached_method
    def semigroup_generators(self):
        from sage.combinat.set_partition_ordered import OrderedSetPartitions
        from sage.sets.family import Family
        return Family([self(self.Element.wrapped_class(X)) for X in
                       OrderedSetPartitions(self.underlying_set(), 2)])

    def an_element(self):
        return self.semigroup_generators()[0]

    def create_element(self, x):
        return self(self.Element.wrapped_class(map(Set, x)))

    def from_permutation(self, perm):
        return self.create_element([[i] for i in perm])

    def minimal_ideal(self):
        return map(self.from_permutation, Permutations(sorted(self.underlying_set())))

    def directed_face_from_composition_and_permutation(self, comp, perm):
        def splitting(comp, w):
            it = iter(w)
            return tuple(tuple(it.next() for _ in range(i)) for i in comp)
        x = splitting(comp, perm)
        return self.create_element(x), self.from_permutation(perm)

    def bilinear_form_on_directed_faces_kernel_vectors_non_exhaustive(self):
        n = self.underlying_set().cardinality()
        directed_faces = self.directed_faces()
        IndexSet = dict((xc, i) for (i, xc) in enumerate(directed_faces))
        from collections import defaultdict
        K = []
        for partition in Partitions(n):
            for T in Permutations(partition):
                for U in Permutations(partition):
                    X = []
                    if T != U:
                        for D in Permutations(n):
                            TD = self.directed_face_from_composition_and_permutation(T, D)
                            UD = self.directed_face_from_composition_and_permutation(U, D)
                            X.append((TD, UD))
                        v = defaultdict(int)
                        for (TD, UD) in X:
                            v[IndexSet[TD]] += 1
                            v[IndexSet[UD]] += -1
                        K.append(vector(QQ, len(directed_faces), v))
        return K

    class Element (ElementWrapper):
        wrapped_class = tuple
        __lt__ = ElementWrapper._lt_by_value

        def shape(self):
            from sage.combinat.composition import Composition
            return Composition([len(B) for B in self.value])

        def reverse(self):
            return self.parent()(self.value[::-1])

        def _repr_(self):
            return '|'.join(''.join(map(str, block)) for block in self.value)
