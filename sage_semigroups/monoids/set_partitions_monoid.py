r"""
Monoid of set partitions

EXAMPLES::

    sage: import sage_semigroups
    Loading sage-semigroups and patching its features into Sage's library: ...

"""

from sage.misc.cachefunc import cached_method
from sage.sets.set import Set_object_enumerated
from sage.structure.element_wrapper import ElementWrapper
from sage.combinat.set_partition import SetPartitions
from .set_compositions_monoid import SetCompositionsMonoid

class SetPartitionsMonoid(SetCompositionsMonoid):
    def _repr_(self):
        return "Monoid of set partitions of %s" % self._underlying_set

    def __iter__(self):
        r"""

        EXAMPLES::

            sage: from sage_semigroups.monoids.set_partitions_monoid import SetPartitionsMonoid
            sage: [SetPartitionsMonoid(n).cardinality() for n in range(8)]
            [1, 1, 2, 5, 15, 52, 203, 877]

            sage: S = SetPartitionsMonoid(4); S
            Monoid of set partitions of {1, 2, 3, 4}
            sage: TestSuite(S).run()

        """
        for sp in SetPartitions(self._underlying_set):
            yield self(Set_object_enumerated(sp))

    @cached_method
    def semigroup_generators(self):
        from sage.sets.family import Family
        return Family([self(Set_object_enumerated(X)) for X in SetPartitions(self._underlying_set,2)])

    class Element (ElementWrapper):
        wrapped_class = Set_object_enumerated
        __lt__ = ElementWrapper._lt_by_value

        def to_set_composition(self):
            n = sum(map(len, self.value))
            x = tuple(sorted(self.value, key=min))
            return SetCompositionsMonoid(n)(x)


