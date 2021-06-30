from sage.structure.parent import Parent


class AutomaticSemigroup:
    def __init__(self, generators, ambient, one, mul, category):  # Bug fix
        """
        Initializes this semigroup.

        TESTS::

            sage: from sage.monoids.automatic_semigroup import AutomaticSemigroup
            sage: R = IntegerModRing(21)
            sage: M = AutomaticSemigroup(Family(()), one=R.one())
            sage: M.ambient() == R
            True
            sage: M = AutomaticSemigroup(Family(()))
            Traceback (most recent call last):
            ...
            ValueError: AutomaticSemigroup requires at least one generator or `one` to determine the ambient space

            sage: M = AutomaticSemigroup(Family([1,1,-1,1,0]), one=1) # Bug fix w.r.t. Sage 8.0
            sage: M.cardinality()
            sage: M.list()
            3
            [1, -1, 0]
        """
        Parent.__init__(self, category=category)

        # Attributes for the multiplicative structure
        self._ambient = ambient
        self._mul = mul
        if one is not None:
            self._one = self._retract(one)
            self._one._reduced_word = []

        # Attributes for the lazy construction of the elements
        self._constructed = False
        self._done = 0
        self._elements = [self.one()] if one is not None else []
        self._elements_set = set(self._elements)

        # Handle the generators
        self._generators_in_ambient = generators
        self._generators = generators.map(self._retract)
        for e in self._generators:
            e._reduced_word = [self._generators.inverse_family()[e]]
            if e in self._elements_set:
                continue
            self._elements.append(e)
            self._elements_set.add(e)

        self._iter = self.__init__iter()

        # Customization
        self._repr_element_method = "ambient"
