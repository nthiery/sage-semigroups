r"""
The Transition Monoid of an automaton
"""
#*****************************************************************************
#  Copyright (C) 2011 Nicolas M. Thiery <nthiery at users.sf.net>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************

import functools
import operator
from copy import copy
from sage.sets.family import Family
from sage.sets.finite_set_maps import FiniteSetMaps
from sage.categories.monoids import Monoids
from sage.monoids.automatic_semigroup import AutomaticMonoid

class TransitionMonoidOfDeterministicAutomaton(AutomaticMonoid):
    """
    INPUT:

     - ``automaton`` -- a deterministic automaton (currently encoded as a DiGraph)

    EXAMPLES:

    We consider the example p. 83 of [Pin.MPRI]_::

        sage: automaton = DiGraph( [ (1, 1, "b"), (1, 2, "a"),
        ...                          (2, 2, "a"), (2, 2, "c"), (2, 3, "b"),
        ...                          (3, 2, "a"), (3, 3, "b"), (3, 3, "c") ] )
        sage: M = automaton.transition_monoid()
        sage: M.cardinality()
        7
        sage: M.list()
        [[], ['b'], ['a'], ['c'], ['b', 'a'], ['b', 'c'], ['a', 'c']]

    TESTS::

        sage: automaton = DiGraph()
        sage: M = automaton.transition_monoid()
        sage: M.cardinality()
        1
    """

    @staticmethod
    def __classcall__(cls, automaton, alphabet=None, category=None, side='right'):
        automaton = copy(automaton)
        automaton._immutable = True  # should be automaton.set_immutable
        category = Monoids().Transformation().Finite().Subobjects().FinitelyGenerated().or_subcategory(category, join=True)
        if alphabet is None:
            alphabet = tuple(sorted(set(automaton.edge_labels())))
        else:
            alphabet = tuple(alphabet) # for safety for the moment

        return super(TransitionMonoidOfDeterministicAutomaton, cls).__classcall__(cls, automaton, alphabet, category, side)

    def __init__(self, automaton, alphabet, category, side):
        """
            sage: automaton = DiGraph( [ (1, 1, "b"), (1, 2, "a"),
            ...                          (2, 2, "a"), (2, 2, "c"), (2, 3, "b"),
            ...                          (3, 2, "a"), (3, 3, "b"), (3, 3, "c") ] )
            sage: from sage.monoids.transition_monoid import TransitionMonoidOfDeterministicAutomaton
            sage: M = TransitionMonoidOfDeterministicAutomaton(automaton)
            sage: M.cardinality()
            7
            sage: M.list()
            [[], ['a'], ['b'], ['c'], ['a', 'b'], ['b', 'c'], ['c', 'a']]
            sage: TestSuite(M).run()

        Since ``automaton`` is mutable, we made a private copy of it::

            sage: M.automaton() == automaton
            True
            sage: M.automaton() is automaton
            False
        """

        # Should check that automaton is deterministic
        self._automaton = automaton
        # We would want to have FiniteSetPartialMaps
        ambient = FiniteSetMaps( list(automaton.vertices())+[None], action=side)
        def generator(a):
            return ambient( functools.partial(automaton.transition, a = a) )
        generators = Family( alphabet, generator )
        AutomaticMonoid.__init__(self, generators, ambient, ambient.one(), operator.mul, category)

    def automaton(self):
        r"""
        EXAMPLES::

            sage: automaton = DiGraph( [ (1, 1, "b"), (1, 2, "a"),
            ...                          (2, 2, "a"), (2, 2, "c"), (2, 3, "b"),
            ...                          (3, 2, "a"), (3, 3, "b"), (3, 3, "c") ] )
            sage: M = automaton.transition_monoid()
            sage: M.automaton()
            Looped multi-digraph on 3 vertices
            sage: M.automaton() == automaton
            True
        """
        return self._automaton

    def _repr_(self):
        """
        EXAMPLES::

            sage: automaton = DiGraph( [ (1, 1, "b"), (1, 2, "a"),
            ...                          (2, 2, "a"), (2, 2, "c"), (2, 3, "b"),
            ...                          (3, 2, "a"), (3, 3, "b"), (3, 3, "c") ] )
            sage: automaton.transition_monoid()
            The transition monoid of Looped multi-digraph on 3 vertices

        """
        return "The transition monoid of %s"%self.automaton()
