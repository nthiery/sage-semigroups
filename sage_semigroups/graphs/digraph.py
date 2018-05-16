class DiGraph:

    def transition(self, u, a):
        """
        Transition function

        INPUT:

         - ``u`` -- a vertex of ``G`` or ``None``
         - ``a`` -- a label

        Assuming that ``self`` models a deterministic automaton `A`,
        this implements the transition of `A`. Namely, this returns
        ``v`` such that there is an edge ``(u, v, a)`` in ``G``, or
        ``None`` if there is no such edge.

        EXAMPLES::

            sage: automaton = DiGraph( [ (1, 1, "b"), (1, 2, "a"),
            ...                          (2, 2, "a"), (2, 2, "c"), (2, 3, "b"),
            ...                          (3, 2, "a"), (3, 3, "b"), (3, 3, "c") ] )
            sage: automaton.transition(1, "a")
            2
            sage: automaton.transition(1, "b")
            1
            sage: automaton.transition(1, "c")

        As a convenience, ``u`` can be ``None``, in which case the
        result is always None::

            sage: automaton.transition(None, "c")
        """
        if u is None:
            return None
        assert u in self
        for (_,v,l) in self.outgoing_edges(u):
            if l == a:
                return v
        return None

    def transition_monoid(self, alphabet = None, category = None, side='right'):
        """
        EXAMPLES::

            sage: automaton = DiGraph( [ (1, 1, "b"), (1, 2, "a"),
            ...                          (2, 2, "a"), (2, 2, "c"), (2, 3, "b"),
            ...                          (3, 2, "a"), (3, 3, "b"), (3, 3, "c") ] )
            sage: M = automaton.transition_monoid()
            sage: M.cardinality()
            7
            sage: M.list()
            [[], ['a'], ['b'], ['c'], ['a', 'c'], ['b', 'a'], ['b', 'c']]
            sage: for f in M:
            ...       print f, f.lift()
            []         map: 1 -> 1, 2 -> 2, 3 -> 3, None -> None
            ['a']      map: 1 -> 2, 2 -> 2, 3 -> 2, None -> None
            ['b']      map: 1 -> 1, 2 -> 3, 3 -> 3, None -> None
            ['c']      map: 1 -> None, 2 -> 2, 3 -> 3, None -> None
            ['a', 'c'] map: 1 -> None, 2 -> 2, 3 -> 2, None -> None
            ['b', 'a'] map: 1 -> 3, 2 -> 3, 3 -> 3, None -> None
            ['b', 'c'] map: 1 -> None, 2 -> 3, 3 -> 3, None -> None

        """
        from sage_semigroups.monoids.transition_monoid import TransitionMonoidOfDeterministicAutomaton
        return TransitionMonoidOfDeterministicAutomaton(self, alphabet = alphabet, category = category, side=side)

    def is_finite(self):
        return True

    def transition_module(self, alphabet = None, monoid=None, side="right"):
        r"""
        Constructs a transformation module whose Cayley graph is ``self``.

        INPUT:

        - ``alphabet`` -- a list of index of the operators (default:
          the set of labels of the edges of the graph)
        - ``monoid`` -- the monoid that is acting (default: the
          transition monoid of this automaton);
        - ``side`` -- 'left' or 'right' (default: 'right'); on which
          side the action is considered


        .. warning::

            At this point only the transition monoid is actually supported!
            One should support instead any monoid of whom the
            transition monoid is a quotient of, by going through
            reduced words.

        EXAMPLES::

            sage: automaton = DiGraph( [ (1, 1, "b"), (1, 2, "a"),
            ...                          (2, 2, "a"), (2, 2, "c"), (2, 3, "b"),
            ...                          (3, 2, "a"), (3, 3, "b"), (3, 3, "c") ] )
            sage: M = automaton.transition_module()
            sage: M.cayley_graph().edges() == automaton.edges()  # todo: not implemented (some edges are repeated!!!)
            True
            sage: set(M.cayley_graph().edges()) == set(automaton.edges())
            True

        Its semigroup is the transition monoid of ``self``::

            sage: M.semigroup()
            The transition monoid of Looped multi-digraph on 3 vertices
            sage: M.semigroup() is automaton.transition_monoid()
            True
            sage: TestSuite(M).run() # todo: several tests fail here
        """
        from sage.misc.misc import attrcall
        from sage.monoids.representations import SetWithAction
        if monoid is None:
            monoid = self.transition_monoid(alphabet = alphabet, side=side)
        else:
            assert monoid.automaton().vertices() == self.vertices()

        return SetWithAction(monoid, self.vertices(), attrcall("__call__"), side=side)
