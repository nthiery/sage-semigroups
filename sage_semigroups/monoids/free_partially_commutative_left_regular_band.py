r"""
Free partially commutative left regular band

EXAMPLES::

    sage: import sage_semigroups
    Loading sage-semigroups and patching its features into Sage's library: ...

"""
from functools import reduce

from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.parent import Parent
from sage.structure.element_wrapper import ElementWrapper
from sage.misc.cachefunc import cached_method
from sage.graphs.graph import Graph
from sage.graphs.digraph import DiGraph


class FreePartiallyCommutativeLeftRegularBand(UniqueRepresentation, Parent):
    r"""
    TESTS::

        sage: from sage_semigroups.monoids.free_partially_commutative_left_regular_band import FreePartiallyCommutativeLeftRegularBand
        sage: n = 6
        sage: C = graphs.CycleGraph(n)
        sage: M = FreePartiallyCommutativeLeftRegularBand(C)
        sage: M.cardinality()
        721
    """
    @staticmethod
    def __classcall__(cls, graph):
        r"""
        Normalize the input: convert vertices to instances of ``str`` and
        delete edge labels.
        """
        if isinstance(graph, Graph):
            graph = graph.relabel(str, inplace=False)
            vertices = tuple(graph.vertices())
            edges = tuple((u, v) for (u, v, l) in graph.edges())
        elif isinstance(graph, tuple) and len(graph) == 2:
            vertices, edges = graph
        else:
            raise ValueError("incorrect input to __classcall__")
        return super(FreePartiallyCommutativeLeftRegularBand, cls).__classcall__(cls, (vertices, edges))

    def __init__(self, args):
        r"""
        The free partially commutative left regular band associated to the
        (undirected) graph ``graph``.

        This is the left regular band generated by the vertices of the graph
        and relations `xy = yx` for every edge `(x,y)` of the graph.

        EXAMPLES::

            sage: from sage_semigroups.monoids.free_partially_commutative_left_regular_band import FreePartiallyCommutativeLeftRegularBand
            sage: G = Graph({0:[],1:[],2:[]})
            sage: S = FreePartiallyCommutativeLeftRegularBand(G); S
            Free partially commutative left regular band on Graph on 3 vertices
            sage: K = graphs.CompleteGraph(4)
            sage: S = FreePartiallyCommutativeLeftRegularBand(K); S
            Free partially commutative left regular band on Graph on 4 vertices
            sage: TestSuite(S).run(skip=["_test_elements", "_test_pickling"])
        """
        (vertices, edges) = args
        graph = Graph()
        graph.add_vertices(vertices)
        graph.add_edges(edges)
        self._graph = graph
        from sage_semigroups.categories.finite_left_regular_bands import FiniteLeftRegularBands
        Parent.__init__(self, category=FiniteLeftRegularBands().FinitelyGenerated())

    def __iter__(self):
        from sage.combinat.backtrack import TransitiveIdeal
        return TransitiveIdeal(self.succ_generators(side="right"), [self.one()]).__iter__()

    def associated_graph(self):
        return self._graph

    def _repr_(self):
        return "Free partially commutative left regular band on %s" % (repr(self.associated_graph()),)

    @cached_method
    def one(self):
        r"""
        Returns the one of the monoid, as per :meth:`Monoids.ParentMethods.one`.

        EXAMPLES::

            sage: from sage_semigroups.monoids.free_partially_commutative_left_regular_band import FreePartiallyCommutativeLeftRegularBand
            sage: G = Graph({'a':['b'],'b':['d'],'c':[],'d':[]})
            sage: S = FreePartiallyCommutativeLeftRegularBand(G)
            sage: S.one()
            ''

        """
        return self("")

    @cached_method
    def semigroup_generators(self):
        r"""
        Returns the generators of the semigroup.

        EXAMPLES::

            sage: from sage_semigroups.monoids.free_partially_commutative_left_regular_band import FreePartiallyCommutativeLeftRegularBand
            sage: G = Graph({'a':['b'],'b':['d'],'c':[],'d':[]})
            sage: S = FreePartiallyCommutativeLeftRegularBand(G)
            sage: S.semigroup_generators()
            Family ('a', 'b', 'c', 'd')

        """
        from sage.sets.family import Family
        return Family([self(i) for i in self.associated_graph().vertices()])

    def an_element(self):
        r"""
        Returns an element of the semigroup.

        EXAMPLES::

            sage: from sage_semigroups.monoids.free_partially_commutative_left_regular_band import FreePartiallyCommutativeLeftRegularBand
            sage: G = Graph({'a':['b'],'b':['d'],'c':[],'d':[]})
            sage: S = FreePartiallyCommutativeLeftRegularBand(G)
            sage: S.an_element()
            'a'
            sage: K = graphs.CompleteGraph(3)
            sage: S = FreePartiallyCommutativeLeftRegularBand(K)
            sage: S.an_element()
            '0'

        """
        return self.semigroup_generators()[0]

    def product(self, x, y):
        r"""
        Returns the product of two elements of the semigroup.

        EXAMPLES::

            sage: from sage_semigroups.monoids.free_partially_commutative_left_regular_band import FreePartiallyCommutativeLeftRegularBand
            sage: G = Graph({'a':['b'],'b':['d'],'c':[],'d':[]})
            sage: S = FreePartiallyCommutativeLeftRegularBand(G)
            sage: S('a') * S('b')
            'ab'
            sage: S('a') * S('b') * S('a')
            'ab'
            sage: S('a') * S('a')
            'a'

        """
        return self._cached_product(x.value, y.value)

    @cached_method
    def _cached_product(self, x, y):
        r"""
        Returns the product of two elements of the semigroup.

        EXAMPLES::

            sage: from sage_semigroups.monoids.free_partially_commutative_left_regular_band import FreePartiallyCommutativeLeftRegularBand
            sage: G = Graph({'a':['b'],'b':['d'],'c':[],'d':[]})
            sage: S = FreePartiallyCommutativeLeftRegularBand(G)
            sage: S('a') * S('b')
            'ab'
            sage: S('a') * S('b') * S('a')
            'ab'
            sage: S('a') * S('a')
            'a'

        """
        xy = x + ''.join(c for c in y if c not in x)
        return self.normal_form(xy)

    @cached_method
    def normal_form(self, w):
        r"""
        Map a word to its Foata-Cartier normal form.

        TESTS::

            sage: from sage_semigroups.monoids.free_partially_commutative_left_regular_band import FreePartiallyCommutativeLeftRegularBand
            sage: G = Graph({'a':['b'],'b':['d'],'c':[],'d':[]})
            sage: S = FreePartiallyCommutativeLeftRegularBand(G); S
            Free partially commutative left regular band on Graph on 4 vertices
            sage: S.normal_form(S('cdab'))
            'cbda'
            sage: S.normal_form(S('dab'))
            'bda'
        """
        return self.element_class(self, self._normalize_word(w))

    def _normalize_word(self, w):
        if isinstance(w, self.element_class):
            w = w.value
        F = self.vertex_sequence(w)
        return ''.join(''.join(sorted(Fj)) for Fj in F)

    def vertex_sequence(self, w):
        r"""
        Return the Foata-Cartier *V-sequence* for the word `w`. It is uniquely
        defined.

        EXAMPLES::

            sage: from sage_semigroups.monoids.free_partially_commutative_left_regular_band import FreePartiallyCommutativeLeftRegularBand
            sage: n = 4
            sage: C = graphs.CycleGraph(n)
            sage: M = FreePartiallyCommutativeLeftRegularBand(C)
            sage: M.vertex_sequence('0123')
            ({'1', '0'}, {'3', '2'})

        """
        if isinstance(w, self.element_class):
            w = w.value
        return reduce(self._vertex_sequence_action_by_letter, w, ())

    def _vertex_sequence_action_by_letter(self, F, z):
        r"""
        DEFINITION: Suppose `F = (F_0, \dots, F_r)`.

        (1) If `z` is connected to `F_r`, then `F \cdot z = (F_0, \dots, F_r, \{z\})`.

        (2) Otherwise, let `j` be the smallest index such that `z` is not
        connected to any set `F_j, F_{j+1}, \dots, F_r`, and define
        `F \cdot z = (F_0, \dots, F_{j-1}, F_j \cup \{z\}, F_{j+1}, \dots)`.

        EXAMPLES::

            sage: from sage_semigroups.monoids.free_partially_commutative_left_regular_band import FreePartiallyCommutativeLeftRegularBand
            sage: n = 4
            sage: C = graphs.CycleGraph(n)
            sage: M = FreePartiallyCommutativeLeftRegularBand(C)
            sage: M.vertex_sequence('0123')
            ({'1', '0'}, {'3', '2'})
            sage: F = ()
            sage: for z in '0123':
            ....:     F = M._vertex_sequence_action_by_letter(F, z)
            ....:     print map(sorted, F)
            [['0']]
            [['0', '1']]
            [['0', '1'], ['2']]
            [['0', '1'], ['2', '3']]

        """
        from sage.sets.set import Set
        if len(F) == 0:
            return (Set([z]),)
        j = len(F) - 1
        while j >= 0:
            if self._is_connected(z, F[j]):
                break
            else:
                j -= 1
        if j + 1 == len(F):
            return F + (Set([z]),)
        else:
            return F[:j + 1] + (F[j + 1].union(Set([z])),) + F[j + 2:]

    def _is_connected(self, z, F_j):
        r"""
        Return whether `z` is connected to the set `F_j`.
        """
        return z in F_j or any(not self._graph.has_edge(x, z) for x in F_j)

    def _element_constructor_(self, x):
        if isinstance(x, str):
            return self.normal_form(x)
        else:
            return super(FreePartiallyCommutativeLeftRegularBand, self)._element_constructor_(x)

    def quiver_v2(self):
        # if hasattr(self, "_quiver_cache"):
        #     return self._quiver_cache
        from sage.combinat.subset import Subsets
        from sage.graphs.digraph import DiGraph
        Q = DiGraph(multiedges=True)
        Q.add_vertices(self.j_transversal())
        g = self.associated_graph()
        for U in Subsets(g.vertices()):
            for W in Subsets(U):
                h = g.subgraph(U.difference(W))
                n = h.connected_components_number() - 1
                if n > 0:
                    u = self.j_class_representative(self.j_class_index(self(''.join(U))))
                    w = self.j_class_representative(self.j_class_index(self(''.join(W))))
                    for i in range(n):
                        Q.add_edge(w, u, i)
        return Q

    # miscellaneous methods
    def iter_from_free_lrb(self):
        r"""
        Iterate through elements of the semigroup by projection elements of the
        free left regular band on the given generators.
        """
        from free_left_regular_band import FreeLeftRegularBand
        F = FreeLeftRegularBand(alphabet=tuple(x.value for x in self.semigroup_generators()))
        seen = {}
        for w in F:
            x = self.normal_form(w)
            if x not in seen:
                seen[x] = True
                yield x

    def induced_orientation(self, w):
        r"""
        The induced subgraph of the complement of the underlying graph with an
        orientation determined by `w`: an edge `(x,y)` is directed from `x` to
        `y` if `x` comes before `y` in `w`.

        EXAMPLES::

            sage: from sage_semigroups.monoids.free_partially_commutative_left_regular_band import FreePartiallyCommutativeLeftRegularBand
            sage: G = Graph({'a':['b'],'b':['d'],'c':[],'d':[]})
            sage: S = FreePartiallyCommutativeLeftRegularBand(G); S
            Free partially commutative left regular band on Graph on 4 vertices
            sage: w = S('cdab')
            sage: H = S.induced_orientation(w)
            sage: H.vertices()
            ['a', 'b', 'c', 'd']
            sage: H.edges()
            [('c', 'a', None), ('c', 'b', None), ('c', 'd', None), ('d', 'a', None)]
            sage: w = S('dab')
            sage: H = S.induced_orientation(w)
            sage: H.vertices()
            ['a', 'b', 'd']
            sage: H.edges()
            [('d', 'a', None)]

        """
        pos = {wi: i for i, wi in enumerate(w.value)}
        D = DiGraph()
        D.add_vertices(pos)
        for (u, v, l) in self.associated_graph().complement().edges():
            if u in pos and v in pos:
                if pos[u] < pos[v]:
                    D.add_edge(u, v)
                else:
                    D.add_edge(v, u)
        return D

    class Element (ElementWrapper):
        wrapped_class = str
        __lt__ = ElementWrapper._lt_by_value

        def __eq__(self, other):
            r"""

            EXAMPLES::

                sage: from sage_semigroups.monoids.free_partially_commutative_left_regular_band import FreePartiallyCommutativeLeftRegularBand
                sage: G = Graph({'a':['b'],'b':['d'],'c':[],'d':[]})
                sage: S = FreePartiallyCommutativeLeftRegularBand(G)
                sage: w, u = S('cdab'), S('cbda')
                sage: w == w
                True
                sage: u == u
                True
                sage: w == u
                True
                sage: a, b = S('dab'), S('dba')
                sage: a == b
                True
                sage: a == w
                False

            """
            return (self.__class__ is other.__class__ and
                    self.parent() == other.parent() and
                    self.value == other.value)

        def length(self):
            return len(self.value)


FPCLRB = FreePartiallyCommutativeLeftRegularBand
