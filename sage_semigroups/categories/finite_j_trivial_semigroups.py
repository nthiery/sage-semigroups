# -*- encoding: utf-8 -*-
r"""
Finite J-Trivial semigroups

    sage: import sage_semigroups # random
"""
#*****************************************************************************
#  Copyright (C) 2009-2010 Florent Hivert <florent.hivert at univ-rouen.fr>
#                2009-2017 Nicolas M. Thiery <nthiery at users.sf.net>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************

from sage.misc.cachefunc import cached_method, cached_in_parent_method
from sage.misc.misc import attrcall
from sage.categories.category_with_axiom import CategoryWithAxiom
from sage.categories.algebra_functor import AlgebrasCategory
from sage_semigroups.categories.character_ring_functor import CharacterRingsCategory
from sage.categories.with_realizations import WithRealizationsCategory
from sage.sets.family import Family
from sage.combinat.ranker import rank_from_list

class FiniteJTrivialSemigroups(CategoryWithAxiom):
    """
    EXAMPLES::

        sage: C = Semigroups().JTrivial().Finite(); C
        Category of finite j trivial monoids
        sage: C.super_categories()
        [Category of j trivial monoids, Category of finite h trivial monoids]
        sage: M = C.example()
        sage: M.cardinality()
        14
        sage: M
        The monoid of Non Decreasing Parking Functions on {1, 2, 3, 4}

        sage: TestSuite(C).run()
        sage: TestSuite(M).run()
        sage: import sage.monoids.catalog as semigroups
        sage: M = semigroups.NDPFMonoidPoset(Posets(3)[3])
        sage: TestSuite(M).run()
    """

    def example(self, n = 4):
        """
        Returns the monoid of (type A) non decreasing parking functions,
        as an example of finite J-trivial semigroup.

        EXAMPLES::

            sage: Semigroups().JTrivial().Finite().example()
            The (automatic) monoid with generators Finite family {1: [1], 2: [2], 3: [3]}
        """
        from sage_semigroups.monoids.catalog import NDPFMonoid
        return NDPFMonoid(n)

    class ParentMethods:

        @cached_method
        def semigroup_generators(self):
            """
            Returns the canonical minimal set of generators. It
            consists of the irreducible elements, that is elements
            which are not of the form `x*y` with `x` and `y` in
            ``self`` distinct from `x*y`.

            As a slight optimization, this only computes products
            `x*y` for those `x` which are not yet known to be
            reducible.

            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.NDPFMonoidPosetNew(Posets.ChainPoset(4))
                sage: M.semigroup_generators()
                Family (...)
                sage: sorted(M.semigroup_generators())
                [[0, 1, 2, 2], [0, 1, 1, 3], [0, 0, 2, 3]]
            """
            result = set(self.list())
            result.remove(self.one())
            for x in self:
                if x in result:
                    for y in self:
                        xy = x*y
                        if xy != x and xy != y:
                            result.discard(xy)
            return Family(result)

        @cached_method
        def cartan_matrix_as_table(self, q=None):
            result = dict()
            for x in self:
                if q is None:
                    coeff = 1
                else:
#                    coeff = q**(self.factorization_poset_lengths()[x])
                    coeff = q**(self.compatible_lengths()[x])
                e = x.symbol("left")
                f = x.symbol("right")
                result[e,f] = result.get((e,f), 0) + coeff
            return result

        @cached_method
        def cartan_matrix(self, q = None, idempotents = None):
            """
            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.NDPFMonoidPoset(Posets(3)[3])
                sage: M.cartan_matrix(var('q'))
                [1 0 0 0]
                [0 1 q 0]
                [0 0 1 0]
                [0 0 0 1]

            The algorithm used for computing the q-Cartan matrix is
            experimental. It has been tested for the 0-Hecke monoid in
            types A1-A4, B2-3,G2, and for NDPFMonoidB 1-5.

                sage: M =  PiMonoid(["A",3])               # long time
                sage: m1 = M.cartan_matrix(var('q'))       # long time
                sage: m2 = M.cartan_matrix_mupad(var('q')) # long time
                sage: isomorphic_cartan_matrices(m1,m2)    # long time
                True

                sage: M =  PiMonoid(["A",4])               # long time
                sage: m1 = M.cartan_matrix(var('q'))       # long time
                sage: m2 = M.cartan_matrix_mupad(var('q')) # long time
                sage: isomorphic_cartan_matrices(m1,m2)    # long time
                True

            The current version *does* fail for the 0-Hecke monoid of
            type D_4!!!

                sage: ZZ.<q> = ZZ[]
                sage: list(sum(sum(PiMonoid(["D",4]).cartan_matrix(q)))) # long time
                [16, 38, 62, 35, 20, 15, 6]

            Compare with:

                sage: list(sum(sum(PiMonoid(["D",4]).cartan_matrix_mupad(q)))) # long time
                [16, 38, 62, 38, 20, 12, 6]

            Which could mean that the factorization constraints are too weak.

            """
            #left_symbols,  right_modules = cartan_data_of_j_trivial_monoid(self, side="left" )
            #right_symbols, left_modules  = cartan_data_of_j_trivial_monoid(self, side="right")
            if idempotents is None:
                idempotents = self.idempotents()
            #idempotents = [self.retract(self.ambient.e(w)) for w in self.ambient.W]
            rank = rank_from_list(idempotents)
            from sage.matrix.constructor import matrix
            if q is None:
                cartan_matrix = matrix(len(idempotents), len(idempotents), sparse=True)
            else:
                cartan_matrix = matrix(q.parent(), len(idempotents), len(idempotents), sparse=True)
            for (e,f),coeff in self.cartan_matrix_as_table(q).iteritems():
                cartan_matrix[rank(e), rank(f)] = coeff
            return cartan_matrix

        @cached_method
        def cartan_matrix_as_graph(self, q=None):
            from sage.graphs.graph import DiGraph
            G = DiGraph()
            G.add_vertices(self.idempotents())
            for (e,f),coeff in self.cartan_matrix_as_table(q).iteritems():
                G.add_edge(e,f, None if coeff == 1 else coeff)
            return G

        @cached_method
        def quiver_elements(self):
            """
            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.NDPFMonoidPoset(Posets(3)[3])
                sage: M.quiver_elements()
                [[3]]
            """
            fact = self.compatible_factorisations()
            return [x for x in self.non_idempotents() if fact[x] == []]

        @cached_method
        def quiver(self, edge_labels=True, index=False):
            """
            Returns the quiver of ``self``

            INPUT:

             - ``edges_labels`` -- whether to use the quiver element
               as label for the edges between the idempotents; if
               False, this may lead to multiple edges when the monoid
               is not generated by idempotents (default: True)

             - ``index`` -- whether to index the vertices of the graph
               by the indices of the simple modules rather than the
               corresponding idempotents (default: False)

            OUTPUT: the quiver of ``self``, as a graph with the
            idempotents of this monoid as vertices

            .. todo:: should index default to True?

            .. todo:: use a meaningful example

            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.NDPFMonoidPoset(Posets(3)[3])
                sage: G = M.quiver()
                sage: G
                Digraph on 4 vertices
                sage: G.edges()
                [([1], [2], [3])]
                sage: M.quiver(edge_labels=False).edges()
                [([1], [2], None)]
                sage: M.quiver(index=True).edges()
                [(2, 1, [3])]
                sage: M.quiver(index=True, edge_labels=False).edges()
                [(2, 1, None)]
            """
            from sage.graphs.graph import DiGraph
            res  = DiGraph()
            if index:
                res.add_vertices(self.simple_modules_index_set())
                symbol = attrcall("symbol_index")
            else:
                res.add_vertices(self.idempotents())
                symbol = attrcall("symbol")
            for x in self.quiver_elements():
                res.add_edge(symbol(x,"left"), symbol(x, "right"), x if edge_labels else None)
            return res

        @cached_method
        def j_compatible_list(self):
            """
            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.NDPFMonoidPoset(Posets(3)[3])
                sage: sorted(M.j_compatible_list())
                [[], [1], [2], [3], [4]]
            """
            g = self.cayley_graph(side="twosided", simple=True)
            return g.topological_sort()

        @cached_method
        def j_order_as_graph(self):
            """
            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.NDPFMonoidPoset(Posets(3)[3])
                sage: M.j_order_as_graph().adjacency_matrix()
                [0 1 1 1 1]
                [0 0 0 1 1]
                [0 0 0 1 1]
                [0 0 0 0 1]
                [0 0 0 0 0]
            """
            g = self.cayley_graph(side="twosided", simple=True)
            return g.transitive_closure()

        def j_order(self, a, b):
            """
            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.NDPFMonoidPoset(Posets(3)[3])
                sage: all(M.j_order(M.one(), x) for x in M)
                True
                sage: [M.j_order(a,b) for a in M for b in M] 
                [True, True, True, True, True, False, True, False, True, True, False, False, True, True, True, False, False, False, True, True, False, False, False, False, True]
            """
            return  a == b or self.j_order_as_graph().has_edge(a, b)

        @cached_method
        def factorization_poset_lengths(self):
            """

            """
            P = self.factorization_poset()
            level_sets = P.level_sets()
            return dict( (u.element, i) for i in range(len(level_sets)) for u in level_sets[i] )

        @cached_method
        def factorization_poset(self):
            """
            Returns the poset on self, where `u < w` if either u is
            the left symbol of w, or there exists a compatible
            factorization `w = u v` where v is in the quiver.

            The elements at level 1 are the elements of the quiver

            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = PiMonoid(["A",3])
                sage: P = M.factorization_poset(); P
                Finite poset containing 24 elements

            The minimal elements are the idempotents of M::

                sage: sorted([x.element for x in P.minimal_elements()]) == sorted(M.idempotents())
                True

            The elements at level 1 index the quiver of M::

                sage: sorted([x.element for x in P.level_sets()[1]]) == sorted(M.quiver_elements())
                True
            """
            quiver = self.quiver_elements()
            edges = [ [u,uv] for (uv,l) in self.compatible_factorisations_strong().iteritems() for (u,v) in l if v in quiver ] + [ [ u.symbol("left"), u ] for u in self.non_idempotents() ]
            from sage.combinat.posets.posets import Poset
            return Poset((self, edges), cover_relations = False)

        @cached_method
        def initial_of_iterated_radical(self,use_quiver=True):
            r"""
            Returns the poset on self, where `u < w` if `w=uv` for
            some v such that `\lt (u-u^\infty)(v-v^\infty) = uv`

            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: map(len, PiMonoid(["B",3]).initial_of_iterated_radical())
                [8, 10, 14, 10, 6]

            This match MuPAD's q-Cartan matrix for A1-3,B2-3,G2, but fails for A4::

                sage: map(len, PiMonoid(["A",4]).initial_of_iterated_radical()) # long time
                [16, 32, 38, 26, 8]

            Compare with::

                sage: list(sum(sum(PiMonoid(["A",4]).cartan_matrix(q)))) # long time
                [16, 32, 38, 24, 10]

            Which could mean that we are missing some valid factorizations

            """
            def is_good_factorization1(fact): # Too strong (A4, even with use_quiver=False)
                product = self.prod(fact)
                if product.symbol("left") != fact[0].symbol("left"):
                    return False
                for i in range(len(fact)):
                    if self.prod(fact[:i])*fact[i].pow_omega()*self.prod(fact[i+1:]) == product:
                        return False
                return True
            def is_good_factorization2(factorization): # Too strong (D4)
                for i in range(1,len(factorization)):
                    u = self.prod(factorization[:i])
                    v = self.prod(factorization[i:])
                    uv = u*v
                    if u.symbol("left") != uv.symbol("left") or v.symbol("right") != uv.symbol("right") or u.symbol("right") != v.symbol("left"):
                        return False
                return True
            def is_good_factorization3(factorization): # Too weak (A4,B3)
                for i in range(1,len(factorization)):
                    u = self.prod(factorization[:i])
                    v = self.prod(factorization[i:])
                    uv = u*v
                    if u.symbol("left") != uv.symbol("left") or v.symbol("right") != uv.symbol("right"):
                        return False
                return True
            is_good_factorization = is_good_factorization1
            depth = dict( (u, 0) for u in self )
            smaller_factorizations = [[]]
            if use_quiver:
                factors = self.quiver_elements()
            else:
                factors = self.non_idempotents()
            for k in range(1, self.cardinality()):
                # print(k, len(smaller_factorizations))
                factorizations = []
                found = False
                for smaller_factorization in smaller_factorizations:
                    for v in factors:
                        factorization = smaller_factorization + [v]
                        if is_good_factorization(factorization):
                            product = self.prod(factorization)
                            depth[product] = k
                            found = True
                            factorizations.append(factorization)
                if not found:
                    break
                smaller_factorizations = factorizations
            levels = [ [] for i in range(k) ]
            for u in self:
                levels[depth[u]].append(u)
            return levels

        @cached_method
        def non_idempotents(self):
            """
            Returns the list of non idempotents in a (reverse) j-compatible
            order that is `x <_J y` then `x` is generated *after* `y`.

            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.NDPFMonoidPoset(Posets(3)[3])
                sage: M.non_idempotents()
                [[3]]
                sage: ni = PiMonoid(["A", 3]).non_idempotents(); ni # random order
                [[1, 2], [2, 1], [2, 3], [3, 2], [1, 2, 3], [1, 3, 2], [1, 2, 1, 3], [1, 2, 1, 3, 2], [1, 3, 2, 1], [1, 2, 3, 2, 1], [2, 1, 3], [3, 2, 1], [2, 1, 3, 2], [2, 1, 3, 2, 1], [2, 3, 2, 1], [1, 2, 3, 2]]
                sage: len(ni)
                16
            """
            return [ x for x in self.j_compatible_list() if not x.is_idempotent() ]

        @cached_method
        def symbol_sorted_non_idempotents(self, side="left"):
            """
            Returns a dictionnary ``s : [k_1,...,k_l]`` which associates to
            each idempotent ``e`` of ``self`` the list of all non-idempotent
            elements ``k`` of symbol ``e``. The symbols are taken on the given
            side. If side is ``"both"`` then ``s`` is replaced by the pair of
            left and right symbols.

            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: PiMonoid(["A", 2]).symbol_sorted_non_idempotents("left") # random order
                {[2]: [[2, 1]], [1]: [[1, 2]]}
                sage: PiMonoid(["A", 2]).symbol_sorted_non_idempotents("right") # random order
                {[1]: [[2, 1]], [2]: [[1, 2]]}
                sage: PiMonoid(["A", 2]).symbol_sorted_non_idempotents("both") # random order
                {([2], [1]): [[2, 1]], ([1], [2]): [[1, 2]]}
                """
            res = {}
            for x in self.non_idempotents():
                if side == "both":
                    symb = (x.symbol("left"), x.symbol("right"))
                else:
                    symb = x.symbol(side)
                res.setdefault(symb, []).append(x)
            return res

        @cached_method
        def compatible_factorisations_strong(self):
            """
            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.NDPFMonoidPoset(Posets(3)[3])
                sage: M.compatible_factorisations()
                {[3]: []}
            """
            non_idemp = self.non_idempotents()
            res = dict( (x, []) for x in non_idemp )
            for x in non_idemp:
                for y in non_idemp:
                    if x.symbol("right") == y.symbol("left"):
                        xy = x*y
                        if (x.symbol("left") == xy.symbol("left") and
                            y.symbol("right") == xy.symbol("right")):
                            res[xy].append([x,y])
            return res

        @cached_method
        def non_trivial_factorisations(self):
            """
            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.NDPFMonoidPoset(Posets(3)[3])
                sage: M.non_trivial_factorisations()
                {[3]: []}
                sage: M = PiMonoid(["A", 3])
                sage: M.non_trivial_factorisations() # random order
            """
            non_idemp = self.non_idempotents()
            res = dict( (x, []) for x in non_idemp )
            for x in non_idemp:
                for y in non_idemp:
                    xy = x*y
                    e = xy.symbol("left")
                    f = xy.symbol("right")
                    if e*x != x and x*f != f:
                        res[xy].append([x,y])
            return res

        @cached_method
        def compatible_factorisations(self):
            """
            This is equal to :meth:``compatible_factorisations_strong`` but
            faster.

            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.NDPFMonoidPoset(Posets(3)[3])
                sage: M.compatible_factorisations()
                {[3]: []}
                sage: M = PiMonoid(["A", 3])
                sage: M.compatible_factorisations() # random order
                {[3, 2]: [], [2, 3]: [], [1, 2, 3]: [[[1, 2], [2, 3]]], [1, 3, 2, 1]: [], [1, 2, 1, 3, 2]: [[[1, 2, 1, 3], [1, 2, 3, 2]]], [3, 2, 1]: [[[3, 2], [2, 1]]], [1, 2]: [], [1, 3, 2]: [], [1, 2, 3, 2, 1]: [[[1, 3, 2], [2, 1, 3]], [[1, 3, 2, 1], [1, 2, 1, 3]], [[1, 2, 3, 2], [2, 3, 2, 1]]], [2, 1]: [], [2, 1, 3, 2]: [[[2, 1, 3], [1, 3, 2]]], [1, 2, 1, 3]: [], [2, 1, 3]: [], [2, 3, 2, 1]: [], [2, 1, 3, 2, 1]: [[[2, 3, 2, 1], [1, 3, 2, 1]]], [1, 2, 3, 2]: []}

            For some reason the order is the same so that::

                sage: M.compatible_factorisations() == M.compatible_factorisations_strong()
                True

            We check the coherency with NCSF6. The following must hold for any
            integer ``n``::

                sage: n = 3;  M = PiMonoid(["A", n]); res = (3*n-4)*2^(n-2)
                sage: len([x for x in M.compatible_factorisations().values() if x==[]]) == res
                True
            """
            sort_symb = self.symbol_sorted_non_idempotents("left")
            res = dict( (x, []) for x in self.non_idempotents() )
            for (lft, elts) in sort_symb.items():
                for x in elts:
                    for y in sort_symb.get(x.symbol("right"), []):
                        xy = x*y
                        if (lft == xy.symbol("left") and
                            y.symbol("right") == xy.symbol("right")):
                            res[xy].append([x,y])
            return res

        @cached_method
        def compatible_factorisations_weak(self):
            """
            This returns the weak version of compatible factorization
            See :meth:``compatible_factorisations_strong``.

            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.NDPFMonoidPoset(Posets(3)[3])
                sage: M.compatible_factorisations_weak()
                {[3]: []}
            """
            non_idemp = self.non_idempotents()
            res = dict( (x, []) for x in non_idemp )
            for x in non_idemp:
                for y in non_idemp:
                    xy = x*y
                    if (x.symbol("left") == xy.symbol("left") and
                        y.symbol("right") == xy.symbol("right")):
                        res[xy].append([x,y])
            return res

        def compatible_factorisations_left(self):
            """
            Just for checking counter-example. In general is no equal to
            :meth:``compatible_factorisations``.

            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.NDPFMonoidPoset(Posets(3)[3])
                sage: M.compatible_factorisations_weak()
                {[3]: []}
            """
            non_idemp = self.non_idempotents()
            res = dict( (x, []) for x in non_idemp )
            for x in non_idemp:
                for y in non_idemp:
                    xy = x*y
                    if x.symbol("left") == xy.symbol("left"):
                        res[xy].append([x,y])
            return res

        @cached_method
        def compatible_lengths(self):
            """
            """
            res = dict((x, 0) for x in self.idempotents())
            fact = self.compatible_factorisations()
            for x in self.non_idempotents(): # j-order compatible enumeration
                if fact[x] == []:
                    res[x] = 1
                else:
                    res[x] = max(res[a] + res[b] for a,b in fact[x])
            return res

        def check_conj_factorization(self):
            """
            Check that the Compatible semigroup of self is associative using
            Anne and Tom's short tests.

            sage: import sage_semigroups.monoids.catalog as semigroups
            sage: P = Poset([range(7), [[0,1],[1,2],[1,3],[2,4],[3,4],[3,5],[4,6],[5,6]]])
            sage: M = semigroups.NDPFMonoidPosetNew(P)
            sage: M.check_conj_factorization()
            Size ... 100 ...

            sage: P1 = Poset([range(7), [[0,1],[1,2],[1,3],[2,4],[3,4],[3,5],[5,6]]])
            sage: M1 = semigroups.NDPFMonoidPosetNew(P1)
            sage: M1.check_conj_factorization()
            Size ... 100 ...
            """
            M = self
            from sage.combinat.j_trivial_monoids import CompatibleSemiGroup
            C = CompatibleSemiGroup(M)

            print(M.cardinality())
            idm = M.idempotents()
            print("#idemp = %s"%(len(idm)))
            print("sorting elements...")
            M.symbol_sorted_non_idempotents("right")
            M.symbol_sorted_non_idempotents("left")
            print("done")
            right_bad_pairs = []
            left_bad_pairs = []
            for id in idm:
                for x in M.symbol_sorted_non_idempotents("right").get(id, []):
                    for y in M.symbol_sorted_non_idempotents("left").get(id, []):
                        if (x*y).symbol("right") != y.symbol("right"):
                            right_bad_pairs.append((x,y))
                        if (x*y).symbol("left") != x.symbol("left"):
                            left_bad_pairs.append((x,y))
            print("#right bad pairs = %i"%(len(right_bad_pairs)))
            print("#left bad pairs = %i"%(len(left_bad_pairs)))

            for (x, y) in right_bad_pairs:
                rsymb = y.symbol("right")
                for z in M.symbol_sorted_non_idempotents("left").get(rsymb, []):
                    print(x, y, z)
                    assert (C(x)*C(y))*C(z) == C(x)*(C(y)*C(z))

            for (x, y) in left_bad_pairs:
                rsymb = x.symbol("left")
                for z in M.symbol_sorted_non_idempotents("right").get(rsymb, []):
                    print(z, x, y)
                    assert C(z)*(C(x)*C(y)) == (C(z)*C(x))*C(y)


        @cached_method
        def projective_module(self, idempotent, side = "left"):
            r"""
            INPUT:
             - idempotent: an idempotent of this monoid
             - side: "left" or "right"

            Returns the set P of elements x of the monoid such that
            the set ``\{b_x, x \in P\}`` is a basis of the left
            (resp. right) projective module associated to the
            idempotent

            The implementation is stupid ...

            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.NDPFMonoidPoset(Posets(3)[3])
                sage: M.projective_module(M.one())
                [[]]
                sage: [M.projective_module(x) for x in M.idempotents()]
                [[[]], [[1]], [[2], [3]], [[4]]]
            """
            if side == "left":
                symbol_side = "right"
            else:
                symbol_side = "left"
            return [ x for x in self
                     if x.symbol(side=symbol_side) == idempotent ]

        def _test_j_trivial(self, **options):

            """
            Test that ``self`` in indeed j-trivial.

            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.NDPFMonoidPoset(Posets(3)[3])
                sage: M._test_j_trivial()

            See also :class:`TestSuite`.
            """
            tester = self._tester(**options)
            for cl in self.j_classes():
                tester.assert_(len(cl) == 1, "Non trivial j class: %s"%(cl))

        def _test_symbol(self, **options):
            """
            Tests the ``symbol`` method of elements of this monoid.

            EXAMPLES::

                sage: M = Semigroups().JTrivial().Finite().example()
                sage: M._test_symbol()
                sage: M._test_symbol(elements = M)
            """
            tester = self._tester(**options)
            for x in tester.some_elements():
                e = x.symbol(side = "left")
                f = x.symbol(side = "right")
                tester.assert_(e.is_idempotent())
                tester.assert_(f.is_idempotent())
                tester.assertEquals(e*x, x)
                tester.assertEquals(x*f, x)


    class ElementMethods:
        @cached_in_parent_method
        def symbol(self, side = "left"):
            """
            INPUT:

             - ``self`` -- a monoid element `x`
             - ``side`` -- "left", "right"

            Returns the unique minimal idempotent `e` (in J-order)
            such that `e x = x` (resp. `xe = x`).

            EXAMPLES::

                sage: M = Semigroups().JTrivial().Finite().example()
                sage: M.cardinality()
                14
                sage: [x.symbol(side = "right") for x in M]
                [[], [1], [2], [3], [2], [1, 3], [2, 1], [3], [3, 2], [3], [3, 2], [1, 3], [3, 2, 1], [3, 2]]
                sage: [x.symbol(side = "left") for x in M]
                [[], [1], [2], [3], [1], [1, 3], [2, 1], [2], [3, 2], [1], [1, 3], [2, 1], [3, 2, 1], [2, 1]]
            """
            monoid = self.parent()

            if side == "left":
                fix = [ s for s in monoid.semigroup_generators() if (s * self == self) ]
            else:
                fix = [ s for s in monoid.semigroup_generators() if (self * s == self) ]
            return (monoid.prod(fix)).pow_omega()

        def symbol_index(self, side = "left"):
            """
            INPUT:

             - ``self`` -- a monoid element `x`
             - ``side`` -- "left", "right", or "both"

            Returns the (index of) the j_class of the left/right symbol of self.

            EXAMPLES::

                sage: M = Semigroups().JTrivial().Finite().example()
                sage: [x.symbol_index() for x in M]
                [0, 1, 5, 7, 1, 2, 3, 5, 4, 1, 2, 3, 6, 3]
                sage: [x.symbol_index(side = "left") for x in M]
                [0, 1, 5, 7, 1, 2, 3, 5, 4, 1, 2, 3, 6, 3]
                sage: [x.symbol_index(side = "right") for x in M]
                [0, 1, 5, 7, 5, 2, 3, 7, 4, 7, 4, 2, 6, 4]
                sage: [x.symbol_index(side = "both") for x in M]
                [(0, 0), (1, 1), (2, 2), (3, 3), (1, 2), (4, 4), (6, 6), (2, 3), (5, 5), (1, 3), (4, 5), (6, 4), (7, 7), (6, 5)]

            TODO: cleanup symbol/fix as follow:

             - fix(left/right) should return an idempotent
             - symbol(left/right) should return the index of a simple module
             - add a method M.j_class_of_idempotent(e), or e.j_class()?
            """
            if side == "both":
                return (self.symbol_index(side="left"), self.symbol_index(side="right"))
            else:
                return self.parent().j_transversal_of_idempotents().inverse_family()[self.symbol(side)]


    ###################################################################
    class Algebras(AlgebrasCategory):

        class ParentMethods:

            @cached_method
            def g(self, idempotent):
                """
                INPUT:
                 - ``idempotent`` - an idempotent of self

                Returns f_i, obtained by inclusion-exclusion from the
                lower idempotents of the monoid in j-order

                EXAMPLES::

                """
                monoid = self.basis().keys()
                K = self.base_ring()
                P = monoid.j_poset_on_regular_classes()
                e = monoid.j_transversal_of_idempotents()
                symbols = e.inverse_family()              # is this cached?
                j = symbols[idempotent]
                return self.sum(self.term(e[i], K(P.mobius_function(i,j)))
                                for i in P.principal_order_ideal(j))

            @cached_method
            def orthogonal_idempotents(self, idm_list=None):
                """
                Returns a maximal decomposition of the identity into
                orthogonal idempotents.

                INPUT:

                 - ``idmlist`` - the list (in a given order) of the idempotent
                   of the monoid. If none is given then a default is choosen.

                OUTPUT:

                  -- A family of idempotents indexed by the idempotents of
                  the monoid.

                EXAMPLES::

                    sage: import sage_semigroups.monoids.catalog as semigroups
                    sage: M = semigroups.NDPFMonoidPoset(Posets(3)[3])
                    sage: A = M.algebra(QQ)
                    sage: A.orthogonal_idempotents() # random order
                    Finite family {[]: B[[]] - B[[1]] - B[[2]] + B[[3]], [1]: B[[1]] - B[[4]], [4]: B[[4]], [2]: B[[2]] - B[[3]]}

                    sage: M = semigroups.NDPFMonoid(5)
                    sage: idms = M.idempotents()
                    sage: idmps = tuple(Permutations(idms).random_element())
                    sage: A = M.algebra(QQ)
                    sage: dec = A.orthogonal_idempotents(idmps)
                    sage: A._test_orthogonal_idempotents(dec)

                    sage: A = semigroups.NDPFMonoid(4).algebra(QQ)
                    sage: dec = A.orthogonal_idempotents("random")
                    sage: A._test_orthogonal_idempotents(dec)
                """
                from sage.combinat.permutation import Permutations
                monoid = self.basis().keys()
                if idm_list is None:
                    idm_list = monoid.idempotents()
                elif idm_list == "random":
                    idm_list = Permutations(monoid.idempotents()).random_element()
                res = {}
                sum1_idm = self.one() # 1-sum(idm)
                for idm in idm_list:
                    fi = (sum1_idm*self.g(idm)*sum1_idm).idempotent_lift()
                    res[idm] = fi
                    sum1_idm -=fi
                return Family(res)

            def orthogonal_idempotent_wrong(self, idempotent):
                return self.g(idempotent).pow_omega()

            @cached_method
            def orthogonal_idempotents_wrong(self):
                """
                OUTPUT:

                  -- A family of idempotents indexed by the idempotents of ``self``

                Returns a (conjectural) maximal decomposition of the
                identity into orthogonal idempotents

                Does not work: the obtained idempotents are not orthogonal

                EXAMPLES::

                    sage: Semigroups().JTrivial().Finite().example().algebra(QQ).orthogonal_idempotents() # non deterministic
                    Finite family {...}
                """
                monoid = self.basis().keys()
                return Family(monoid.idempotents(), self.orthogonal_idempotent)

            # TODO: move to FiniteDimensionalAlgebrasWithBasis
            def _test_orthogonal_idempotents(self, idempotents = None, **options):
                """
                Tests that :meth:`orthogonal_idempotents` returns a
                decomposition of the identity into orthogonal
                idempotents.

                TODO: check that it is maximal when the number and
                dimension of the simple modules is known.

                EXAMPLES::

                    sage: Semigroups().JTrivial().Finite().example().algebra(QQ)._test_orthogonal_idempotents()

                .. see also:: :class:`TestSuite`.
                """
                tester = self._tester(**options)
                if idempotents is None:
                    idempotents = self.orthogonal_idempotents()
                for e in idempotents:
                    tester.assert_(e.is_idempotent())
                    for f in idempotents:
                        if e == f: continue
                        tester.assert_((e*f).is_zero())
                tester.assert_((self.sum(idempotents) - 1).is_zero())

            @cached_method
            def radical_basis(self, n = 1):
                """
                Returns a basis for the n-th iterated radical.

                EXAMPLES::

                    sage: M = Semigroups().JTrivial().Finite().example()
                    sage: W = CoxeterGroup(["A",3], implementation = "permutation")
                    sage: from sage.monoids.automatic_semigroup import AutomaticMonoid
                    sage: M = AutomaticMonoid(W.simple_projections(), W.one(), by_action=True, category=Monoids().JTrivial().Finite())
                    sage: A = M.algebra(QQ)
                    sage: A.radical_basis(10)

                .. todo:: cut out a separate method
                radical_filtration_basis (or something similar), and
                generalize it for any finite dimensional algebra.
                """
                if n == 0:
                    return self.basis().list()
                if n == 1:
                    monoid = self.basis().keys()
                    res = [self.term(x) - self.term(x.pow_omega()) for
                            x in monoid.non_idempotents()]
                else:
                    from sage.matrix.constructor import matrix
                    basis_rad = self.radical_basis()
                    basis_rad_n1 = self.radical_basis(n-1)
                    # TODO: for J-Trivial monoids, we could just
                    # multiply by the elements of the quiver, since we
                    # know how to compute them combinatorially
                    new_basis = matrix([(a*b).to_vector()
                                        for a in basis_rad
                                        for b in basis_rad_n1])
                    new_basis = new_basis.row_space().basis()
                    res = map(self.from_vector, new_basis)
                return res

            @cached_method
            def cartan_matrix_by_hands(self):
                """
                EXAMPLES::

                    sage: M = Semigroups().JTrivial().Finite().example()
                    sage: A = M.algebra(QQ)
                    sage: M.cartan_matrix_as_table()
                    {([1], [3]): 1, ([3], [3]): 1, ([1], [2]): 1, ([2, 1], [1, 3]): 1, ([2, 1], [3, 2]): 1, ([2], [2]): 1, ([], []): 1, ([3, 2], [3, 2]): 1, ([3, 2, 1], [3, 2, 1]): 1, ([1, 3], [1, 3]): 1, ([1, 3], [3, 2]): 1, ([2], [3]): 1, ([2, 1], [2, 1]): 1, ([1], [1]): 1}
                    sage: A.cartan_matrix_by_hands()
                    {([3, 2], [3, 2]): 1, ([3], [3]): 1, ([1], [2]): 1, ([2, 1], [1, 3]): 1, ([2, 1], [3, 2]): 1, ([1], [3]): 1, ([1, 3], [1, 3]): 1, ([2], [2]): 1, ([3, 2, 1], [3, 2, 1]): 1, ([1, 3], [3, 2]): 1, ([2], [3]): 1, ([], []): 1, ([2, 1], [2, 1]): 1, ([1], [1]): 1}
                """
                from sage.matrix.constructor import matrix
                result = dict()
                print("Orthog idemps ...")
                idempotents = self.orthogonal_idempotents()
                print("Done")
                for x in idempotents.keys():
                    print(x)
                    for y in idempotents.keys():
                        res = len(
                            matrix([(idempotents[x]*v*idempotents[y]).to_vector()
                                    for v in self.basis()]).row_space().basis())
                        if res != 0:
                            result[x,y] = res
                return result


        class ElementMethods:

            # TODO: remove once a generic pow_omega will be available for any semigroup
            def pow_omega(self):
                """
                INPUT:

                 - ``self``: a pseudo idempotent

                Returns `self^\infty`

                Caveat: this implementation won't terminate if ``self`` is of infinite order

                """
                a,b = self.pseudo_order()
                assert a-b == 1
                return self ** b

            pow_infinity = pow_omega 

            def idempotent_lift(self):
                """
                INPUT:

                 - ``self`` - an ultimately idempotent `x(x-1)` is nilpotent.

                returns the idempotent where the nilpotent part is removed.

                Caveat: there is no check that self is ultumately idempotent
                and if not the implementation won't terminate.
                """
                res = self
                res2 = res*res
                while res2 != res:
                    res = 2*res2 - res2*res2
                    res2 = res*res
                return res

    class CharacterRings(CharacterRingsCategory):

        class WithRealizations(WithRealizationsCategory):

            class ParentMethods:

                def __init_extra__(self):

                    if self._q == self.base_ring().one():
                        self.PtoS = self.P().module_morphism(on_basis = self.PtoS_on_basis, codomain = self.S(), category = self.character_ring_category())
                        self.PtoS.register_as_coercion()
                        # This is not always invertible!!!
                        (~(self.PtoS)).register_as_coercion()

                        self.EtoS = self.E().module_morphism(on_basis = self.EtoS_on_basis, codomain = self.S(), category = self.character_ring_category())
                        self.EtoS.register_as_coercion()
                        (~(self.EtoS)).register_as_coercion()

                        self.StoC = self.S().module_morphism(on_basis = self.StoC_on_basis, codomain = self.C(), category = self.character_ring_category())
                        self.StoC.register_as_coercion()
                        (~(self.StoC)).register_as_coercion()

                def C(self):
                    r"""
                    Return the character ring of the monoid ``self`` on
                    the basis indexed by the class functions of (conjugacy
                    classes of) idempotents. I.e. if `Xhi = \sum c_e C_e`,
                    the `c_e` is the character of the idempotent `e` on
                    the corresponding representation.

                    EXAMPLES::

                        sage: M = Semigroups().JTrivial().Finite().example()
                        sage: M.character_ring().C()
                        Character ring of The (automatic) monoid with generators Finite family {1: [1], 2: [2], 3: [3]} over Integer Ring in the basis of characters of class functions modules
                    """
                    from sage_semigroups.monoids.character_ring import CharacterRing
                    return CharacterRing(self, prefix = "C", modules = "class functions") # todo: fix the name


                @cached_method
                def StoC_on_basis(self, i):
                    r"""
                    INPUT:

                      - ``i`` -- the index of a `J`-class of idempotents

                    Returns the character on the `i`-th simple module of
                    all the idempotents. The character of an idempotent
                    `e` is `1` if `e\geq_J e_i` and `0` otherwise.

                    EXAMPLES::

                        sage: M = Semigroups().JTrivial().Finite().example()
                        sage: S = M.character_ring().S()
                        sage: C = M.character_ring().C()
                        sage: for chi in S.basis():
                        ...       print(chi, "=", C(chi)) # indirect doctest
                        S[0] = C[0] + C[1] + C[2] + C[3] + C[4] + C[5] + C[6] + C[7]
                        S[1] = C[1] + C[2]
                        S[2] = C[2]
                        S[3] = C[1] + C[2] + C[3] + C[6]
                        S[4] = C[1] + C[2] + C[4] + C[7]
                        S[5] = C[2] + C[5] + C[6] + C[7]
                        S[6] = C[2] + C[6]
                        S[7] = C[2] + C[7]
                    """
                    j_poset = self.base().j_poset_on_regular_classes()
                    return self.C().sum_of_monomials(j for j in j_poset.principal_order_filter(i))

                @cached_method
                def PtoS_on_basis(self, i):
                    """
                    INPUT:

                      - ``i`` -- the index of a `J`-class of idempotents

                    Returns the character of the right projective module
                    `P_i` expressed in the simple module basis.

                    Caveat: THIS DOES NOT COMPUTE THE q-CHARACTER!!!!

                    EXAMPLES::

                        sage: M = Semigroups().JTrivial().Finite().example()
                        sage: P = M.character_ring().P()
                        sage: S = M.character_ring().S()
                        sage: for e in P.basis():
                        ...       print(e, "=", S(e))# indirect doctest
                        P[0] = S[0]                  # not fully checked; seems consistent with the cartan matrix
                        P[1] = S[1] + S[5]
                        P[2] = S[1] + S[2] + S[5]
                        P[3] = S[3] + S[4] + S[6]
                        P[4] = S[4] + S[6]
                        P[5] = S[5]
                        P[6] = S[6]
                        P[7] = S[7]

                    TODO: make the ordering consistent with the cartan matrix::

                        sage: M.cartan_matrix()
                        [1 0 0 0 0 0 0 0]
                        [0 1 1 1 0 0 0 0]
                        [0 0 1 1 0 0 0 0]
                        [0 0 0 1 0 0 0 0]
                        [0 0 0 0 1 0 1 0]
                        [0 0 0 0 1 1 1 0]
                        [0 0 0 0 0 0 1 0]
                        [0 0 0 0 0 0 0 1]

                    This requires making self.idempotents() and
                    self.j_transversal_of_idempotents() consistent /
                    identical.

                    """
                    assert self._q == self.base_ring().one()
                    M = self.base()
                    e = M.j_transversal_of_idempotents()[i]
                    side = self.side()
                    return self.S().sum_of_monomials(x.symbol_index(side) for x in M.projective_module(e, side))

                @cached_method
                def EtoS_on_basis(self, i):
                    """
                    INPUT:

                      - ``i`` -- the index of a `J`-class of idempotents

                    Returns the character of the right module generated by
                    e[i], for e in the given J-class of idempotents,
                    expressed in the simple module basis. As for any
                    module generated by an element of the monoid, this is
                    given by looking at the right symbols of the elements
                    in this module.

                    .. warning:: THIS DOES NOT COMPUTE THE q-CHARACTER!!!!

                    .. todo:: make this work for both left and right modules

                    EXAMPLES::

                        sage: M = Semigroups().JTrivial().Finite().example()
                        sage: E = M.character_ring().E()
                        sage: S = M.character_ring().S()
                        sage: for e in E.basis():
                        ...       print(e, "=", S(e))# indirect doctest
                        E[0] = S[0] + S[2] + S[3] + S[4] + S[6] + 2*S[7]
                        E[1] = S[0] + S[1] + S[2] + S[3] + 2*S[4] + S[6] + 2*S[7]
                        E[2] = S[2] + S[4] + S[6] + 2*S[7]
                        E[3] = S[3] + S[4] + S[6] + S[7]
                        E[4] = S[4] + S[6] + S[7]
                        E[5] = 2*S[0] + S[1] + 3*S[2] + S[3] + 2*S[4] + S[5] + S[6] + 3*S[7]
                        E[6] = S[6]
                        E[7] = S[6] + S[7]

                    It is a piece of luck that the coefficients are +-1 in
                    inverse morphism; it does not work for the BiHeckeMonoid::

                        sage: for e in S.basis():
                        ...       print(e, "=", E(e))
                        S[0] = E[0] - E[2] - E[3] + E[4]
                        S[1] = -E[0] + E[1] - E[4] + E[7]
                        S[2] = E[2] - E[4] + E[6] - E[7]
                        S[3] = E[3] - E[4]
                        S[4] = E[4] - E[7]
                        S[5] = -E[0] - E[1] - E[2] + E[3] + E[4] + E[5] - E[6] + E[7]
                        S[6] = E[6]
                        S[7] = -E[6] + E[7]
                    """
                    assert self._q == self.base_ring().one()
                    M = self.base()
                    e = M.j_transversal_of_idempotents()[i]
                    side = "right"
                    return self.S().sum_of_monomials(x.symbol_index(side) for x in e.ideal(side))
