r"""
FiniteHTrivialSemigroups

::

    sage: import sage_semigroups    # random
"""
#*****************************************************************************
#  Copyright (C) 2009-2011 Nicolas M. Thiery <nthiery at users.sf.net>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************

from sage.misc.cachefunc import cached_method#, cached_function
from sage.categories.category_with_axiom import CategoryWithAxiom
from sage.categories.semigroups import Semigroups
from sage.categories.modules import Modules
# from sage.categories.module_functor import ModulesCategory
# from sage.categories.algebra_functor import AlgebrasCategory
# from sage.categories.character_ring_functor import CharacterRingsCategory
# from sage.categories.set_with_action_functor import SetsWithActionCategory
#from sage.categories.realizations import RealizationsCategory
#from sage.categories.with_realizations import WithRealizationsCategory
from sage.sets.family import Family

class FiniteHTrivialSemigroups(CategoryWithAxiom):
    r"""

    The category of (multiplicative) aperiodic finite semigroups,
    i.e. finite semigroups such that for any element `x`, the sequence
    `x,x^2,x^3,...` eventually stabilizes.

    In terms of variety, this can be described by the equation `x^\omega x = x`.

    EXAMPLES::

        sage: Semigroups().HTrivial().Finite()
        Category of finite aperiodic semigroups
        sage: Semigroups().HTrivial().Finite().super_categories()
        [Category of finite semigroups, Category of aperiodic semigroups]
        sage: Monoids().HTrivial().Finite().example()
        The finite H-trivial monoid of order preserving maps on {1, 2, 3}

    TESTS::

        sage: C = Semigroups().HTrivial().Finite()
        sage: TestSuite(C).run()
    """
    @cached_method
    def extra_super_categories(self):
        r"""
        EXAMPLES:

        Any aperiodic monoid is H-trivial::

            sage: Semigroups().Aperiodic().super_categories()
            [Category of h trivial semigroups]

        This methods implements the fact that reciprocally any finite
        H-trivial semigroup is aperiodic::

            sage: Semigroups().HTrivial().Finite().extra_super_categories()
            [Category of aperiodic semigroups]

            sage: Semigroups().HTrivial().Finite().super_categories()
            [Category of finite semigroups, Category of aperiodic semigroups]

        .. seealso:: :meth:`sage.categories.adjective_category.AdjectiveCategory.extra_super_category`
        """
        return [Semigroups().Aperiodic()]

    class Unital(CategoryWithAxiom):
        def example(self, *args):
            from sage_semigroups.categories.examples.finite_h_trivial_monoids import Example
            return Example(*args)

    class ParentMethods:

        def simple_modules_index_set(self):
            """
            Return an indexing set for the simple modules of ``self``

            This indexing set is sorted decreasingly along `J`-order.
            This default implementation uses the same indexing set as
            for the j_classes, as given by::
            :meth:`Semigroups.Finite.ParentMethods.regular_j_classes_keys`.

            EXAMPLES::

                sage: S = Monoids().HTrivial().Finite().example(5); S 
                The finite H-trivial monoid of order preserving maps on {1, 2, 3, 4, 5}
                sage: S.simple_modules_index_set()
                {0, 1, 2, 3, 4}
            """
            result = self.j_transversal_of_idempotents().keys()
            if isinstance(result, list):
                from sage.sets.finite_enumerated_set import FiniteEnumeratedSet
                result = FiniteEnumeratedSet(result)
            return result

        def eggbox_picture(self, i):
            r"""
            The eggbox picture of a regular `J` class.

            INPUT:

             - ``i``: the index of some regular `J`-class of this semigroup

            Let `J` be the regular `J`-class indexed by `i`, and let
            `L` and `R` be respectively the left and right classes of
            `J` containing the canonical idempotent representative of
            the `J` class (see :meth:`lr_regular_class`). Then,

            .. math: J = \{ l * r, l \in L, r\in R \}

            with all products being distinct.

            This constructs a matrix `M`, where the cell (i,j)
            corresponds to the element `l[i]*r[i]` of `J`. Each row of
            `M` corresponds to a left class of `J`, while each column
            corresponds to a right class. The entry is `1` if the
            `l[i]*r[i]` is idempotent, and `0` otherwise. Each column
            and each row is garanteed to contain at least a `1`.

            The monoid induced by ``self`` on `J\cup 0` is an
            aperiodic Rees matrix monoid with `0`, whose structure is
            encoded by `M`. See :class:`AperiodicReesMatrixMonoid`.

            EXAMPLES::

                sage: S = Monoids().Aperiodic().Finite().example(5); S
                The finite H-trivial monoid of order preserving maps on {1, 2, 3, 4, 5}
                sage: S.eggbox_picture(2)
                [0 0 0 0 0 1]
                [1 1 1 1 0 0]
                [0 0 1 1 1 0]
                [0 1 0 0 0 0]
                [1 0 0 0 0 1]
                [1 1 0 0 0 0]
                [0 0 1 0 1 0]
                [0 0 0 0 1 0]
                [1 0 0 1 0 1]
                [0 1 1 0 0 0]

            TODO: should this method be just called eggbox?
            """
            l_class = self.lr_regular_class(i, side='left' )
            r_class = self.lr_regular_class(i, side='right')
            from sage.matrix.constructor import matrix
            return matrix( [ [ 1 if (l * r).is_idempotent() else 0
                               for r in r_class ]
                             for l in l_class ] )

        @cached_method
        def regular_j_class_semigroup_generators(self, i):
            """
            Semigroup generators for a regular `J` class

            INPUT:

             - ``i``: the index of some regular `J`-class `J` of this semigroup

            This returns a set of semigroup generators of `J`. This is
            currently the union of the left and right classes of `J`
            returned by :meth:`lr_regular_class`.

            EXAMPLES::

                sage: S = Monoids().Aperiodic().Finite().example(5); S
                The finite H-trivial monoid of order preserving maps on {1, 2, 3, 4, 5}
                sage: S.regular_j_class_semigroup_generators(0)
                {12345}
                sage: S.regular_j_class_semigroup_generators(1)
                {11235, 23445, 12335, 12355, 12445, 12235, 12334, 13445}

            We check that, for any `J` class of `S`, the elements of
            `J` are products of two elements of the corresponding
            generating set::

                sage: for i in S.regular_j_classes_keys():
                ...       J = J = S.regular_j_class(i)
                ...       g = S.regular_j_class_semigroup_generators(i)
                ...       assert J == J.intersection(Set(l*r for l in g for r in g))

            TODO: check validity for any semigroup, and lift up accordingly
            """
            from sage.sets.set import Set
            l_class = self.lr_regular_class(i, side='left' )
            r_class = self.lr_regular_class(i, side='right')
            return Set(l_class).union(Set(r_class))

        @cached_method
        def simple_modules(self, **options):
            """
            Returns the simple modules of ``self``

            """
            def simple_module(i, **options):
                return self.simple_module(**options)
            return Family(self.simple_modules_index_set(), simple_module)

        @cached_method
        def simple_module_dimension(self, i):
            """
            The dimension of the simple module indexed by ``i``

            INPUT:

             - ``i``: the index of some `J`-class of this semigroup

            The dimension of this simple module is given by the rank
            of the egg box picture for the `J`-class indexed by `i`.

            .. todo:: specify a coefficient ring; for the moment `\QQ` is taken

            EXAMPLES::

                sage: S = Monoids().Aperiodic().Finite().example(5); S
                The finite H-trivial monoid of order preserving maps on {1, 2, 3, 4, 5}
                sage: S.simple_module_dimension(2)
                6
                sage: [S.simple_module_dimension(i) for i in S.simple_modules_index_set()]
                [1, 4, 6, 4, 1]

            .. seealso:: :meth:`eggbox_picture`
            """
            return self.eggbox_picture(i).rank()

        @cached_method
        def simple_module(self, i, side='right', base_ring = None, as_plain_free_module = False):
            r"""
            Construct the simple module `S_i`

            .. todo:: specify a coefficient ring; for the moment `\QQ` is taken

            INPUT:

             - ``i``: the index of some regular `J`-class of this semigroup
             - ``side``: 'left' or 'right' (default: 'right')
             - ``as_plain_free_module``: a boolean (default: False)

            In the following, we assume that side='right', and denote
            by `K` the base_ring, and write `L` and `R` for the left
            and right classes of this `J`-class chosen by
            :meth:`lr_regular_class_module`. Recall that all left
            (resp. right) classes are isomorphic, so this choice is
            mostly irrelevant.

            This implementation constructs the right simple module
            `S_i`, as the quotient of `KR` by its radical `\rad
            KR`. The radical `\rad KR` itself is constructed as the
            annihilator of `L`.

            If ``as_plain_free_module`` is True, the result is a plain
            quotient of the `K`-:class:`FreeModule`'s with basis
            indexed by `0,\dots,|R|`, without additional module
            structure (rationale: plain :class:`FreeModule` currently
            have some additional features, like subspace comparisons).

            EXAMPLES::

                sage: S = Monoids().Aperiodic().Finite().example(5); S
                The finite H-trivial monoid of order preserving maps on {1, .., 5}

            With this example, the simple modules coincide with the right class modules::

                sage: S.simple_module(2, as_plain_free_module = True)
                Vector space quotient V/W of dimension 6 over Rational Field where
                V: Vector space of dimension 6 over Rational Field
                W: Vector space of degree 6 and dimension 0 over Rational Field
                Basis matrix:
                []
                sage: [S.simple_module(i).dimension() for i in S.simple_modules_index_set()]
                [1, 4, 6, 4, 1]
                sage: [S.lr_regular_class(i).cardinality() for i in S.simple_modules_index_set()]
                [1, 4, 6, 4, 1]

            On the left, the situation is more interesting::

                sage: S.simple_module(2, side = 'left', as_plain_free_module = True)
                Vector space quotient V/W of dimension 6 over Rational Field where
                V: Vector space of dimension 10 over Rational Field
                W: Vector space of degree 10 and dimension 4 over Rational Field
                Basis matrix:
                [ 1  0  0  0  0  0  0  1 -1 -1]
                [ 0  1  0  0  1  0 -1 -1  0  0]
                [ 0  0  1  0  0  1 -1  0  0 -1]
                [ 0  0  0  1 -1 -1  1  1 -1  0]
                sage: [S.simple_module(i, side='left').dimension() for i in S.simple_modules_index_set()]
                [1, 4, 6, 4, 1]
                sage: [S.lr_regular_class(i, side='left').cardinality() for i in S.simple_modules_index_set()]
                [1, 5, 10, 10, 5]

            See e.g. [Hivert_Thiery.HeckeGroup.2007]_ for the
            description of the representation theory of `S`.
            """
            if base_ring is None:
                from sage.rings.rational_field import QQ
                base_ring = QQ
            other_side = {'left':'right', 'right':'left'}[side]

            KR = self.lr_regular_class_module(i, side = side,     base_ring = base_ring)
            L  = self.lr_regular_class       (i, side = other_side)
            if as_plain_free_module:
                RR = KR.vectors_parent() # R, as a FreeModule
                Rad = KR.annihilator_of_subsemigroup(L)
                return RR.quotient(Rad)
            else:
                RadBasis = KR.annihilator_basis(L, action = KR.action, side='left')
                # TODO: improve the category to only require:
                # self.category().Modules(base_ring).FiniteDimensional().Quotients().WithBasis()
                return KR.quotient(RadBasis,
                                   category = (self.category().Modules(base_ring).Quotients(),
                                              Modules(base_ring).WithBasis().FiniteDimensional()))

        @cached_method
        def composition_series_poset(self, side = 'right'):
            """
            Experimental, and apparently broken ...

            EXAMPLES::

                sage: S = Monoids().Aperiodic().Finite().example(5); S
                The finite H-trivial monoid of order preserving maps on {1, 2, 3, 4, 5}
                sage: P = S.composition_series_poset(side = 'right')
                sage: list(P)
                [4, 3, 2, 1, 0]
                sage: P.cover_relations()
                []
                sage: P = S.composition_series_poset(side = 'left')
                sage: list(P)
                [4, 3, 2, 1, 0]
                sage: P.cover_relations()
            """
            from sage.combinat.posets.posets import Poset
            Js = self.regular_j_classes_keys()
            principal_order_filters = {}
            for J in Js:
                R = self.lr_regular_class_module(J, side=side)
                principal_order_filters[J] = R.composition_series()
                import time
                print "%s  %s: %s %s %s"%(time.strftime("%H:%M:%S"), J, self.simple_module_dimension(J), R.dimension(), principal_order_filters[J])
            P = Poset( ( Js, lambda J1, J2: J2 in principal_order_filters[J1] ), facade = True )
            from sage.sets.set import Set
            assert all( Set( P.principal_order_filter(J) ) == principal_order_filters[J]
                        for J in Js )
            return P

        @cached_method
        def cartan_matrix_as_table(self):
            r"""
            Returns the Cartan invariant matrix for ``self``

            OUTPUT:

             - a table mapping pairs to nonnegative integers

            EXAMPLES::

                sage: M = Monoids().HTrivial().Finite().example(4); M
                The finite H-trivial monoid of order preserving maps on {1, .., 4}
                sage: sorted(M.cartan_matrix_as_table().iteritems())
                [((0, 0), 1), ((0, 1), 1), ((1, 1), 1), ((1, 2), 1), ((2, 2), 1), ((2, 3), 1), ((3, 3), 1)]
            """
            result = dict()
            GL = self.character_ring(side='left')
            SL = GL.S(); TL = GL.T_all(); # CL= GL.C()
            GR = self.character_ring(side='right')
            SR = GR.S(); TR = GR.T_all(); # CR= GR.C()
            for j in self.simple_modules_index_set():
                #print "Calculating the character of the left simple module %s"%j
                #print "%s = %s"%(SL[j], CL(SL[j]))
                #print "Calculating the character of the right simple module %s"%j
                #print "%s = %s"%(SR[j], CR(SR[j]))
                pass
            for j in self.j_classes().keys():
                #print "Calculating the composition factors of the left class module %s"%j
                L = SL(TL[j])  # The composition factors for the left  class module of this J-class
                #print "%s = %s"%(TL[j], L)
                #print "Calculating the composition factors of the right class module %s"%j
                R = SR(TR[j])  # The composition factors for the right class module of this J-class
                #print "%s = %s"%(TR[j], R)
                for (jl, cl) in L:
                    for (jr, cr) in R:
                        result[jl,jr] = result.get((jl,jr), 0) + cl * cr
            return result

        # Basically a dup from J-Trivial monoids
        @cached_method
        def cartan_matrix(self, q = None):
            """
            EXAMPLES::

                sage: M = Monoids().HTrivial().Finite().example(4); M
                The finite H-trivial monoid of order preserving maps on {1, .., 4}
                sage: M.cartan_matrix()
                [1 1 0 0]
                [0 1 1 0]
                [0 0 1 1]
                [0 0 0 1]


            """
            from sage.combinat.ranker import rank_from_list
            index_set = list(self.simple_modules_index_set())
            rank = rank_from_list(index_set)
            from sage.matrix.constructor import matrix
            cartan_matrix = matrix(len(index_set), len(index_set), sparse=True)
            for (i,j),coeff in self.cartan_matrix_as_table().iteritems():
                cartan_matrix[rank(i), rank(j)] = coeff
            return cartan_matrix

    class ElementMethods:

        def pow_omega(self):
            """
            The omega power of ``self``.

            EXAMPLES::

                sage: S = Monoids().Aperiodic().Finite().example(5); S
                The finite H-trivial monoid of order preserving maps on {1, .., 5}
                sage: pi = S.semigroup_generators()

            For any element `x` of an aperiodic monoid, and the
            sequence `x,x^2,x^3,\dots` eventually stabilizes::

                sage: f = pi[4]*pi[3]*pi[2]*pi[1]
                sage: f.lift()
                map: 1 -> 1, 2 -> 1, 3 -> 2, 4 -> 3, 5 -> 4
                sage: (f^2).lift()
                map: 1 -> 1, 2 -> 1, 3 -> 1, 4 -> 2, 5 -> 3
                sage: (f^3).lift()
                map: 1 -> 1, 2 -> 1, 3 -> 1, 4 -> 1, 5 -> 2
                sage: (f^4).lift()
                map: 1 -> 1, 2 -> 1, 3 -> 1, 4 -> 1, 5 -> 1
                sage: (f^5).lift()
                map: 1 -> 1, 2 -> 1, 3 -> 1, 4 -> 1, 5 -> 1

            The limit of this sequence is traditionally denoted `x^\omega`::

                sage: f.pow_omega().lift()
                map: 1 -> 1, 2 -> 1, 3 -> 1, 4 -> 1, 5 -> 1

            It is always idempotent::

                sage: all(s.pow_omega().is_idempotent() for s in S)
                True
            """
            res_old = self
            res_new = res_old*res_old
            while res_old != res_new:
                res_old = res_new
                res_new = res_old*res_old
            return res_new

        pow_infinity = pow_omega # for backward compatibility

    # class CharacterRings(CharacterRingsCategory):

    #     class WithRealizations(WithRealizationsCategory):

    #         class ParentMethods:

    #             def __init_extra__(self):
    #                 """
    #                 TESTS::

    #                     sage: M = Monoids().HTrivial().Finite().example(4); M
    #                     The finite H-trivial monoid of order preserving maps on {1, .., 4}
    #                     sage: G = M.character_ring()
    #                     sage: C = G.C(); S = G.S(); T_all = G.T_all(); T = G.T()
    #                     sage: StoC = C.coerce_map_from(S)
    #                     sage: StoC._test_triangular()
    #                     sage: CtoS = S.coerce_map_from(C)
    #                     sage: CtoS._test_triangular()
    #                     sage: TtoS = C.coerce_map_from(T)
    #                     sage: TtoS._test_triangular()
    #                 """
    #                 self.StoC = self.S().module_morphism(on_basis = self.StoC_on_basis,
    #                                                      triangular = "upper", unitriangular = True, cmp = self.C().get_order_cmp(),
    #                                                      codomain = self.C(),
    #                                                      category = self.character_ring_category())
    #                 self.StoC.register_as_coercion()
    #                 (~(self.StoC)).register_as_coercion()

    #                 # Everything below is just for q=1!

    #                 self.T_alltoC = self.T_all().module_morphism(on_basis = self.T_alltoC_on_basis,
    #                                                              codomain = self.C(),
    #                                                              category = self.character_ring_category())
    #                 self.T_alltoC.register_as_coercion()

    #                 # Could implement T -> T_all by relabelling
    #                 self.TtoC = self.T().module_morphism(on_basis = self.TtoC_on_basis,
    #                                                      triangular = "upper", unitriangular = True, cmp = self.C().get_order_cmp(),
    #                                                      codomain = self.C(),
    #                                                      category = self.character_ring_category())
    #                 self.TtoC.register_as_coercion()
    #                 (~(self.TtoC)).register_as_coercion()

    #                 self.PtoS = self.P().module_morphism(on_basis = self.PtoS_on_basis,
    #                                                      codomain = self.S(),
    #                                                      category = self.character_ring_category())
    #                 self.PtoS.register_as_coercion()
    #                 # TODO: reenable this when the inverse will be computed lazily
    #                 # Right now we get a recursion loop
    #                 #(~(self.PtoS)).register_as_coercion()

    #                 # TODO: could also do EtoC when q == 1

    #             def dimension(self, chi):
    #                 """
    #                 Return the dimension of the representation with the character chi

    #                 EXAMPLES::

    #                     sage: M = Monoids().HTrivial().Finite().example(); M
    #                     The finite H-trivial monoid of order preserving maps on {1, .., 3}
    #                     sage: G = M.character_ring(side = "left"); G
    #                     The left-character ring of The finite H-trivial monoid of order preserving maps on {1, .., 3} over Rational Field

    #                 This is the dimension of the simple module indexed by ``1``::

    #                     sage: S = G.S()
    #                     sage: G.dimension(S[1])
    #                     2

    #                 As a shortcut, one can also use::

    #                     sage: S[1].dimension()
    #                     2

    #                 Let us look at the dimension of all simple and left class modules::

    #                     sage: for chi in G.S().basis():
    #                     ...       print "dim %s = %s"%(chi, G.dimension(chi))
    #                     dim S[0] = 1
    #                     dim S[1] = 2
    #                     dim S[2] = 1

    #                     sage: for chi in G.T_all().basis():
    #                     ...       print "dim %s = %s"%(chi, G.dimension(chi))
    #                     dim T[0] = 1
    #                     dim T[1] = 3
    #                     dim T[2] = 3
    #                 """
    #                 semigroup = self.base()
    #                 # The regular j_class of the identity
    #                 i = semigroup.j_transversal_of_idempotents().inverse_family()[semigroup.one()]
    #                 return self.C()(chi)[i]

    #             @cached_method
    #             def C(self):
    #                 r"""
    #                 The character ring of the monoid ``self`` on the class function basis

    #                 The basis is indexed by the class functions of
    #                 `J`-classes of idempotents. I.e., if `M` is a module,
    #                 then `\Chi(M) = \sum c_i C_i`, where `c_i` is the
    #                 character (i.e. the trace) on `M` of any idempotent
    #                 `e` in the regular `J`-class indexed by `i`.

    #                 For triangularity purposes, the basis is sorted
    #                 decreasingly along a linear extension of `J`-order.

    #                 .. seealso:: :meth:`simple_modules_index_set`

    #                 EXAMPLES::

    #                     sage: M = Monoids().HTrivial().Finite().example(); M
    #                     The finite H-trivial monoid of order preserving maps on {1, .., 3}
    #                     sage: C = M.character_ring().C(); C
    #                     The right-character ring of The finite H-trivial monoid of order preserving maps on {1, .., 3} over Rational Field in the basis of characters of right-class functions modules
    #                     sage: C.basis()
    #                     Finite family {0: C[0], 1: C[1], 2: C[2]}
    #                 """
    #                 from sage.combinat.character_ring import CharacterRing
    #                 result = CharacterRing(self, prefix = "C", modules = "%s-class functions"%self.side()) # todo: fix the name
    #                 result.set_order(list(self.base().simple_modules_index_set()))
    #                 return result

    #             @cached_method
    #             def T(self):
    #                 """
    #                 Return the ring of characters of regular left/right-class modules

    #                 EXAMPLES::

    #                     sage: M = Monoids().HTrivial().Finite().example(); M
    #                     The finite H-trivial monoid of order preserving maps on {1, .., 3}
    #                     sage: T = M.character_ring().T(); T
    #                     The right-character ring of The finite H-trivial monoid of order preserving maps on {1, .., 3} over Rational Field in the basis of characters of regular right-class modules
    #                     sage: T.basis()
    #                     Finite family {0: T[0], 1: T[1], 2: T[2]}
    #                     sage: for chi in T.basis():
    #                     ...       print "dim %s = %s"%(chi, chi.dimension())
    #                     dim T[0] = 1
    #                     dim T[1] = 2
    #                     dim T[2] = 1
    #                 """
    #                 from sage.combinat.character_ring import CharacterRing
    #                 return CharacterRing(self, prefix = "T",
    #                                      modules = "regular %s-class"%self.side())

    #             @cached_method
    #             def T_all(self):
    #                 """
    #                 Return the ring of characters of left/right-class modules

    #                 .. note:: This includes both regular and non regular
    #                     modules. So this is in general not isomorphic to
    #                     the other character rings, and the indexing set
    #                     may be completely unrelated.

    #                 .. todo:: add a good example, and find a good name

    #                 EXAMPLES::

    #                 """
    #                 from sage.combinat.character_ring import CharacterRing
    #                 from sage.sets.finite_enumerated_set import FiniteEnumeratedSet
    #                 return CharacterRing(self, prefix = "T",
    #                                      modules = "%s-class"%self.side(),
    #                                      index_set = FiniteEnumeratedSet(self.base().j_classes().keys()))

    #             @cached_method
    #             def StoC_on_basis(self, i):
    #                 """
    #                 INPUT:

    #                   - ``i`` -- the index of a regular `J`-class

    #                 Returns the character of all the (`J`-classes of)
    #                 idempotents on the `i`-th simple module.

    #                 EXAMPLES::

    #                     sage: M = Monoids().HTrivial().Finite().example(); M
    #                     The finite H-trivial monoid of order preserving maps on {1, .., 3}
    #                     sage: G = M.character_ring()
    #                     sage: G.StoC_on_basis(1)
    #                     2*C[0] + C[1]

    #                     sage: S = G.S(); C = G.C()
    #                     sage: for chi in S.basis():
    #                     ...       print chi, "=", C(chi)
    #                     S[0] = C[0]
    #                     S[1] = 2*C[0] + C[1]
    #                     S[2] = C[0] + C[1] + C[2]

    #                 The character of simple modules is the same on the
    #                 left and on the right::

    #                     sage: G = M.character_ring(side = "left")
    #                     sage: S = G.S(); C = G.C()
    #                     sage: for chi in S.basis():
    #                     ...       print chi, "=", C(chi)
    #                     S[0] = C[0]
    #                     S[1] = 2*C[0] + C[1]
    #                     S[2] = C[0] + C[1] + C[2]

    #                     sage: for chi in C.basis():
    #                     ...       print chi, "=", S(chi)
    #                     C[0] = S[0]
    #                     C[1] = -2*S[0] + S[1]
    #                     C[2] = S[0] - S[1] + S[2]

    #                 """
    #                 chi = self.base().simple_module(i, side = "right", base_ring = self.modules_base_ring()).character()
    #                 if self.side() == 'left':
    #                     chi = self.C().sum_of_terms(chi)
    #                 return chi

    #             @cached_method
    #             def T_alltoC_on_basis(self, i):
    #                 """
    #                 INPUT:

    #                   - ``i`` -- the index of a `J`-class

    #                 Returns the character of all the (`J`-classes of)
    #                 idempotents on the left (resp. right) class module for
    #                 the `J`-class indexed by ``i``.

    #                 .. todo:: update the examples here with a monoid
    #                 with non regular `J`-classes.

    #                 EXAMPLES::

    #                     sage: M = Monoids().HTrivial().Finite().example(); M
    #                     The finite H-trivial monoid of order preserving maps on {1, .., 3}
    #                     sage: side = "right"
    #                     sage: [list(M.lr_class(i, side=side)) for i in [0,1,2]]
    #                     [[123], [113, 133], [111]]
    #                     sage: G = M.character_ring(side=side)
    #                     sage: G.T_alltoC_on_basis(1)
    #                     2*C[0] + C[1]
    #                     sage: C = G.C(); T = G.T_all(); S = G.S()
    #                     sage: for chi in T.basis():
    #                     ...       print chi, "=", C(chi)
    #                     T[0] = C[0]
    #                     T[1] = 2*C[0] + C[1]
    #                     T[2] = C[0] + C[1] + C[2]

    #                 The decomposition of right class modules into simple modules::

    #                     sage: for chi in T.basis():
    #                     ...       print chi, "=", S(chi)
    #                     T[0] = S[0]
    #                     T[1] = S[1]
    #                     T[2] = S[2]

    #                 We redo the same calculations on the left::

    #                     sage: side = "left"
    #                     sage: [list(M.lr_class(i, side=side)) for i in [0,1,2]]
    #                     [[123], [133, 233, 122], [111, 222, 333]]
    #                     sage: G = M.character_ring(side=side)
    #                     sage: G.T_alltoC_on_basis(1)
    #                     3*C[0] + C[1]

    #                     sage: C = G.C(); T = G.T_all(); S = G.S()
    #                     sage: for chi in T.basis():
    #                     ...       print chi, "=", C(chi)
    #                     T[0] = C[0]
    #                     T[1] = 3*C[0] + C[1]
    #                     T[2] = 3*C[0] + 2*C[1] + C[2]

    #                 The decomposition of left class modules into simple modules::

    #                     sage: for chi in T.basis():
    #                     ...       print chi, "=", S(chi)
    #                     T[0] = S[0]
    #                     T[1] = S[0] + S[1]
    #                     T[2] = S[1] + S[2]
    #                 """
    #                 return self.base().lr_class(i, side = self.side()).algebra(self.modules_base_ring()).character()

    #             @cached_method
    #             def TtoC_on_basis(self, i):
    #                 """
    #                 INPUT:

    #                   - ``i`` -- the index of a `J`-class

    #                 Returns the character of all the (`J`-classes of)
    #                 idempotents on the left (resp. right) class module
    #                 for the regular `J`-class indexed by ``i``.

    #                 EXAMPLES::

    #                     sage: M = Monoids().HTrivial().Finite().example(); M
    #                     The finite H-trivial monoid of order preserving maps on {1, .., 3}
    #                     sage: side = "right"
    #                     sage: [list(M.lr_class(i, side=side)) for i in [0,1,2]]
    #                     [[123], [113, 133], [111]]
    #                     sage: G = M.character_ring(side=side)
    #                     sage: G.TtoC_on_basis(1)
    #                     2*C[0] + C[1]
    #                     sage: C = G.C(); T = G.T(); S = G.S()
    #                     sage: for chi in T.basis():
    #                     ...       print chi, "=", C(chi)
    #                     T[0] = C[0]
    #                     T[1] = 2*C[0] + C[1]
    #                     T[2] = C[0] + C[1] + C[2]

    #                 The decomposition of right class modules into simple modules::

    #                     sage: for chi in T.basis():
    #                     ...       print chi, "=", S(chi)
    #                     T[0] = S[0]
    #                     T[1] = S[1]
    #                     T[2] = S[2]

    #                 We redo the same calculations on the left::

    #                     sage: side = "left"
    #                     sage: [list(M.lr_class(i, side=side)) for i in [0,1,2]]
    #                     [[123], [133, 233, 122], [111, 222, 333]]
    #                     sage: G = M.character_ring(side=side)
    #                     sage: G.TtoC_on_basis(1)
    #                     3*C[0] + C[1]

    #                     sage: C = G.C(); T = G.T(); S = G.S()
    #                     sage: for chi in T.basis():
    #                     ...       print chi, "=", C(chi)
    #                     T[0] = C[0]
    #                     T[1] = 3*C[0] + C[1]
    #                     T[2] = 3*C[0] + 2*C[1] + C[2]

    #                 The decomposition of left class modules into simple modules::

    #                     sage: for chi in T.basis():
    #                     ...       print chi, "=", S(chi)
    #                     T[0] = S[0]
    #                     T[1] = S[0] + S[1]
    #                     T[2] = S[1] + S[2]
    #                 """
    #                 return self.base().lr_regular_class(i, side = self.side()).algebra(self.modules_base_ring()).character()

    #             @cached_method
    #             def PtoS_on_basis(self, i):
    #                 """
    #                 Return the character of the left (resp. right) projective module indexed by ``i``, in terms of characters of simple modules.
    #                 INPUT:

    #                   - ``i`` -- the index of a regular `J`-class / simple / projective module

    #                 In other words, this gives the composition factors
    #                 in any maximal composition series of this
    #                 projective module.

    #                 EXAMPLES::

    #                     sage: W = WeylGroup(["A", 2])
    #                     sage: W.element_class.__repr__ = W.element_class.to_permutation_string
    #                     sage: M = BiHeckeMonoid(W); M
    #                     bi-Hecke monoid of Weyl Group of type ['A', 2] (as a matrix group acting on the ambient space)
    #                     sage: side = "right"

    #                     sage: G = M.character_ring(side=side)
    #                     sage: G.PtoS_on_basis(W.one())
    #                     S[321] + S[231] + S[312] + S[213] + S[132] + S[123]
    #                     sage: C = G.C(); P = G.P(); S = G.S()
    #                     sage: for chi in P.basis():
    #                     ...       print chi, "=", S(chi)
    #                     P[123] = S[321] + S[231] + S[312] + S[213] + S[132] + S[123]
    #                     P[213] = S[213]
    #                     P[132] = S[132]
    #                     P[312] = S[321] + S[312]
    #                     P[231] = S[321] + S[231]
    #                     P[321] = S[321]

    #                 We redo the same calculations on the left::

    #                     sage: side = "left"
    #                     sage: G = M.character_ring(side=side)
    #                     sage: G.PtoS_on_basis(W.one())
    #                     S[123]
    #                     sage: C = G.C(); P = G.P(); S = G.S()
    #                     sage: for chi in P.basis():
    #                     ...       print chi, "=", S(chi)
    #                     P[123] = S[123]
    #                     P[213] = S[213] + S[123]
    #                     P[132] = S[132] + S[123]
    #                     P[312] = S[312] + S[123]
    #                     P[231] = S[231] + S[123]
    #                     P[321] = S[321] + S[231] + S[312] + S[123]
    #                 """
    #                 M = self.base()
    #                 S = self.S()
    #                 if self.side() == 'left':
    #                     side = 0
    #                 else:
    #                     side = 1
    #                 return S.sum_of_terms( (t[1-side], c)
    #                                        for (t, c) in M.cartan_matrix_as_table().iteritems()
    #                                        if t[side] == i )

    #     class Realizations(RealizationsCategory):

    #         class ElementMethods:

    #             def dimension(self):

    #                 return self.parent().realization_of().dimension(self)


    # class SetsWithAction(SetsWithActionCategory):
    #     """
    #     EXAMPLES::

    #         sage: Monoids().HTrivial().Finite().SetsWithAction().Algebras(QQ).extra_super_categories()
    #         [Category of finite h trivial monoid modules over Rational Field]

    #     TESTS::

    #         sage: S = Monoids().HTrivial().Finite().example()
    #         sage: R = S.with_regular_action().algebra(QQ)
    #         sage: R.category().is_subcategory(Monoids().HTrivial().Finite().Modules(QQ))
    #         True
    #     """

    #     class Algebras(AlgebrasCategory):
    #         # see the warning in sage.categories.set_with_action_functor.SetsWithActionCategory._algebras_extra_super_categories
    #         extra_super_categories = SetsWithActionCategory._algebras_extra_super_categories.im_func

    # class Modules(ModulesCategory):

    #     # class FiniteDimensional ...

    #     class ParentMethods:

    #         def character(self):
    #             r"""
    #             Return the character of this module `M` in the `C` basis

    #             OUTPUT:

    #              - a linear combination `\chi(M) = \sum c_i C_i`, where
    #                `c_i` is the character (i.e. the trace) on `M` of any
    #                idempotent `e` in the regular `J`-class indexed by `i`.

    #             EXAMPLES::

    #                 sage: M = Monoids().HTrivial().Finite().example(); M
    #                 The finite H-trivial monoid of order preserving maps on {1, .., 3}
    #                 sage: M.rename("M")
    #                 sage: R = M.regular_representation(side = 'left')
    #                 sage: R.character()
    #                 10*C[0] + 4*C[1] + C[2]
    #                 sage: R.character().parent()
    #                 The left-character ring of M over Rational Field in the basis of characters of left-class functions modules

    #                 sage: R = M.regular_representation(side = 'right')
    #                 sage: R.character()
    #                 10*C[0] + 6*C[1] + 3*C[2]
    #                 sage: R.character().parent()
    #                 The right-character ring of M over Rational Field in the basis of characters of right-class functions modules
    #             """
    #             S = self.semigroup()
    #             C = S.character_ring(self.base_ring(), side = self.side()).C()
    #             base_ring = C.base_ring()
    #             e = S.j_transversal_of_idempotents()

    #             # Remark: let e and f be two idempotents, and identify
    #             # them with the corresponding linear projections
    #             # acting on ``self``. If e <=_J f, then the rank of e
    #             # is smaller than the rank of f.
    #             #
    #             # Corollary: the set of idempotents having non zero
    #             # character (the support below) is an upper ideal in J-order.
    #             #
    #             # We use this to avoid computing the character for all
    #             # regular J-classes.
    #             #
    #             # I am not yet sure that this works in non zero
    #             # characteristic, so let's be safe.
    #             assert self.base_ring().characteristic() == 0

    #             from sage.combinat.backtrack import TransitiveIdeal
    #             P = S.j_poset_on_regular_classes()
    #             @cached_function
    #             def character(i):
    #                 return self.character_of(e[i])
    #             def children(i):
    #                 return (j for j in P.lower_covers(i) if character(j))
    #             support = TransitiveIdeal(children, [P.top()])
    #             return C.sum_of_terms((i, base_ring(character(i))) for i in support)

    #         def composition_factors(self):
    #             r"""
    #             Return the composition factors this module

    #             OUTPUT:

    #              - a linear combination `\chi(M) = \sum c_i S_i`,
    #                where `c_i` is the number of composition factors of
    #                `M` isomorphic to the simple module `S_i`.

    #             EXAMPLES::

    #                 sage: M = Monoids().HTrivial().Finite().example(); M
    #                 The finite H-trivial monoid of order preserving maps on {1, .., 3}
    #                 sage: M.rename("M")
    #                 sage: R = M.regular_representation(side = 'left')
    #                 sage: R.composition_factors()
    #                 3*S[0] + 3*S[1] + S[2]
    #                 sage: R.composition_factors().parent()
    #                 The left-character ring of M over Rational Field in the basis of characters of simple left modules

    #                 sage: R = M.regular_representation(side = 'right')
    #                 sage: R.composition_factors()
    #                 S[0] + 3*S[1] + 3*S[2]
    #                 sage: R.composition_factors().parent()
    #                 The right-character ring of M over Rational Field in the basis of characters of simple right modules
    #             """
    #             chi = self.character()
    #             return chi.parent().realization_of().S()(chi)
