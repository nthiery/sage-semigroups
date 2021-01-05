# -*- encoding: utf-8 -*-
r"""
BiHecke Monoids

::

    sage: import sage_semigroups # random
"""
#*****************************************************************************
#  Copyright (C) 2009-2010 Nicolas M. Thiéry <nthiery at users.sf.net>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************

import operator
from sage.misc.cachefunc import cached_function, cached_method
from sage.misc.latex import latex
from sage.misc.lazy_attribute import lazy_attribute
from sage.misc.misc import attrcall
from sage.misc.misc_c import prod
from sage.categories.category import Category
from sage.categories.monoids import Monoids
from sage.categories.coxeter_groups import CoxeterGroups
from sage_semigroups.categories.character_ring_functor import CharacterRingsCategory
from sage.categories.with_realizations import WithRealizationsCategory
from sage.structure.unique_representation import UniqueRepresentation
from sage.sets.set import Set
from sage.sets.family import Family
from sage.sets.finite_enumerated_set import FiniteEnumeratedSet
from sage.sets.finite_set_maps import FiniteSetMaps
from sage.rings.rational_field import QQ
from sage.combinat.subset import Subsets
from sage.monoids.automatic_semigroup import AutomaticMonoid
from sage.combinat.backtrack import TransitiveIdeal
from sage.combinat.posets.posets import Poset
from sage.combinat.posets.lattices import LatticePoset
from sage.combinat.root_system.cartan_type import CartanType
from sage.combinat.root_system.weyl_group import WeylGroup
from sage.interfaces.gap import gap
from sage.structure.element import parent
from sage.combinat.permutation import Permutation
from sage.rings.integer_ring import ZZ

class BiHeckeMonoids(Category):

    def super_categories(self):
        return [Monoids().HTrivial().Finite()]

    class ParentMethods:

        @cached_method
        def e(self, a, b = None):
            """
            With a single argument `w` in ``self.W``, returns the unique
            idempotent in this monoid with image set `[1, w]_L`. With two
            arguments, return the idempotent `e_{a,b}` with image set `[a,b]_L`.

            EXAMPLES:

            Let us create the monoid, and force the initialization of the reduced words::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.BiHeckeMonoid(['A',3])
                sage: M.cardinality()
                477

            If w=1, then we get an idempotent with trivial image_set {1}::

                sage: p = M.e(M.W.one())
                sage: p.is_idempotent()
                True
                sage: M.e(M.W.one()).image_set() == set([M.W.one()])
                True

            If w=w_0, we get the identity::

                sage: p = M.e(M.W.w0)
                sage: p.is_idempotent()
                True
                sage: M.e(M.W.w0) == M.one()
                True

            For any w we get an idempotent::

                sage: all(M.e(w).is_idempotent() for w in M.W)
                True

            Here is a typical example::

                sage: w=M.lattice([1,0,3,2])
                sage: M.e(w)
                [-3, -1]

            In type A, it is also possible to create an idempotent from a permutation

                sage: M.e(Permutation([4,2,3,1]))
                [-2]
                sage: M.e(Permutation([3,4,1,2]))    # note: this is identical to [1, 3, -3, -1]
                [-3, -1]

            """
            assert(a in self.W)
            if b is None:
                w = a
                return self.piw(w**-1 * self.W.w0) * self.opiw(self.W.w0 * w)
            else:
                assert(b in self.W)
                return self.opiw(a**-1) * self.e(b*a**-1) * self.piw(a)

        def j_idempotent_representative(self, w):
            """
            Return a canonical idempotent representative for the regular
            J-class indexed by ``w``. This is the idempotent with image
            set `[w, w_0]_L`.

            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.BiHeckeMonoid(['A',2]); M.cardinality()
                sage: M.j_idempotent_representative(M.W.one())
                []
                sage: M.j_idempotent_representative(M.W.w0)
                [1, 2, 1]
            """
            return self.e(w, self.W.w0)

        def j_transversal_of_idempotents(self):
            """
            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.BiHeckeMonoid(['A',2])
                sage: M.j_transversal_of_idempotents()

                sage: M.simple_modules_index_set()
                Weyl Group of type ['A', 2] (as a matrix group acting on the ambient space)
            """
            W = sorted(self.W, key = attrcall("length"))
            return Family( W, self.j_idempotent_representative )

        def simple_module_dimension_cutting(self, w):
            t, simple, minimal_Js, blocks, intervals = simple_module_structure(w**-1*self.W.w0)
            return len(simple)

        def cartan_matrix_as_table_from_M0(self):
            """
            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.BiHeckeMonoid(["A",3])
                sage: M.cartan_matrix_as_table_from_M0() == M.cartan_matrix_as_table()
            """

            result = dict()
            GL = self.character_ring(side='left')
            GR = self.character_ring(side='right')
            SR = GR.S(); TR = GR.T(); CR= GR.C()
            M0 = self.fix_w0_monoid()
            G0 = M0.character_ring(side="left"); P0 = G0.P()
            for j in self.regular_j_classes().keys():
                L = SR(P0[j]) # The composition factors of the left M0-projective module for this J-class
                              # Note: doing it on the right or the left is equivalent, but
                              # S0 -> T (and thus P0->S0->T->S) is only implemented on the right
                R = SR(TR[j]) # The composition factors for the right class module of this J-class
                #print "%s = %s"%(TR[j], R)
                for (jl, cl) in L:
                    for (jr, cr) in R:
                        result[jl,jr] = result.get((jl,jr), 0) + cl * cr
            return result

    class CharacterRings(CharacterRingsCategory):
        r"""
        EXAMPLES::

            sage: import sage_semigroups.monoids.catalog as semigroups
            sage: QQ.<q> = QQ[]
            sage: W = WeylGroup(["A",3])
            sage: G = semigroups.BiHeckeMonoid(W).character_ring(q = q)
            sage: S = G.S()
            sage: T = G.T()
            sage: P = G.P()
            sage: S(T[p(3412)])
            q*S[1234] + S[3412]
            sage: T(S[p(3412)])
            -q*T[1234] + T[3412]

            sage: S(T[p(3421)])
            q^2*S[1234] + q*S[2341] + q*S[3412] + S[3421]

            sage: T(P[p(2143)])
            T[2143] + q*T[2341] + q*T[4123]
            sage: S(P[p(2143)])
            3*q^2*S[1234] + q*S[1243] + q*S[2134] + S[2143] + q*S[2341] + q*S[4123]

            sage: dim = S.module_morphism(lambda x: ZZ(dims[x]['simple']), codomain = S.base_ring())

            sage: for w in W:
            ...       assert G.dims[w]['translation'] == G.dim(S(T[w]))(1)
            ...       assert G.dims[w]['projective' ] == G.dim(S(P[w]))(1)


            sage: M = semigroups.BiHeckeMonoid(["A",2])
            sage: G = M.character_ring()
            sage: E = G.E(); T = G.T();
            sage: for e in E.basis():
            ...       print e, "=", T(e)
            E[123] = T[123] + T[132] + T[213] + 2*T[231] + 2*T[312] + T[321]
            E[213] = T[213] + T[231] + T[312] + T[321]
            E[231] = T[231] + T[321]
            E[321] = T[321]
            E[132] = T[132] + T[231] + T[312] + T[321]
            E[312] = T[312] + T[321]
        """

        class WithRealizations(WithRealizationsCategory):

            class ParentMethods:

                def __init_extra__(self):
                    """
                    EXAMPLES:

                    Calculating the decomposition of left projective
                    modules of M_0 into simple M modules::

                        sage: import sage_semigroups.monoids.catalog as semigroups
                        sage: W = WeylGroup(["A", 3])
                        sage: W.element_class.__repr__ = W.element_class.to_permutation_string
                        sage: M = semigroups.BiHeckeMonoid(W); M
                        bi-Hecke monoid of Weyl Group of type ['A', 2] (as a matrix group acting on the ambient space)
                        sage: M0 = M.fix_w0_monoid()
                        sage: G = M.character_ring(side="right"); S = G.S()
                        sage: G0 = M0.character_ring(side="left"); P0 = G0.P()
                        sage: for chi in P0.basis():
                        ...       print "%s = %s"%(chi, S(chi))
                        P[123] = S[123]
                        P[213] = S[213]
                        P[132] = S[132]
                        P[312] = S[312]
                        P[231] = S[231]
                        P[321] = S[321]

                    """

                    #self.TtoS = self.T().module_morphism(on_basis = self.TtoS_on_basis, codomain = self.S(), category = self.character_ring_category())
                    #self.TtoS.register_as_coercion()
                    #(~(self.TtoS)).register_as_coercion()

                    if self._q == self.base_ring().one():
                        self.EtoT = self.E().module_morphism(on_basis = self.EtoT_on_basis, codomain = self.T(), category = self.character_ring_category())
                        self.EtoT.register_as_coercion()
                        #(~(self.EtoT)).register_as_coercion()

                        self.CMtoC = self.CM().module_morphism(on_basis = self.CMtoC_on_basis,
                                                               triangular = "upper", unitriangular = True, key = self.C().get_order_key(),
                                                               codomain = self.C(),
                                                               category = self.character_ring_category())
                        self.CMtoC.register_as_coercion()
                        (~(self.CMtoC)).register_as_coercion()

                        if self.side() == "right":
                            M0 = self.base().fix_w0_monoid()
                            # FIXME: pass down the module base ring
                            S0 = M0.character_ring().S()
                            self.restrict_TtoS0 = self.T().module_morphism \
                                (on_basis = self.restrict_TtoS0_on_basis,
                                 triangular = "upper", unitriangular = True, cmp = S0.get_order_cmp(),
                                 codomain = S0)

                            self.restrict_TtoS0.register_as_coercion()
                            (~(self.restrict_TtoS0)).register_as_coercion()

                            S0left = M0.character_ring(side="left").S()
                            S0left.module_morphism(on_basis=S0.monomial).register_as_coercion()

                    if self.base().W == WeylGroup(["A",3]):
                        # hardcoded data for A3
                        T = self.T()
                        q = self._q
                        p = self.base().W.from_compact_permutation
                        PtoT = dict( (p, T[p]) for p in self.base().simple_modules_index_set())
                        PtoT[p(1243)] += q*(T[p(3412)])
                        PtoT[p(1324)] += q*(T[p(2341)] + T[p(4123)] + T[p(4231)])
                        PtoT[p(1432)] += q*(T[p(3412)])
                        PtoT[p(2134)] += q*(T[p(3412)])
                        PtoT[p(2143)] += q*(T[p(2341)] + T[p(4123)])
                        PtoT[p(3214)] += q*(T[p(3412)])

                        self.PtoT = self.P().module_morphism(on_basis = PtoT.__getitem__, codomain = self.T(), category = self.character_ring_category())
                        self.PtoT.register_as_coercion()
                        (~(self.PtoT)).register_as_coercion()

                        dims = {}
                        dims[p(1234)] = {'simple': 1, 'translation':  1, 'projective':  1}
                        dims[p(1243)] = {'simple': 1, 'translation':  2, 'projective':  8}
                        dims[p(1324)] = {'simple': 1, 'translation':  2, 'projective': 22}
                        dims[p(1342)] = {'simple': 2, 'translation':  3, 'projective':  3}
                        dims[p(1423)] = {'simple': 2, 'translation':  3, 'projective':  3}
                        dims[p(1432)] = {'simple': 1, 'translation':  6, 'projective': 12}
                        dims[p(2134)] = {'simple': 1, 'translation':  2, 'projective':  8}
                        dims[p(2143)] = {'simple': 1, 'translation':  4, 'projective': 12}
                        dims[p(2314)] = {'simple': 2, 'translation':  3, 'projective':  3}
                        dims[p(2341)] = {'simple': 3, 'translation':  4, 'projective':  4}
                        dims[p(2413)] = {'simple': 4, 'translation':  5, 'projective':  5}
                        dims[p(2431)] = {'simple': 4, 'translation':  8, 'projective':  8}
                        dims[p(3124)] = {'simple': 2, 'translation':  3, 'projective':  3}
                        dims[p(3142)] = {'simple': 4, 'translation':  5, 'projective':  5}
                        dims[p(3214)] = {'simple': 1, 'translation':  6, 'projective': 12}
                        dims[p(3241)] = {'simple': 4, 'translation':  8, 'projective':  8}
                        dims[p(3412)] = {'simple': 5, 'translation':  6, 'projective':  6}
                        dims[p(3421)] = {'simple': 3, 'translation': 12, 'projective': 12}
                        dims[p(4123)] = {'simple': 3, 'translation':  4, 'projective':  4}
                        dims[p(4132)] = {'simple': 4, 'translation':  8, 'projective':  8}
                        dims[p(4213)] = {'simple': 4, 'translation':  8, 'projective':  8}
                        dims[p(4231)] = {'simple': 5, 'translation': 12, 'projective': 12}
                        dims[p(4312)] = {'simple': 3, 'translation': 12, 'projective': 12}
                        dims[p(4321)] = {'simple': 1, 'translation': 24, 'projective': 24}
                        K = self.S().base_ring()
                        self.dims = dims
                        self.dim = self.S().module_morphism(lambda x: K(dims[x]['simple']), codomain = K)

                def T_disabled(self):
                    """
                    Return the character ring of the bi-Hecke monoid on the
                    basis indexed by its translation modules.

                    EXAMPLES::

                        sage: BiHeckeMonoid(["A",2]).character_ring().T()
                        Character ring of bi-Hecke monoid of Weyl Group of type ['A', 2] (as a matrix group acting on the ambient space) over Integer Ring in the basis of characters of translation modules
                    """
                    from sage_semigroups.monoids.character_ring import CharacterRing
                    return CharacterRing(self, prefix = "T", modules = "translation")

                def CM(self):
                    r"""
                    Return the character ring of the bi-Hecke monoid on the Möbius inverted class functions basis

                    Define by Möbius inversion the unique family
                    `(g_w)_{w, w\in W}` such that for all `w`
                    `e_{w,w_0} = \sum_{w' \leq_L w} g_{w'}`.

                    Then, in this basis, the coefficient of the
                    character `\chi_V` on `CM[w]` is the character of
                    `g_w` on `V`.


                    EXAMPLES::

                        sage: BiHeckeMonoid(["A",2]).character_ring().CM()
                        Character ring of bi-Hecke monoid of Weyl Group of type ['A', 2] (as a matrix group acting on the ambient space) over Integer Ring in the basis of characters of translation modules
                    """
                    from sage_semigroups.monoids.character_ring import CharacterRing
                    result = CharacterRing(self, prefix = "CM", modules = "%s-mobius inverted class functions"%self.side())
                    result.set_order(list(self.base().simple_modules_index_set()))
                    return result

                @lazy_attribute
                def CMtoC_on_basis(self):
                    """
                    EXAMPLES::

                        sage: import sage_semigroups.monoids.catalog as semigroups
                        sage: W = WeylGroup(["A", 2])
                        sage: W.element_class.__repr__ = W.element_class.to_permutation_string
                        sage: M = semigroups.BiHeckeMonoid(W); M
                        bi-Hecke monoid of Weyl Group of type ['A', 2] (as a matrix group acting on the ambient space)
                        sage: side = "right"
                        sage: G = M.character_ring(side=side)
                        sage: G.CMtoC_on_basis(W.long_element())
                        CM[123] + CM[213] + CM[312] + CM[132] + CM[231] + CM[321]

                        sage: C = G.C(); CM = G.CM()
                        sage: for chi in CM.basis():
                        ...       print chi, "=", C(chi)
                        CM[123] = C[123]
                        CM[213] = C[123] + C[213]
                        CM[132] = C[123] + C[132]
                        CM[312] = C[123] + C[213] + C[312]
                        CM[231] = C[123] + C[132] + C[231]
                        CM[321] = C[123] + C[132] + C[213] + C[312] + C[231] + C[321]

                        sage: for chi in C.basis():
                        ...       print chi, "=", CM(chi)
                        C[123] = CM[123]
                        C[213] = CM[213] - CM[123]
                        C[132] = CM[132] - CM[123]
                        C[312] = CM[312] - CM[213]
                        C[231] = CM[231] - CM[132]
                        C[321] = CM[321] - CM[231] - CM[312] + CM[123]
                    """
                    L = self.base().W.weak_poset(side="left", facade=True)
                    return self.C().sum_of_monomials * L.principal_order_ideal

                def TtoS_on_basis_disabled(self, w):
                    """
                    Computes the q-character of the translation module T_w in terms of the simple modules

                    EXAMPLES::

                        sage: import sage_semigroups.monoids.catalog as semigroups
                        sage: M = semigroups.BiHeckeMonoid(["A",3])
                        sage: p = M.W.from_compact_permutation
                        sage: QQ.<q> = QQ[]
                        sage: G = M.character_ring(q = q)
                        sage: G.TtoS_on_basis(p(4321))
                        q^3*S[1234] + q^2*S[2341] + q^2*S[3412] + q*S[3421] + q^2*S[4123] + q*S[4231] + q*S[4312] + S[4321]
                        sage: G.TtoS_on_basis(p(4321))
                        q^3*S[1234] + q^2*S[2341] + q^2*S[3412] + q*S[3421] + q^2*S[4123] + q*S[4231] + q*S[4312] + S[4321]
                        sage: G.TtoS_on_basis(p(1234))
                        S[1234]
                    """
                    if self.side()=='left':
                        # Gloups, we need a good idiom to do super calls!!!
                        return Monoids().HTrivial().Finite().CharacterRings(self.base_ring()).parent_class.TtoS_on_basis(self, w)
                    c = cutting_poset(w.parent())
                    r = c.rank_function()
                    S = self.S()
                    q = self._q
                    return S.sum( S.term(u.element, q**(r(w)-r(u))) for u in c.principal_order_ideal(w) )

                @lazy_attribute
                def induce_from_M0(self):
                    """
                    This implements the induction of a character of
                    ``M_0`` into a character of ``M``.

                    Note: this currently assumes that the character is
                    expressed in the basis of characters of simple modules.

                    Rule: inducing a simple modules `S_w` of `M_0` gives
                    the corresponding translation modules `T_w` of `M`.


                    EXAMPLES::

                        sage: import sage_semigroups.monoids.catalog as semigroups
                        sage: M = semigroups.BiHeckeMonoid(["A",2])
                        sage: M0 = M.fix_w0_monoid()
                        sage: S0 = M0.character_ring().S()
                        sage: G = M.character_ring()
                        sage: c = S0.an_element(); c
                        S[123] + 3*S[213] + 3*S[231]
                        sage: G.induce_from_M0( c )
                        T[123] + 3*T[213] + 3*T[231]
                    """
                    M0 = self.base().fix_w0_monoid()
                    S0 = M0.character_ring().S()
                    T  = self.T()
                    return S0.module_morphism(T.monomial)#, category = self.character_ring_category())

                @lazy_attribute
                def restrict_TtoS0_on_basis(self):
                    r"""
                    This implements the restriction of characters of
                    translation modules of ``M`` into characters of simple
                    modules of ``M_0``.

                    Rule: the restriction of the translation module `T_w` is given by

                    .. math:    `T_w = \sum_{u \in [1,w]_R} S_u`

                    EXAMPLES::

                        sage: import sage_semigroups.monoids.catalog as semigroups
                        sage: M = semigroups.BiHeckeMonoid(["A",2])
                        sage: M0 = M.fix_w0_monoid()
                        sage: S0 = M0.character_ring().S()
                        sage: T = M.character_ring().T()
                        sage: G = M.character_ring()
                        sage: G.restrict_TtoS0_on_basis(M.W.an_element())
                        S[231] + S[213] + S[123]
                        sage: for e in T.basis():
                        ...       assert S0(e) == G.restrict_TtoS0(e)
                        ...       print "Res(%s) = %s"%(e, S0(e))
                        Res(T[123]) = S[123]
                        Res(T[213]) = S[213] + S[123]
                        Res(T[132]) = S[132] + S[123]
                        Res(T[312]) = S[312] + S[132] + S[123]
                        Res(T[231]) = S[231] + S[213] + S[123]
                        Res(T[321]) = S[321] + S[231] + S[312] + S[213] + S[132] + S[123]

                        sage: for e in S0.basis():
                        ...       print "%s = Res(%s)"%(e, T(e))
                        S[213] = Res(T[213] - T[123])
                        S[132] = Res(T[132] - T[123])
                        S[312] = Res(T[312] - T[132])
                        S[231] = Res(T[231] - T[213])
                        S[321] = Res(T[321] - T[231] - T[312] + T[123])
                    """
                    assert self.side() == "right"
                    M0 = self.base().fix_w0_monoid()
                    S0 = M0.character_ring().S()
                    S0.set_order(list(self.base().simple_modules_index_set()))
                    W = self.base().W
                    R = W.weak_poset(side = "right", facade=True)
                    return S0.sum_of_monomials * R.principal_order_ideal

                @lazy_attribute
                def induce_from_M0_P(self):
                    """
                    This attempts to implements the induction of a
                    character of projective modules of ``M_0`` into a
                    character of projective modules of ``M``. This works
                    for A_2 and A_3, but not A_4.

                    EXAMPLES::

                        sage: import sage_semigroups.monoids.catalog as semigroups
                        sage: M = semigroups.BiHeckeMonoid(["A",3])
                        sage: M0 = M.fix_w0_monoid()
                        sage: S0 = M0.character_ring().S()
                        sage: P0 = M0.character_ring().P()
                        sage: P = M.character_ring().P()
                        sage: G = M.character_ring() # 10 s
                        sage: for e in P0.basis():
                        ...       assert G.induce_from_M0_P(e) == P(G.induce_from_M0(S0(e)))
                    """
                    print("warning: this is using a wrong formula for A_4, ...")
                    M0 = self.base().fix_w0_monoid()
                    P0 = M0.character_ring().P()
                    return P0.module_morphism(self.induce_from_M0_P_basis, codomain = self.P())

                def induce_from_M0_P_basis(self, w):
                    """
                    EXAMPLES::

                        sage: import sage_semigroups.monoids.catalog as semigroups
                        sage: M = semigroups.BiHeckeMonoid(["A",2])
                        sage: M0 = M.fix_w0_monoid()
                        sage: P0 = M0.character_ring().P()
                        sage: G = M.character_ring() # 10 s
                        sage: for w in M.W:
                        ...       print "Ind(P[%s]) = "%w, G.induce_from_M0_P_basis( w )
                        Ind(P[213]) =  P[213] + P[231]
                        Ind(P[231]) =  P[231]
                        Ind(P[321]) =  P[321]
                        Ind(P[132]) =  P[132] + P[312]
                        Ind(P[312]) =  P[312]
                    """
                    W = w.parent()
                    R = W.weak_poset(side="right")
                    C = cutting_poset(W)
                    w0 = W.w0
                    result = set(u.element for u in R.principal_order_filter(w))
                    for u in C.principal_order_ideal(w0 * w):
                        u = w0 * u.element
                        if u == w: continue
                        result.remove(u)
                    # This computes the smallest element v in [w,w_0]
                    # which is at the bottom of a descent class D_I;
                    # e.g. the interval [v,w0]_R is a translate of the
                    # parabolic subgroup W_I.
                    I = (w**-1 * w0).descents(side = "right")
                    v = w0.coset_representative(index_set = I, side = "right")
                    for u in R.principal_order_filter(v):
                        u = u.element
                        if u == v: continue
                        result.discard(u)
                    P = self.P()
                    return P.sum_of_monomials(result)

                def IndP0_P3_basis(self, w):
                    """
                    EXAMPLES::

                        sage: import sage_semigroups.monoids.catalog as semigroups
                        sage: M = semigroups.BiHeckeMonoid(["A",2])
                        sage: M0 = M.fix_w0_monoid()
                        sage: P0 = M0.character_ring().P()
                        sage: G = M.character_ring() # 10 s
                        sage: for w in M.W:
                        ...       print "IndP0_P(P[%s]) = "%w, G.induce_from_M0_P_basis( w )
                        Ind(P[213]) =  P[213] + P[231]
                        Ind(P[231]) =  P[231]
                        Ind(P[321]) =  P[321]
                        Ind(P[132]) =  P[132] + P[312]
                        Ind(P[312]) =  P[312]
                    """
                    W = w.parent()
                    R = W.weak_poset(side="right")
                    C = cutting_poset(W)
                    w0 = W.w0
                    result = set(u.element for u in R.principal_order_filter(w))
                    # Remove non trivial cutting points
                    for u in C.principal_order_ideal(w0 * w):
                        u = w0 * u.element
                        if u == w: continue
                        result.remove(u)
                    # For u_J in [w,w_0]_L obtained by pealing off as many j-descents
                    # as possible (bottom of a parabolic sub...), and if u <> J,
                    # remove all points strictly below u.
                    #
                    # The type of [w, w_0]_R: v * w = w0
                    w_w0 = w**-1 * w0
                    I = set( w_w0.reduced_word() )
                    for J in Subsets(I, len(I)-1):
                        v = w * w_w0.coset_representative(index_set = J, side ="right")
                        for u in R.principal_order_filter(v):
                            u = u.element
                            if u == v: continue
                            result.discard(u)
                    P = self.P()
                    return P.sum_of_monomials(result)

                @lazy_attribute
                def IndP0_P3(self):
                    """
                    This attempts to implements the induction of a
                    character of projective modules of ``M_0`` into a
                    character of projective modules of ``M``. This works
                    for A_2 and A_3, but not A_4.

                    EXAMPLES::

                        sage: import sage_semigroups.monoids.catalog as semigroups
                        sage: M = semigroups.BiHeckeMonoid(["A",3])
                        sage: M0 = M.fix_w0_monoid()
                        sage: S0 = M0.character_ring().S()
                        sage: P0 = M0.character_ring().P()
                        sage: P = M.character_ring().P()
                        sage: G = M.character_ring() # 10 s
                        sage: for e in P0.basis():
                        ...       assert G.induce_from_M0_P(e) == P(G.induce_from_M0(S0(e)))
                    """
                    print("warning: this is using a wrong formula for A_4, ...")
                    M0 = self.base().fix_w0_monoid()
                    P0 = M0.character_ring().P()
                    return P0.module_morphism(self.IndP0_P3_basis, codomain = self.P(), category = self.character_ring_category())

                def EtoT_on_basis(self, w):
                    """
                    Express the character of `E_w=e_w M` in term of that of
                    translation modules.

                    This is achieved by inducing the expression of the
                    character `E_w^0 = e_w M_0` in terms of the simple
                    modules for `M_0`.

                    EXAMPLES::

                        sage: import sage_semigroups.monoids.catalog as semigroups
                        sage: M = semigroups.BiHeckeMonoid(["A",2])
                        sage: G = M.character_ring()
                        sage: w = M.W.an_element()
                        sage: w
                        sage: G.EtoT_on_basis(w)
                        T[213] + T[231] + T[312] + T[321]
                        sage: G.EtoT_on_basis(w).parent()
                        Character ring of bi-Hecke monoid of Weyl Group of type ['A', 2] (as a matrix group acting on the ambient space) over Integer Ring in the basis of characters of translation modules
                    """
                    M0 = self.base().fix_w0_monoid()
                    S0 = M0.character_ring().S()
                    E0 = M0.character_ring().E()
                    return self.induce_from_M0( S0(E0[w]) )

class BiHeckeBorelSubmonoids(Category):

    def super_categories(self):
        return [Monoids().JTrivial().Finite(), Monoids().Transformation().Subobjects()]

    class ParentMethods:

        @cached_method
        def j_transversal_of_idempotents(self):
            """
            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.BiHeckeMonoid(['A',2]).fix_w0_monoid()
                sage: M.j_transversal_of_idempotents()

                sage: M.simple_modules_index_set()
                Weyl Group of type ['A', 2] (as a matrix group acting on the ambient space)
            """
            return self.ambient().j_transversal_of_idempotents().map(self.retract)

    class ElementMethods:

        def contraction_pattern(self):
            W = self.parent().ambient().W
            s = W.simple_reflections()
            result = []
            w = W.one()
            for i in W.long_element().reduced_word():
                result.append(0 if self(w) == self(s[i]*w) else 1)
                w = s[i] * w
            return result

    class CharacterRings(CharacterRingsCategory):
        pass


class BiHeckeMonoid(AutomaticMonoid):
    """
    Returns the monoid generated by the raising and lowering 0-Hecke
    operators acting on the Coxeter group W (note: only Weyl groups
    are currently supported)

    FIXME: why aren't those tests run???

    EXAMPLES::

        sage: import sage_semigroups.monoids.catalog as semigroups
        sage: M = semigroups.BiHeckeMonoid(['A',2]); M
        bi-Hecke monoid of Permutation Group with generators [(1,3)(2,5)(4,6), (1,4)(2,3)(5,6)]
        sage: M.cardinality()
        23

    The group W is accessible as (TODO: should be a method!)::

        sage: M.W
        Weyl Group of type ['A', 2] (as a matrix group acting on the ambient space)

    Its identity and maximal element are accessible as::

        sage: M.W.one(), M.W.w0
        (123, 321)

     - self.W is a Coxeter group or a TranslationModule
    """
    @staticmethod
    def __classcall_private__(cls, W):
        if not (isinstance(W, TranslationModule) or W in CoxeterGroups()):
            W = WeylGroup(W)
        return super(BiHeckeMonoid, cls).__classcall__(cls, W)

    def __init__(self, W):
        self.W = W
        assert 0 not in W.index_set()
        ambient_monoid = FiniteSetMaps(self.W, action="right")
        #
        pi  = self.W.simple_projections(length_increasing = True ).map(ambient_monoid)
        opi = self.W.simple_projections(length_increasing = False).map(ambient_monoid)
        piopi = Family(dict([ [ i,  pi[i] ] for i in  pi.keys()] +
                            [ [-i, opi[i] ] for i in opi.keys()]))
        assert piopi.cardinality() == len(W.index_set()) * 2,\
            "Oops: using -i as key causes trouble!"
        #
        category = Monoids().Transformation().Subobjects()
        if W in CoxeterGroups():
            category = BiHeckeMonoids() & category
        AutomaticMonoid.__init__(self, piopi,
                                 ambient=ambient_monoid, one=ambient_monoid.one(), mul=operator.mul,
                                 category=category)
        self.rename("bi-Hecke monoid of %s"%W)
        self.domain = self.W
        self.codomain = self.W


    def from_word(self, word):
        g = self.monoid_generators()
        return prod([g[i] for i in word], self.one())

    def piw(self, w):
        assert(w in self.W)
        return self.from_word(w.reduced_word())

    def opiw(self, w):
        assert(w in self.W)
        return self.from_word([-i for i in w.reduced_word()])

    def left_interval(self, a, b):
        """
        With one argument a in self.W, returns the interval [1,
        a]. With two arguments, returns the interval [a, b]

        This really should be a method of self.W
        """
        return self.e(a, b).image_set()

    @cached_method
    def elements_by_image_set(self):
        from sage.misc.misc import fibers
        return fibers(lambda x: frozenset(x.image_set()), self)

    def from_image_set(self, S):
        """
        Returns all the elements of M with a given image set
        """
        return self.elements_by_image_set()[frozenset(S)]


#        if isinstance(w, sage.combinat.permutation.Permutation_class):
#            # Temporary workaround until Permutation_class.reduced_word accept the 'positive' option)
#            red = (Permutation([i for i in reversed(range(1,len(w)+1))]) * w.inverse()).reduced_word()
#        else:
#            red = w.reduced_word(positive=False)
#        return prod([self.generators[i] for i in red] + [self.generators[-i] for i in reversed(red)], self.one())

    def fix_one_monoid(self):
        """
        Returns the submonoid of elements of self which fix one

        EXAMPLES::

            sage: import sage_semigroups.monoids.catalog as semigroups
            sage: M = semigroups.BiHeckeMonoid(['A',3]);
            sage: M1 = M.fix_one_monoid();
            sage: M1.cardinality()
            71
            sage: M = semigroups.BiHeckeMonoid(['A',2]);
            sage: M1 = M.fix_one_monoid();
            sage: M1.cardinality()
            sage: Poset(M1.cayley_graph(simple=True), cover_relations=False).show()

        """
        return AutomaticMonoid(Family(dict((w, self.e(w)) for w in [~u * self.W.w0 for u in self.W.grassmannian_elements(side="right")])),
                               one = self.one(),
                               category = Monoids().JTrivial().Finite())

    @cached_method
    def fix_w0_monoid(self):
        """
        Returns the submonoid of elements of ``self`` which fix `w_0`

        EXAMPLES::

            sage: import sage_semigroups.monoids.catalog as semigroups
            sage: M = semigroups.BiHeckeMonoid(['A',3]);
            sage: M0 = M.fix_w0_monoid()
            sage: M0.cardinality()
            71
        """
        w0 = self.W.w0
        #from sage.libs.semigroupe import semigroupe
        #F = semigroupe.AutomaticSemigroup# ...  cardinality_bound = 150000 (for S6)
        return self.submonoid(Family(dict((w, self.e(w,w0))
                                     for w in self.W.grassmannian_elements(side="left"))),
                               category=BiHeckeBorelSubmonoids())

    @cached_method
    def cardinality(self):
        M0 = self.fix_w0_monoid()
        #W = M0.simple_modules_index_set()
        W = self.W
        w0 = W.long_element()
        e = M0.j_transversal_of_idempotents()
        return sum(len(M0.projective_module(e[w], side="left")) * e[w0*~w].image_set().cardinality()
                   for w in W)


    def zero_hecke_monoid(self):
        """
        Returns the zero hecke submonoid of ``self``

        EXAMPLES::

            sage: import sage_semigroups.monoids.catalog as semigroups
            sage: M = semigroups.BiHeckeMonoid(['A',2]);
            sage: H0 = M.zero_hecke_monoid(); H0.cardinality()
            6
            sage: M = semigroups.BiHeckeMonoid(['A',3]);
            sage: H0 = M.zero_hecke_monoid(); H0.cardinality()
            24
        """
        return AutomaticMonoid(Family(dict((w, self.piw(w)) for w in self.W)), one = self.one(), category = Monoids().JTrivial().Finite())

    def projective_module1(self, w):
        """
        An missed attempt at a combinatorial description of the projective modules

        EXAMPLES::

            sage: import sage_semigroups.monoids.catalog as semigroups
            sage: M = semigroups.BiHeckeMonoid(["A",2])
            sage: for w in sorted(M.W):
            ...       print w, len(list(M.projective_module1(w)))
            123 1
            132 5 # wrong [1,2] should not be in the projective module
            213 5 # wrong
            231 3
            312 3
            321 6
        """
        w0 = self.W.w0
        covers = [self.e(c, w0) for c in w.weak_covers(side = "left", positive = True)]
        def succ(x):
            for g in self.semigroup_generators():
                y = x*g
                if any(e*y == y for e in covers):
                    continue
                yield y
        return TransitiveIdeal(succ, [self.e(w,w0)])


    def projective_module3(self, w):
        """
        Yet another attempt at a combinatorial description of the projective modules

        EXAMPLES::

            sage: import sage_semigroups.monoids.catalog as semigroups
            sage: M = semigroups.BiHeckeMonoid(["A",2])
            sage: for w in sorted(M.W):
            ...       print w, len(list(M.projective_module3(w)))
            123 1
            132 2
            213 2
            231 3
            312 3
            321 6
            sage: M = semigroups.BiHeckeMonoid(["A",3])
            sage: for w in sorted(M.W):
            ...       print w, len(list(M.projective_module3(w)))
            1234:  1  1  1
            1243:  2  2  8
            1324:  2  2 22 !
            1342:  3  3  3
            1423:  3  3  3
            1432: 12  6 12
            2134:  2  2  8 !
            2143: 12  4 12
            2314:  3  3  3
            2341:  4  4  4
            2413:  5  5  5
            2431:  8  8  8
            3124:  3  3  3
            3142:  5  5  5
            3214: 12  6 12
            3241:  8  8  8
            3412:  6  6  6
            3421: 12 12 12
            4123:  4  4  4
            4132:  8  8  8
            4213:  8  8  8
            4231: 12 12 12
            4312: 12 12 12
            4321: 24 24 24
        """
        e = self.j_transversal_of_idempotents()
        P = self.j_poset_on_regular_classes()

        idempotents = sum((self.j_class_idempotents(self.j_class_index(e[f]))
                           for f in P.lower_covers(w)),[])
        def succ(x):
            for g in self.semigroup_generators():
                y = x*g
                if any(f*y == y for f in idempotents):
                    continue
                yield y
        return TransitiveIdeal(succ, [e])

    def projective_module2(self, w):
        """
        Yet another attempt at a combinatorial description of the projective modules

        EXAMPLES::

            sage: import sage_semigroups.monoids.catalog as semigroups
            sage: M = semigroups.BiHeckeMonoid(["A",2])
            sage: for w in sorted(M.W):
            ...       print w, len(list(M.projective_module3(w)))
            123 1
            132 2
            213 2
            231 3
            312 3
            321 6
            sage: M = semigroups.BiHeckeMonoid(["A",3])
            sage: for w in sorted(M.W):
            ...       print w, len(list(M.projective_module3(w)))
            1234:  1  1  1
            1243:  2  2  8
            1324:  2  2 22 !
            1342:  3  3  3
            1423:  3  3  3
            1432: 12  6 12
            2134:  2  2  8 !
            2143: 12  4 12
            2314:  3  3  3
            2341:  4  4  4
            2413:  5  5  5
            2431:  8  8  8
            3124:  3  3  3
            3142:  5  5  5
            3214: 12  6 12
            3241:  8  8  8
            3412:  6  6  6
            3421: 12 12 12
            4123:  4  4  4
            4132:  8  8  8
            4213:  8  8  8
            4231: 12 12 12
            4312: 12 12 12
            4321: 24 24 24
        """
        w0 = self.W.w0
        e = self.e(w,w0)
        P = self.h_poset_on_idempotents()
        idempotents = [f.element for f in P.lower_covers(e)]
        def succ(x):
            for g in self.semigroup_generators():
                y = x*g
                if any(f*y == y for f in idempotents):
                    continue
                yield y
        return TransitiveIdeal(succ, [e])

    def f(self, u, v):
        """
        Given a cover u<v in Bruhat order, try to build f such that f(v) = u and f(1) = 1
        """

    def latex_graph_node_placement(self):
        x = [0] * self.cardinality()
        result = ""
        for m in self:
            l = len(m.reduced_word())
            result += r"""\node(%s) at (%s,%s) {};
"""%(m.node_label(), x[l], 10*l)
            x[l] += 10
        return result

    def latex_graph_inner(self):
        """
        EXAMPLES::

            sage: import sage_semigroups.monoids.catalog as semigroups
            sage: M = semigroups.BiHeckeMonoid(["A",2])
            sage: print M.latex_graph_node_placement()
            sage: M = semigroups.BiHeckeMonoid(["A",2]); fd = open("essai-inner.tex", "write"); fd.write(M.latex_graph_inner()); fd.close()
        """
        colors = {1:"blue", 2:"red", 3:"green"}
        result = r"""\begin{pgfonlayer}{nodes}
"""
        for m in self:
            result += r"""  \node(n%s) at (%s) {\scalebox{1}{%s}};
"""%(m.node_label(), m.node_label(), latex(m))
        result += r"""\end{pgfonlayer}{nodes}
"""

        edges = {}
        for (u, v, (i, dir)) in self.cayley_graph(side = "twosided").edges():
            if (u,v,i) in edges:
                edges[u,v,i] = "both"
            else:
                edges[u,v,i] = dir

        for (u, v, i) in edges.keys():
            dir = edges[u,v,i]
            if u == v:
                continue
            if i<0:
                edge_label = r"\overline{%s}"%-i
            else:
                edge_label = "%s"%i
            if dir == "both":
                edge_label = r"%s\!\!\times\!\!%s"%(edge_label, edge_label)
            elif dir == "left":
                edge_label = r"%s\!\!\times\!\!\phantom{1}"%edge_label
            else:
                edge_label = r"\phantom{1}\!\!\times\!\!%s"%edge_label
            if u != v:
                result += r"""  \draw [->, color = %s](n%s) -- node {$%s$} (n%s);
"""%(colors[abs(i)], u.node_label(), edge_label, v.node_label())
        return result

    class Element(AutomaticMonoid.Element):

        #def left_symbol(self):
        #

        #@cached_method
        def type(self):
            """
            Returns the type of ``self``.

            The image set of ``self`` is contained in the interval
            `[a,b]_L` in left order, where `a=self(1)` and `b =
            self(w_0)`. The type of ``self`` is the type of this
            interval, that is `ba^{-1}`.
            """
            W = self.parent().W
            return self(W.w0) * (self(W.one()))**-1

        def node_label(self):
            result = "".join(str(i) for i in self.reduced_word())
            if result == "":
                return "one"
            else:
                return result

        def latex_sub_weak_order(self, edge_options = lambda u,v: "", draw_node = lambda w: False, side = "right"):
            """
            INPUT:
             - draw_edge: a predicate taking two elements of the Coxeter group 

            Returns a LaTeX / tikz picture of the left weak order,
            including only those edges for which the predicate is satisfied.

            """
            result = r"""
\begin{tikzpicture}[xscale=.5,yscale=-.5,inner sep=0pt,baseline=(current bounding box.east)]
"""
            W = self.parent().W
            layout = right_weak_order_layout(W.cartan_type())
            for w in W:
                label = draw_node(w)
                if label == True:
                    label = r"$\bullet$"
                elif label == False:
                    label = "."
                else:
                    label = "\""+str(label)+"\""
                result += r"""  \node (%s) at %s {%s};
"""%(w.to_permutation_string(), layout[(~w).to_permutation()], label)

            for w in self.parent().W:
                for i in w.descents(side = side):
                    w1 = w.apply_simple_reflection(i, side = side)
                    result += r"""  \draw [color=%s,%s] (%s) -- (%s);
"""%(self._colors[i],edge_options(w, w1),w.to_permutation_string(), w1.to_permutation_string())
            return result + r"""\end{tikzpicture}
"""

        def latex_image_set(self, side = "left"):
            image_set = self.image_set()
            return self.latex_sub_weak_order(
                edge_options = lambda u,v: "line width="+("2pt" if u in image_set and v in image_set else "0pt"),
                draw_node = lambda u: u in image_set,
                side = side)

        def latex_fibers(self, side = "left"):
            return self.latex_sub_weak_order(
                edge_options = lambda u,v: "line width="+("2pt" if self(u) != self(v) else "0pt"),
                side = side)

        def latex_reduced_word(self):
            result = "".join(r"{\color{%s}%s}"%(self._colors[abs(i)], str(i) if i >0 else r"\overline{%s}"%abs(i)) for i in self.reduced_word())
            if self.is_idempotent():
                result = "{%s}^*"%result
            return result

        @cached_method
        def _latex_(self, side = "left"):
            """
            Latex output (currently only implemented for A2/A3)

            EXAMPLES::

                sage: import sage_semigroups.monoids.catalog as semigroups
                sage: M = semigroups.BiHeckeMonoid(["A",3])
                sage: M.list()                          # required for the moment to get the reduced word ...
                sage: latex(M.one())
                sage: view(M.one(), format = 'pdf')
            """
            if right_weak_order_layout(self.parent().W.cartan_type()) is not None:
                return r"""\fbox{$\stackrel{%s}{%s \raisebox{-.5ex}{$\ \mapsto\ $} %s}$}"""%(self.latex_reduced_word(), self.latex_fibers(), self.latex_image_set())
            else:
                return self.latex_reduced_word()

        _colors = {1:"blue", 2:"red", 3:"green"}

def right_weak_order_layout(cartan_type):
    if cartan_type == CartanType(["A",1]):
        return {
            (1,2) : (0,1),
            (2,1) : (0,0),
        }
    if cartan_type == CartanType(["A",2]):
        return {
            (1,2,3) : (1,3),

            (2,1,3) : (0,2),
            (1,3,2) : (2,2),

            (2,3,1) : (0,1),
            (3,1,2) : (2,1),

            (3,2,1) : (1,0)
        }
    elif cartan_type == CartanType(["A",3]):
        return {
            (1, 2, 3, 4) : ( 0,6),

            (2, 1, 3, 4) : (-1,5),
            (1, 3, 2, 4) : ( 0,5),
            (1, 2, 4, 3) : ( 1,5),

            (2, 3, 1, 4) : (-2,4),
            (3, 1, 2, 4) : (-1,4),
            (2, 1, 4, 3) : ( 0,4),
            (1, 3, 4, 2) : ( 1,4),
            (1, 4, 2, 3) : ( 2,4),

            (2, 3, 4, 1) : (-2.5,3),
            (3, 2, 1, 4) : (-1.5,3),
            (2, 4, 1, 3) : (-0.5,3),
            (3, 1, 4, 2) : ( 0.5,3),
            (4, 1, 2, 3) : ( 1.5,3),
            (1, 4, 3, 2) : ( 2.5,3),

            (3, 2, 4, 1) : (-2,2),
            (2, 4, 3, 1) : (-1,2),
            (3, 4, 1, 2) : ( 0,2),
            (4, 2, 1, 3) : ( 1,2),
            (4, 1, 3, 2) : ( 2,2),

            (3, 4, 2, 1) : (-1,1),
            (4, 2, 3, 1) : ( 0,1),
            (4, 3, 1, 2) : ( 1,1),

            (4, 3, 2, 1) : ( 0,0),
       }

def simple_module_structure(w):
    """
        sage: W = WeylGroup(["D", 4])
        ...   for w in W:
        ...       t, simple, minimal_Js, blocks, intervals = simple_module_structure(w)
        ...       print w.to_permutation(), len(simple), minimal_Js



        sage: for T in [ ["A", 1], ["A", 2], ["A", 3], ["A", 4], ["B", 2], ["B", 3], ["B", 4], ["D", 4] ]:
        ...     print "\n",T
        ...     W = WeylGroup(T)
        ...     for w in sorted(W, key = attrcall("to_permutation")):
        ...       wcomp = W.long_element() * w^-1
        ...       t, simple, minimal_Js, blocks, intervals = simple_module_structure(wcomp)
        ...       print "%s %s %3s %2s %-12s%s"%(w.to_permutation(), wcomp.to_permutation(), len(t), len(simple), [len(blocks[J]) for J in minimal_Js], minimal_Js)

    Computer evidence: the minimal Js always form a connected subgraph of the dynkin diagram
    (if everything commute, one can split two blocks?)
    """
    W = w.parent()
    # the simple reflections used to go from w to w0 in right order,
    I = set( ((w**-1) * W.long_element()).reduced_word() )
    translation_module = upper_ideal(w)
    blocks    = dict()
    intervals = dict()
    simple_module = translation_module

    # If J1 \subset J2 give the same block, we only keep the first one
    # For this, we assume that the Subsets(I) are sorted by increasing cardinality
    for J in Subsets(I):
        J = tuple(sorted(J))
        block = upper_ideal(w, index_set = J)
        if len(block) == 1 or len(translation_module) % len(block) != 0: continue
        if block in blocks.values():
#            print "Ignoring J giving an already know block"
            continue

        # construct the top interval by removing from the translation
        # module everything that is below elements u in block with u != w
        top_interval = translation_module.difference( upper_ideal(block.difference([w]) ))

        interval = [w**-1 * u for u in top_interval]
        if len(interval) * len(block) != len(translation_module): continue
        if len(set( u * v for u in block for v in interval )) != len(translation_module): continue
        bot = max(block, key = attrcall('length'))
        bottom_interval = set(bot * v for v in interval)
        simple_module = simple_module.difference(bottom_interval)
        blocks[J] = block
        intervals[J] = interval

    # Check that the set of J's is closed under union, and extract
    # those that are not unions of smaller ones
    Js        = set(blocks.keys())
    minimalJs = set(blocks.keys())
    for a,b in Subsets(Js, 2):
        ab = tuple(sorted(set(a).union(set(b))))
        if a == ab or b == ab: continue
        assert ab in Js
        minimalJs.discard(ab)
    minimalJs = sorted(minimalJs, key = lambda l: (len(l), l))

    return translation_module, simple_module, minimalJs, blocks, intervals

class TranslationModule(FiniteEnumeratedSet):
    @staticmethod
    def __classcall__(cls, w):
        return UniqueRepresentation.__classcall__(cls, w)

    @classmethod
    def an_instance(cls):
        """
        EXAMPLES::

            sage: T = TranslationModule.an_instance()
            sage: T
            sage: list(T)
            [123, 213, 231]

        """
        W = WeylGroup(["A",2])
        s = W.simple_reflections()
        return cls(s[1] * s[2])

    def __init__(self, w):
        """
        Returns the interval [1,w], endowed with the action of the pi-opi monoid

            sage: W = WeylGroup(["A",3])
            sage: s = W.simple_reflections()
            sage: T = TranslationModule(s[1] * s[2])
            sage: list(T)
            [123, 213, 231]
        """
        self._w = w
        self._W = w.parent()
        FiniteEnumeratedSet.__init__(self, sorted(lower_ideal(w, side = "right"), key = attrcall("to_permutation")))

    @cached_method
    def index_set(self):
        return sorted(set(self._w.reduced_word()))

    @cached_method
    def descent_set_structure(self, J):
        w = self._w
        u = w.coset_representative(side = "left", index_set = J)
        if w == u: # Trivial block
            return None
        if not weak_lequal(u, w, side = "right"): # u \not <_R w
            return None
        wJ = w * u**-1
        if set(J) != set(wJ.reduced_word()): # J not minimal
            return None
        return (wJ, u)

    def coset(self, J):
        return lower_ideal(self.descent_set_structure(J)[1], side = "right")

    def long_element(self, J):
        r"""
        For J a descent set, returns the longest element w_J in self \intersect W_J
        """
        return self.descent_set_structure(J)[0]

    def Jw(self, J):
        """
        For J a descent set, returns the element `{}^Jw` such that `w = w_J{}^Jw`.
        """
        return self.descent_set_structure(J)[1]

    @cached_method
    def descent_sets(self):
        return [ J
                 for J in (tuple(sorted(J)) for J in Subsets(self.index_set()))
                 if self.descent_set_structure(J) is not None ]

    @cached_method
    def minimal_descent_sets(self):
        """

        EXAMPLES::

            sage: W = WeylGroup(["A", 3])
            sage: for w in sorted(W, key=attrcall("to_permutation")):
            ...       T = TranslationModule(w)
            ...       print w, T.minimal_descent_sets()
            1234 []
            1243 [(3,)]
            1324 [(2,)]
            1342 [(2, 3)]
            1423 [(2, 3)]
            1432 [(2,), (3,)]
            2134 [(1,)]
            2143 [(1,), (3,)]
            2314 [(1, 2)]
            2341 [(1, 2, 3)]
            2413 [(1, 2, 3)]
            2431 [(3,), (1, 2, 3)]
            3124 [(1, 2)]
            3142 [(1, 2, 3)]
            3214 [(1,), (2,)]
            3241 [(2,), (1, 2, 3)]
            3412 [(1, 2, 3)]
            3421 [(1,), (2, 3)]
            4123 [(1, 2, 3)]
            4132 [(2,), (1, 2, 3)]
            4213 [(1,), (1, 2, 3)]
            4231 [(1, 2), (2, 3)]
            4312 [(3,), (1, 2)]
            4321 [(1,), (2,), (3,)]

        """
        # Check that the set of J's is closed under union, and extract
        # those that are not unions of smaller ones
        Js        = set(self.descent_sets())
        minimalJs = set(self.descent_sets())
        for a,b in Subsets(Js, 2):
            ab = tuple(sorted(set(a).union(set(b))))
            if a == ab or b == ab: continue
            assert ab in Js
            minimalJs.discard(ab)
        minimalJs = sorted(minimalJs, key = lambda l: (len(l), l))
        return minimalJs

    def partial_hom(self):
        """
        Returns the set of (partially defined) functions from self to self
        """
        return FiniteSetMaps(self, self, action = "right")

    def simple_projection(self, i, side = "right", length_increasing = True):
        assert side == "right"
        pi = self.W.simple_projection(i, length_increasing=toward_max)
        def simple_projection(w):
            if w.apply_simple_reflection(i) in self:
                return pi(w)
            else:
                return None
        return self.partial_hom()(simple_projection)

    @cached_method
    def descents(self, x):
        """
            sage: W = WeylGroup(["A", 2])
            sage: w = W.long_element()
            sage: T = TranslationModule(w)
            sage: for w in sorted(W):
            ...       print w, T.descents(x)
        """
        result = set()
        for J in self.minimal_descent_sets():
            if weak_lequal(self.long_element(J), x, side = "right"):
                result = result.union(J)
        return result

    # identical to CoxeterGroups
    @cached_method
    def simple_projections(self, side = "right", length_increasing = True):
        """

        Code identical to CoxeterGroups.ParentMethods.simple_projections

        EXAMPLES::

            sage: T = TranslationModule.an_instance()
            sage: pi = T.simple_projections()
            sage: pi[1]
            [0 1 0]
            [0 1 0]
            [0 0 0]
            sage: pi[2]
            [0 0 0]
            [0 0 1]
            [0 0 1]
            sage: opi = T.simple_projections(length_increasing = False)
            sage: opi[1]
            [1 0 0]
            [1 0 0]
            [0 0 0]
            sage: opi[2]
            [0 0 0]
            [0 1 0]
            [0 1 0]

        """
        return Family(self.index_set(), lambda i: self.simple_projection(i, side = side, length_increasing=toward_max))

    def simple_reflection(self, i, side = "right"):
        assert side == "right"
        return self.simple_projection(i, length_increasing = True).to_matrix() + self.simple_projection(i, toward_max=False).to_matrix() - 1

    def simple_reflections(self, side = "right"):
        r"""
        Code identical to CoxeterGroups.ParentMethods.simple_reflections

        EXAMPLES::

            sage: T = TranslationModule.an_instance()
            sage: s = T.simple_reflections()
            sage: s[1]
            [ 0  1  0]
            [ 1  0  0]
            [ 0  0 -1]
            sage: s[2]
            [-1  0  0]
            [ 0  0  1]
            [ 0  1  0]

        s[i] is defined as the element `\pi[i] + \opi[i] -1` acting on `\C T_w`::

            sage: pi[1].to_matrix() + opi[1].to_matrix() - 1
            [ 0  1  0]
            [ 1  0  0]
            [ 0  0 -1]

        Those s[i] satisfy the braid relations::

            sage: s[1]*s[2]*s[1] - s[2]*s[1]*s[2]
            [0 0 0]
            [0 0 0]
            [0 0 0]

        But this is not always the case ... counter example::

        TESTS::

            sage: W = WeylGroup(["A", 3])
            sage: from sage.combinat.root_system.coxeter_matrix import coxeter_matrix_as_function
            sage: m = coxeter_matrix_as_function(W.cartan_type())
            sage: for w in W:
            ...       T = TranslationModule(w)
            ...       s = T.simple_reflections()
            ...       for i,j in Subsets(T.index_set(), 2):
            ...           if (s[i]+1).is_zero(): continue
            ...           if (s[j]+1).is_zero(): continue
            ...           assert ((s[i]*s[j]) ** m(i,j) - 1).is_zero()
        """
        return Family(self.index_set(), lambda i: self.simple_reflection(i, side = side))

    def unsigned_simple_reflection(self, i, side = "right"):
        assert side == "right"
        def unsigned_simple_reflection(u):
            v = u.apply_simple_reflection(i)
            if v in self:
                return v
            else:
                return u
        return self.partial_hom()(unsigned_simple_reflection)

    def unsigned_simple_reflections(self, side = "right"):
        """

        EXAMPLES::

            sage: T = TranslationModule.an_instance()
            sage: s = T.unsigned_simple_reflections()
            sage: s[1]
            [ 0  1  0]
            [ 1  0  0]
            [ 0  0  1]
            sage: s[2]
            [ 1  0  0]
            [ 0  0  1]
            [ 0  1  0]
        """
        return Family(self.index_set(), lambda i: self.unsigned_simple_reflection(i, side = side))

    def piopi_algebra(self):
        """
        EXAMPLES::

            sage: W = WeylGroup(["A", 3])
            sage: for w in sorted(W):
            ...       T = TranslationModule(w)
            ...       print w, T.piopi_algebra().Dimension()
            1234 1
            1243 3
            1324 3
            1342 7
            1423 7
            1432 19
            2134 3
            2143 9
            2314 7
            2341 13
            2413 21
            2431 45
            3124 7
            3142 21
            3214 19
            3241 45
            3412 31
            3421 79
            4123 13
            4132 45
            4213 45
            4231 85
            4312 79
            4321 211
        """
        ambient = gap.MatrixAlgebra(QQ, self.cardinality())
        pi  = self.simple_projections(length_increasing = True )
        opi = self.simple_projections(length_increasing = False)
        generators = [ f.to_matrix() for f in list(pi) + list(opi) ]
        if len(generators) == 0:
            generators = [ambient.One()]
        return gap.SubalgebraWithOne(ambient, generators)

    def piopi_monoid(self):
        return BiHeckeMonoid(self)

    def pius_monoid(self):
        """
        EXAMPLES::

            sage: T = TranslationModule.an_instance()
            sage: M = T.pius_monoid()
            sage: M.category()
            sage: M.one().image_set()
            set([123, 213, 231])
            sage: M.cardinality()
            16
            sage: TestSuite(M).run()
        """
        pi = self.simple_projections(length_increasing = True )
        us = self.unsigned_simple_reflections()
        pius = Family(dict([ [ i, pi[i] ] for i in pi.keys()] +
                           [ [-i, us[i] ] for i in us.keys()]))
        #
        return AutomaticMonoid(pius, one=self.partial_hom().one(),
                               category=Monoids().Transformation().Subobjects())

    def triangular_element(self, u, v):
        M = self.partial_hom()
        pi  = self.simple_projections(length_increasing = True )
        opi = self.simple_projections(length_increasing = False )
        us  = self.unsigned_simple_reflections()
        u_to_v = v * u**-1
        v_to_w = self._w * v**-1
        return M.prod(us[i] for i in u_to_v.reduced_word()) * M.prod(pi[i] for i in v_to_w.reduced_word()) * M.prod(opi[i] for i in reversed(v_to_w.reduced_word()))


    def arrows(self):
        """
        Returns all pairs ``(u,v)`` such that ``self.descents(u)`` is a subset of ``self.descents(v)``

        EXAMPLES::

            sage: T = TranslationModule.an_instance()
            sage: T.arrows()
            ((123, 123),
             (123, 213),
             (123, 231),
             (213, 123),
             (213, 213),
             (213, 231),
             (231, 231))
        """
        return tuple( (u, v) for u in self for v in self if self.descents(u).issubset(self.descents(v)) )

    def n_arrows(self):
        """
        EXAMPLES::

            sage: W = WeylGroup(["A", 2])
            sage: for w in sorted(W):
            ...       T = TranslationModule(w)
            ...       print w, T.piopi_algebra().Dimension(), T.n_arrows()
        """
        return len(self.arrows())

    def n_arrows2(self):
        """
        EXAMPLES::

            sage: W = WeylGroup(["A", 2])
            sage: for w in sorted(W):
            ...       T = TranslationModule(w)
            ...       print w, T.n_arrows(), T.n_arrows2()
        """
        result = 0
        for u in self:
            for v in self:
                if len(self.descents(u).intersection(self.descents(v))) == 0:
                    result += 1
        return result

    def projection(self, J):
        """
        Attempts to constructs an element of the monoid algebra which
        projects on `v^w_J` and kills the others.

            sage: W = WeylGroup(["A", 2])
            sage: s = W.simple_reflections()
            sage: T = TranslationModule(s[1]*s[2]*s[1])
            sage: T.projection((1,))

        Non functional yet.

        """
        Jw = self.Jw(J)

        one = self.partial_hom().one().to_matrix()
        pi  = self.simple_projections(length_increasing = True ).map(attrcall("to_matrix"))
        opi = self.simple_projections(length_increasing = False).map(attrcall("to_matrix"))

        antisymmetrizer = prod(((1-opi[i]) for i in self._W.long_element(J).reduced_word()), one)

        word = Jw.reduced_word()
        result = antisymmetrizer
        for i in range(len(word)-1):
            result *= prod((pi[word[j]] for j in range(i)), one) * (1-pi[word[i]]) * prod((opi[word[j]] for j in reversed(range(i))),one) * antisymmetrizer
        return result

@cached_function
def cutted_points(w):
    """
    Returns the set of u such that w is a cutting point for u

    EXAMPLES::

        sage: [[w, cutted_points(w)] for w in sorted(W)]

        [[123, set([123])],
         [132, set([123, 132])],
         [213, set([123, 213])],
         [231, set([231])],
         [312, set([312])]]
         [321, set([123, 132, 213, 231, 312, 321])],


    """
    W = w.parent()
    s = W.simple_reflections()
    sSet = Set(s)
    # The index of the simple roots that are mapped to simple roots
    # In type A this is i such that w(i+1) = w(i) + 1 (2x2 identity block)
    J = tuple( i for i in w.descents(side="right", positive=True) if w*s[i]*w**-1 in sSet )
    # This is {w * u, u \in W_J}, where the products are reduced
    # this is an upper ideal in right weak order
    return upper_ideal((w), side = "right", index_set = J)

@cached_function
def cutting_poset(self):
    """
    """
    return Poset((self, tuple((u,v) for u in self for v in cutted_points(u))), cover_relations=False)

@cached_function
def cutting_lattice(self):
    return LatticePoset(poset_concatenation(cutting_poset(self), Poset([["top"],[]])))

def ideal(generators, side = "right", index_set = None, positive = False):
    """
    Returns the lower (resp. upper) ideal in right (resp. right) order
    generated by the elements.

    EXAMPLES::

        sage: W = WeylGroup(["A", 2])
        sage: s = W.simple_reflections()
        sage: ideal(s[1])
        set([123, 213])
        sage: ideal(s[1], positive = True)
        set([321, 213, 231])
        sage: ideal(s[1], side = "left", positive = True)
        set([312, 321, 213])

    TESTS::

        sage: W = WeylGroup(["A", 3])
        sage: sorted([len(ideal(w)) for w in W])
        [1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 5, 5, 6, 6, 6, 8, 8, 8, 8, 12, 12, 12, 24]
    """
    if parent(generators) in CoxeterGroups():
        generators = (generators,)
    else:
        generators = tuple(generators)
    return ideal_internal(generators, side, index_set, positive)

@cached_function
def ideal_internal(generators, side = "right", index_set = None, positive = False):
    return set(TransitiveIdeal(lambda u: u.weak_covers(side = side, index_set = index_set, positive = positive), generators))

def upper_ideal(*args, **options):
    return ideal(positive = True, *args, **options)

def lower_ideal(*args, **options):
    return ideal(positive = False, *args, **options)

def weak_lequal(x, y, side = "right"):
    """
    Returns whether x <= y in weak order

        sage: W = WeylGroup(["A", 3])
        sage: s = W.simple_reflections()
        sage: weak_lequal(s[1]*s[2], s[1]*s[2]*s[3], side = "right")
        True
        sage: weak_lequal(s[1]*s[2], s[1]*s[2]*s[3], side = "left")
        False
        sage: weak_lequal(s[2]*s[3], s[1]*s[2]*s[3], side = "right")
        False
        sage: weak_lequal(s[2]*s[3], s[1]*s[2]*s[3], side = "left")
        True
    """
    if side == "right":
        div = x^(-1)*y
    else:
        div = y*x^(-1)
    return x.length() + div.length() == y.length()

def hasse_diagram_on_element(poset):
    G = poset.hasse_diagram()
    G.relabel(dict([x, x.element] for x in poset))
    return G

def poset_concatenation(P, Q):
    P = hasse_diagram_on_element(P)
    Q = hasse_diagram_on_element(Q)
    G = P.disjoint_union(Q)
    G.add_edges([p,q] for p in P.vertices() for q in Q.vertices())
    return Poset(G)

def weyl_from_compact_permutation(self, x):
    """
    EXAMPLES::

        sage: p = WeylGroup(["A",3]).p
        sage: p(1324)
        1324
    """
    return self.from_reduced_word(Permutation(reversed(ZZ(x).digits())).reduced_word())

# WeylGroup(["A", 2]).__class__.from_compact_permutation = weyl_from_compact_permutation
