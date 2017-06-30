r"""
Aperiodic semigroups
"""
#*****************************************************************************
#  Copyright (C) 2009-2010 Florent Hivert <florent.hivert at univ-rouen.fr>
#                2009-2017 Nicolas M. Thiery <nthiery at users.sf.net>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************

class AperiodicSemigroups:

    class ParentMethods:

        def _test_aperiodic(self, **options):
            tester = self._tester(**options)
            for x in self:
                (k,j) = x.pseudo_order()
                tester.assert_( k-j == 1, "%s has ultimate period %s"%(x,k-j) )

    class ElementMethods:

        def pow_omega(self):
            """
            The omega power of ``self``.

            EXAMPLES::

                sage: S = AperiodicMonoids().Finite().example(5); S
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
