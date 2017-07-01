"""
SetWithAction Functorial Construction

AUTHORS:

 - Nicolas M. Thiery (2010): initial revision
"""
#*****************************************************************************
#  Copyright (C) 2010 Nicolas M. Thiery <nthiery at users.sf.net>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.categories.category import Category
from sage.categories.covariant_functorial_construction import CovariantFunctorialConstruction, CovariantConstructionCategory
from sage.categories.algebra_functor import AlgebrasCategory
import sage.structure.parent
import sage.structure.element

class SetWithActionFunctor(CovariantFunctorialConstruction):
    """
    A singleton class for the module functor

    EXAMPLES::

        sage: from sage.categories.set_with_action_functor import SetWithActionFunctor
        sage: F = SetWithActionFunctor(); F
        The module functorial construction
        sage: TestSuite(F).run()
    """
    _functor_name = "module"
    _functor_category = "SetsWithAction"

class SetsWithActionCategory(CovariantConstructionCategory):
    """
    Returns the category of sets endowed with an action of some object of ``self``

    .. todo:: UPDATE! A category with module functor is a category
    endowed with an module functor from itself to the category of
    modules, mapping a set `S` and a field `C` to a `C`-free module
    with basis indexed by `S`, more often than not endowed with an
    module structure. Typical examples are the functor from monoids
    to monoid modules, groups to group modules, etc.

    See also
    :class:`~sage.categories.covariant_functorial_construction.CovariantFunctorialConstruction`.

    EXAMPLES::

        sage: Monoids().SetsWithAction()
        Category of sets endowed with an action of a semigroup
    """

    _functor_category = "SetsWithAction"

    def __init__(self, base_category):
        """
        EXAMPLES::

            sage: C = Semigroups().SetsWithAction()
            sage: C
            Category of sets endowed with an action of a semigroup
            sage: C.base_category()
            Category of semigroups
            sage: C.super_categories()
            [Category of sets]

        TESTS::

            sage: C._short_name()
            'SetsWithAction'
            sage: latex(C) # todo: improve that
            \mathbf{SetsWithAction}(\mathbf{Semigroups})
        """
        CovariantConstructionCategory.__init__(self, base_category)

    def _algebras_extra_super_categories(self):
        """
        EXAMPLES::

            sage: Semigroups().SetsWithAction().Algebras(QQ).extra_super_categories()
            [Category of semigroup modules over Rational Field]
            sage: HTrivialMonoids().Finite().SetsWithAction().Algebras(QQ).extra_super_categories()
            [Category of finite h trivial monoid modules over Rational Field]

        This models the statement that the algebra of a set endowed
        with an action of a semigroup is a semigroup-module, and in
        general that the algebra of a set endowed with an action of a
        shmurff should be a shmurff-module.

        .. warning:: at this point, for this to work, any category
           defining a Modules nested class should define a
           SetsWithAction nested class containing at least:

              class Algebras(AlgebrasCategory):
                  # see the warning in sage.categories.set_with_action_functor.SetsWithActionCategory._algebras_extra_super_categories
                  extra_super_categories = SetsWithActionCategory._algebras_extra_super_categories.im_func
        """
        return [self.base_category().base_category().Modules(self.base_ring())]

    def _repr_object_names(self):
        """
        EXAMPLES::

            sage: Semigroups().SetsWithAction() # indirect doctest
            Category of sets endowed with an action of a semigroup
        """
        return "sets endowed with an action of a %s"%(self.base_category()._repr_object_names()[:-1])
