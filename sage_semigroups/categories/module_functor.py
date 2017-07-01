"""
Module Functorial Construction # RESURRECTED

AUTHORS:

 - Nicolas M. Thiery (2011): initial revision
"""
#*****************************************************************************
#  Copyright (C) 2011 Nicolas M. Thiery <nthiery at users.sf.net>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.categories.category import Category
from sage.categories.covariant_functorial_construction import CovariantFunctorialConstruction, CovariantConstructionCategory
from sage.categories.category_types import Category_over_base_ring
import sage.structure.parent

# This is Category.Modules
def Modules(self, base_ring):
    """
    Return the category of ``self``-modules over ``base_ring``

    INPUT:

    - ``self`` -- a subcategory of ``Semigroups()``
    - ``base_ring`` -- a ring

    EXAMPLES:

    The category of modules over ``\QQ`` endowed with a linear action
    of a monoid::

        sage: Monoids().Modules(QQ)
        Category of semigroup modules over Rational Field

    The category of modules over ``\QQ`` endowed with a linear action
    of a finite group::

        sage: Groups().Finite().Modules(QQ)
        Category of semigroup modules over Rational Field

    TESTS::

        sage: TestSuite(Groups().Finite().Modules(QQ)).run()
    """
    from sage.categories.rings import Rings
    assert base_ring in Rings()
    return ModulesCategory.category_of(self, base_ring)

Category.Modules = Modules

class ModuleFunctor(CovariantFunctorialConstruction):
    """
    A singleton class for the module functor
    """
    _functor_name = "module"
    _functor_category = "Modules"

    def __init__(self, base_ring):
        """
        EXAMPLES::

            sage: from sage.categories.module_functor import ModuleFunctor
            sage: F = ModuleFunctor(QQ); F
            The module functorial construction
            sage: TestSuite(F).run()
        """
        from sage.categories.rings import Rings
        assert base_ring in Rings()
        self._base_ring = base_ring

    def base_ring(self):
        """
        Returns the base ring for this functor

        EXAMPLES::

            sage: from sage.categories.module_functor import ModuleFunctor
            sage: ModuleFunctor(QQ).base_ring()
            Rational Field
        """
        return self._base_ring

class ModulesCategory(CovariantConstructionCategory, Category_over_base_ring):
    """
    Returns the category of ``self``-modules over ``base_ring``

    .. todo:: UPDATE! A category with module functor is a category
    endowed with an module functor from itself to the category of
    modules, mapping a set `S` and a field `C` to a `C`-free module
    with basis indexed by `S`, more often than not endowed with an
    module structure. Typical examples are the functor from monoids
    to monoid modules, groups to group modules, etc.

    See also
    :class:`~sage.categories.covariant_functorial_construction.CovariantFunctorialConstruction`.

    INPUT:

     - ``base_ring`` -- a ring

    EXAMPLES::

        sage: Monoids().Modules(QQ)
        Category of semigroup modules over Rational Field
    """

    _functor_category = "Modules"

    def __init__(self, base_category, base_ring):
        """
        EXAMPLES::

            sage: C = Semigroups().Modules(QQ)
            sage: C
            Category of semigroup modules over Rational Field
            sage: C.base_category()
            Category of semigroups
            sage: C.super_categories()
            [Category of sets endowed with an action of a semigroup, Category of vector spaces over Rational Field]

        TESTS::

            sage: C._short_name()
            'SemigroupModules'
            sage: latex(C) # todo: improve that
            \mathbf{SemigroupModules}(\mathbf{Semigroups})
        """
        super(ModulesCategory, self).__init__(base_category, base_ring)

    def _repr_object_names(self):
        """
        EXAMPLES::

            sage: Semigroups().Modules(QQ) # indirect doctest
            Category of semigroup modules over Rational Field
        """
        return "%s modules over %s"%(self.base_category()._repr_object_names()[:-1], self.base_ring())
