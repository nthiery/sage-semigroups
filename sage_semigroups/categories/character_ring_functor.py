"""
Character Ring functor
"""
#*****************************************************************************
#  Copyright (C) 2010 Nicolas M. Thiery <nthiery at users.sf.net>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.categories.category import Category
from sage.categories.covariant_functorial_construction import CovariantFunctorialConstruction, CovariantConstructionCategory
from sage.categories.category_types import Category_over_base_ring
import sage.structure.parent
import sage.structure.element

class CharacterRingFunctor(CovariantFunctorialConstruction):
    """
    A singleton class for the character_ring functor
    """
    _functor_name = "character_ring"
    _functor_category = "CharacterRings"

    def __init__(self, base_ring):
        """
        EXAMPLES::

            sage: from sage.categories.character_ring_functor import CharacterRingFunctor
            sage: F = CharacterRingFunctor(QQ); F
            The character_ring functorial construction
            sage: TestSuite(F).run()
        """
        from sage.categories.rings import Rings
        assert base_ring in Rings()
        self._base_ring = base_ring

    def base_ring(self):
        """
        Returns the base ring for this functor

        EXAMPLES::

            sage: from sage.categories.character_ring_functor import CharacterRingFunctor
            sage: CharacterRingFunctor(QQ).base_ring()
            Rational Field
        """
        return self._base_ring

class CharacterRingsCategory(CovariantConstructionCategory, Category_over_base_ring):
    """
    Returns the category of ``base_ring``-character_rings over ``self``

    ...

    See also :class:`CovariantFunctorialConstruction`.

    INPUT:

     - ``base_ring`` -- a ring

    .. todo:: Do we want to also take as parameter the base ring for
    the modules this character ring is for?

    EXAMPLES::

        sage: FiniteSemigroups().CharacterRings(QQ)
        Category of character rings of finite semigroups over Rational Field
    """

    _functor_category = "CharacterRings"

    def __init__(self, base_category, base_ring):
        """
        EXAMPLES::

            sage: C = FiniteSemigroups().CharacterRings(QQ)
            sage: C
            Category of character rings of finite semigroups over Rational Field
            sage: C.base_category()
            Category of finite semigroups
            sage: C.super_categories()
            [Category of vector spaces with basis over Rational Field]
            sage: latex(C)    # todo: not implemented
            \mathbf{CharacterRingsOf(FiniteSemigroups)}_{\Bold{Q}}

        """
        super(CharacterRingsCategory, self).__init__(base_category, base_ring)  #, name = "CharacterRingsOf(%s)"%base_category._Category__label)

    def extra_super_categories_disabled(self):
        """
        EXAMPLES::

            sage: C = FiniteSemigroups().CharacterRings(QQ)
            sage: C.is_subcategory(Modules(QQ).WithBasis())
            True
        """
        from sage.categories.modules import Modules
        return [Modules(self.base_ring()).WithBasis()]

    def _repr_object_names(self):
        """
        EXAMPLES::

            sage: Semigroups().Finite().CharacterRings(QQ) # indirect doctest
            Category of character rings of finite semigroups over Rational Field
        """
        return "character rings of %s over %s"%(self.base_category()._repr_object_names(), self.base_ring())


def CharacterRings(self, base_ring):
    """
    INPUT:

     - ``self`` -- a subcategory of ``Semigroups(...)``

    Returns the category of character rings of ``self``.

    EXAMPLES::

        sage: FiniteSemigroups().CharacterRings(QQ)
        Category of character rings of finite semigroups over Rational Field
    """
    return CharacterRingsCategory.category_of(self, base_ring)


Category.CharacterRings = CharacterRings
