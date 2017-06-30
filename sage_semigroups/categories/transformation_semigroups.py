r"""
Transformation semigroups
"""

from sage.misc.cachefunc import cached_method
from sage.categories.category_with_axiom import CategoryWithAxiom, all_axioms
from sage.categories.subobjects import SubobjectsCategory
from sage.categories.semigroups import Semigroups

all_axioms += ["Transformation"]

# This used to be SubmonoidOfFunctions in sage-combinat
class TransformationSemigroups(CategoryWithAxiom):

    @cached_method
    def super_categories(self):
        return [Semigroups()]

    class Subobjects(SubobjectsCategory):

        class ParentMethods:

            def domain(self):
                return self.ambient().domain()

        class ElementMethods:
            def __call__(self, *args):
                return self.lift()(*args)

            def image_set(self):
                return self.lift().image_set()

            def rank(self):
                return self.lift().rank()

            def fibers(self):
                return self.lift().fibers()

            def domain(self):
                return self.lift().domain()

            def codomain(self):
                return self.lift().codomain()

Semigroups.Transformation = TransformationSemigroups

Semigroups().subcategory_class.Transformation = lambda self: self._with_axiom("Transformation")
