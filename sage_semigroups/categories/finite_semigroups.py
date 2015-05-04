from sage_semigroups.misc.monkey_patch import MonkeyPatch
from sage.categories.semigroups import Semigroups

class FiniteSemigroups(MonkeyPatch, Semigroups.Finite):
    class ParentMethods:
        def is_r_trivial(self):
            return self.cayley_graph(side="right", simple=True).is_directed_acyclic()

