class FiniteSemigroups:
    class ParentMethods:
        def is_r_trivial(self):
            return self.cayley_graph(side="right", simple=True).is_directed_acyclic()

