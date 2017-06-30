from sage.misc.cachefunc import cached_method

class Semigroups:
    class ParentMethods:

        @cached_method
        def cayley_graph_cached(self, *args, **kwds):
            return self.cayley_graph(*args, **kwds)
