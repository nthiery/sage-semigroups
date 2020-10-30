
import unittest

class InstanceTester:
    def __init__(self, instance, elements = None, verbose = False, prefix = "", max_runs = 4096, max_samples = 1024, failure_exception = None, **options):
        """
        A gadget attached to an instance providing it with testing utilities.

        EXAMPLES::

            sage: from sage.misc.sage_unittest import InstanceTester
            sage: InstanceTester(instance = ZZ, verbose = True, elements = [1,2,3])
            Testing utilities for Integer Ring

        This is used by ``SageObject._tester``, which see::

            sage: QQ._tester()
            Testing utilities for Rational Field
        """
        unittest.TestCase.__init__(self)
        self._instance = instance
        self._verbose = verbose
        self._elements = elements
        self._prefix = prefix
        self._max_runs = max_runs
        self._max_samples = max_samples
        if failure_exception:
            self.failureException = failure_exception

class ReturnOnError(Exception):
    pass

from sage.misc.method_decorator import MethodDecorator
class IsMethod(MethodDecorator):
    """
    ``is_method`` / ``_test_from_is_method``: method wrappers to factor out code between ``is_bar`` and ``_test_bar`` methods

    The typical usecase for those wrappers is as follow: Consider a
    category ``Foo`` with a subcategory ``Bar``.  ``Foo`` wants to
    provide a method ``Foo.ParentMethods.is_bar`` such that, for ``F``
    in ``Foo()``, ``F.is_bar()`` returns whether ``F`` satisfies all
    the properties of ``Bar()``. The method ``is_bar`` is allowed to
    assume that ``F`` indeed satisfies all the properties specified by
    ``Foo()``. It may decide to upgrade the category of ``F`` to
    ``Bar()``.

    ``Bar`` itself wants to provide a method
    ``Bar.ParentMethod._test_bar`` which is supposed to do some
    reasonable sanity checks on ``F`` to determine whether it
    satisfies all the properties of ``Bar``. If yes, ``F._test_bla()``
    should return None; otherwise it should raise some (hopefully
    meaningful) assertion.  Note that ``Bar()`` will typically
    override ``is_bar`` by a trivial method that always returns
    ``True``.

    The purpose of two decorators ``is_method`` and
    ``_test_method_from_is`` is to factor out the logic between the two
    related methods ``F.is_bla()`` and ``F._test_bla()``. They take as
    input a Python function ``is_bla(self, proof=False, **options)``.
    This function should proceed as usual for a ``_test method`` (see
    :class:`TestSuite`). If ``proof`` is ``True``, then the answer
    should be provably correct. At the end, ``is_bla`` should return
    ``None``, or a category that will be used to refine the category
    of ``F``.

    EXAMPLES:

    For the sake of brievity, we don't use categories in this example,
    but just two parents ``Union`` and ``FiniteUnion``::

        sage: from sage.misc.sage_unittest import is_method, _test_method_from_is
        sage: class Union(Parent):
        ....:     def __init__(self, sets):
        ....:         self._sets = sets
        ....:     @is_method
        ....:     def is_finite(self, proof=False, **options):
        ....:         tester = self._tester(**options)
        ....:         if proof: # we only run a full test if proof=True
        ....:             sets = self._sets
        ....:         else:     # otherwise we only check the first element
        ....:             sets = self._sets[:1]
        ....:         for set in sets:
        ....:             tester.assert_( set.is_finite(), "The set %s is not finite"%set )
        ....:         return Sets().Finite()
        sage: class FiniteUnion(Union):
        ....:     _test_finite = _test_method_from_is(Union.is_finite)

        sage: U = Union([GF(2), GF(3)])
        sage: U.category()
        Category of sets
        sage: U.is_finite()
        True
        sage: U.category()
        Category of finite enumerated sets

        sage: U = Union([GF(2), ZZ])
        sage: U.is_finite()
        False

    With ``raise_on_failure=True`` an exception is raised,
    giving information on the reason for the failure::

        sage: U.is_finite(raise_on_failure=True)
        Traceback (most recent call last):
        ...
        AssertionError: The set Integer Ring is not finite

    We now create ``FiniteUnion`` instances, and check whether they
    are correct::

        sage: V = FiniteUnion([GF(2), GF(3)])
        sage: V._test_finite()

        sage: V = FiniteUnion([ZZ, GF(2)])
        sage: V._test_finite()
        Traceback (most recent call last):
        ...
        AssertionError: The set Integer Ring is not finite

    The checks are not guaranteed to be thorought::

        sage: V = FiniteUnion([GF(2), ZZ])
        sage: V._test_finite()

    TESTS::

        sage: from sage.misc.sageinspect import sage_getsource
        sage: sage_getsource(U.is_finite)
        '      @is_method...def is_finite(self, proof=False, **options):...'
        sage: from sage.misc.sageinspect import sage_getsource
        sage: sage_getsource(V._test_finite)
        '      @is_method...def is_finite(self, proof=False, **options):...'
    """
    def __call__(self, raise_on_failure=False, proof=True, **kwds):
        """
        """
        try:
            category = self.f(self._instance, failure_exception=None if raise_on_failure else ReturnOnError, proof=proof, **kwds)
            if category:
                self._instance._refine_category_(category)
            return True
        except ReturnOnError:
            return False

is_method = IsMethod

class TestMethodFromIs(MethodDecorator):
    __doc__ = IsMethod.__doc__

    def __init__(self, f):
        r"""
        """
        if isinstance(f, IsMethod):
            f = f.f
        return super(TestMethodFromIs, self).__init__(f)

    def __call__(self, **kwds):
        r"""
        """
        self.f(self._instance, proof=False, **kwds)

_test_method_from_is = TestMethodFromIs
