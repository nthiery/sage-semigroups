sage-semigroups: A semigroup (representation) theory library for SageMath
=========================================================================

sage-semigroups is a library for computational semigroup
(representation) theory, for the open source mathematical system
`SageMath <http://sagemath.org>`_. Its intention is to serve as a
repository where experimental features can be shared among researchers
and mature until they get integrated into the main SageMath library or
discarded.

Installation
------------

Stable version (not much there yet)::

    sage -pip install sage-semigroups

For the bleeding edge version::

    git clone https://github.com/nthiery/sage-semigroups.git
    cd sage-semigroups
    sage -pip install .

In both cases, this installs the library in the Sage tree. You may
instead want to install sage-semigroup in your user directory::

    sage -pip install --user ...

Or to install it in editable mode for development::

    sage -pip install --user -e ...

See the help of the corresponding pip options for details

Usage
-----

Run sage as usual, and do::

    sage: import sage-semigroups

The features are then available as if they were native Sage features::

    TODO: add some examples

The intention is to make the later integration of those features into
Sage as transparent as possible. To enable this, the code is
structured as in the SageMath library; for example the features in::

    sage_semigroups.categories.j_trivial_monoids.JTrivialMonoids

get merged into::

    sage.categories.j_trivial_monoids.JTrivialMonoids

This is achieved using the `Recursive Monkey Patching
<http//github.com/nthiery/recursive-monkey-patch>`_ package, which see
for details.


Acknowledgements
----------------

A lot of the code was authored by Florent Hivert, Franco Saliola,
Nicolas M. Thiéry, ... and resurrected from the former Sage-Combinat
patch queue.
