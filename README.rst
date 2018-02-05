sage-semigroups: A semigroup (representation) theory library for SageMath
=========================================================================

.. image:: https://mybinder.org/badge.svg
   :target: https://mybinder.org/v2/gh/nthiery/sage-semigroups/master?filepath=demo.ipynb
   :alt: Run on binder

sage-semigroups is a library for computational semigroup
(representation) theory, for the open source mathematical system
`SageMath <http://sagemath.org>`_. Its intention is to serve as a
repository where experimental features can be shared among researchers
and mature until they get integrated into the main SageMath library or
discarded.

News
----

- June 2017: up to now, that repository had been a mostly empty shell.
  At the occasion of a sprint with Franco Saliola, most of the
  semigroup code from the Sage-Combinat queue was imported in
  sage-semigroups, together with private code from Franco. As a
  result, a dozen semigroups are available in the ``semigroups.*``
  catalog. In principle, the code to compute the representation theory
  of j-trivial / aperiodic monoids is there too. However the latter
  code has been imported as is, and still remains to be updated w.r.t.
  the new environment.

  **Most tests don't pass at this stage**

  Use at your own risk, and expect many failures!

Future plans
------------

- Clean up to get all tests to pass;
- As much as possible, use `libsemigroups <https://github.com/james-d-mitchell/libsemigroups/>`_
  and GAP's `Semigroups package <https://gap-packages.github.io/Semigroups/>`_ for
  the semigroups;
- Focus on the representation theory aspects (e.g. representation
  theory of general semigroups) and on providing special families of
  monoids whose definition use other features of Sage (e.g. root
  systems).

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

See the brief `demo notebook <demo.ipynb>`_, or try it live on
`Binder <https://mybinder.org/v2/gh/nthiery/sage-semigroups/master?filepath=demo.ipynb>`_.

In short:

    sage: import sage_semigroups

The features are then available as if they were native Sage features::

    sage: semigroups.<tab>
    sage: H = semigroups.HeckeMonoid(["A",3])
    sage: H.is_l_trivial()
    True
    sage: H.quiver()
    Digraph on 8 vertices
    sage: H.cartan_matrix()
    [1 0 0 0 0 0 0 0]
    [0 1 1 1 0 0 0 0]
    [0 1 2 1 1 0 0 0]
    [0 1 1 1 0 0 0 0]
    [0 0 1 0 2 1 1 0]
    [0 0 0 0 1 1 1 0]
    [0 0 0 0 1 1 1 0]
    [0 0 0 0 0 0 0 1]

The intention is to make the later integration of those features into
Sage as transparent as possible. To enable this, the code is
structured as in the SageMath library; for example the features
implemented in::

    sage_semigroups.categories.j_trivial_monoids.JTrivialMonoids

get merged into the corresponding native Sage category::

    sage.categories.j_trivial_monoids.JTrivialMonoids

This is achieved using the `Recursive Monkey Patching
<https://github.com/nthiery/recursive-monkey-patch>`_ package, which see
for details.


Acknowledgements
----------------

A lot of the code was authored by Florent Hivert, Franco Saliola,
Nicolas M. Thiéry, ... and resurrected from the former Sage-Combinat
patch queue.
