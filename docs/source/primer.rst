
A Primer
========

This short document aims to show the basic concepts underlying *μkanren*,
namely relations as goals, starting from the two primitive relations, then goal
constructors, then unification, then both finite and countable predicates,
finally.

First of all we start importing objects and definitions of the logic system:

.. doctest::

    >>> from muk.core import *
    >>> from muk.ext import *

Primitive goals
---------------

The two primitive goals :py:func:`succeed <muk.core.succeed>` and
:py:func:`fail <muk.core.fail>` denote *truth* and *falsehood* in classic
logic, respectively. Both of them are implemented as functions as any other
goal:

.. doctest::

    >>> succeed
    <function succeed at ...>
    >>> fail
    <function fail at ...>

``succeed``
~~~~~~~~~~~

In parallel, asking for all substitutions that satisfy the ``succeed``
relation yields a tautology, namely any substitution works: 

.. doctest::
    
    >>> run(succeed)
    [Tautology]

``fail``
~~~~~~~~

On the other hand, there is no substitution that satisfies the ``fail`` relation:

.. doctest::
    
    >>> run(fail)
    []

Goal ctors
----------

Before introducing the four goal constructors we show how a logic variable is
represented when it doesn't get any association:

.. doctest::

    >>> rvar(0)
    ▢₀

where class :py:class:`rvar` builds a *reified variable* providing an
integer, namely :py:const:`0`, to track the variable's birthdate.

``fresh``
~~~~~~~~~

It is a goal ctor that introduces *new* logic variables, namely without
associations, according to the plugged-in lambda expression, which receives
vars and returns a goal. Consider the following query where the variable ``q``
is introduced fresh:

.. doctest::

    >>> run(fresh(lambda q: succeed))
    [▢₀]

since the returned goal is :py:obj:`succeed` and var :py:obj:`q` doesn't get
any associations, it remains fresh in the list of values that satisfy the goal
:py:obj:`fresh(lambda q: succeed)`.

As particular case, it is possible to plugin a *thunk*, namely a lambda
expression without argument:

.. doctest::

    >>> run(fresh(lambda: succeed))
    [Tautology]

at a first this could look useless but it is of great help for the definition
of *recursive relations* as we will see in later examples (it is an instance of
η-inversion, formally).

``unify``
~~~~~~~~~

It is a goal ctor that attempts to make two arbitrary objects equal, recording
associations when fresh variables appears in the nested structures under
unification. Here we show two simple examples of unification, the first succeeds
while the second doesn't:

.. doctest::

    >>> run(unify(3, 3))
    [Tautology]
    >>> run(unify([1, 2, 3], [[1]]))
    []    

On the other hand, things get interesting when fresh variables are mixed in:

.. doctest::

    >>> run(fresh(lambda q: unify(3, q)))
    [3]
    >>> run(fresh(lambda q: unify([1, 2, 3], [1] + q)))
    [[2, 3]]
    >>> run(fresh(lambda q: unify([[2, 3], 1, 2, 3], [q, 1] + q)))
    [[2, 3]]

When two fresh vars are unified it is said that they *share*:

.. doctest::
    
    >>> run(fresh(lambda q, z: unify(q, z)))
    [▢₀]
    >>> run(fresh(lambda q, z: unify(q, z)), 
    ...     var_selector=lambda q, z: z)
    [▢₀]


``disj``
~~~~~~~~

It is a goal ctor that consumes two goals and returns a new goal that can be
satisfied when *either* the former *or* the latter goal can be satisfied:

.. doctest::

    >>> run(disj(succeed, fail))
    [Tautology]
    >>> run(disj(fail, fresh(lambda q: unify(q, True))))
    [Tautology]
    >>> run(fresh(lambda q: disj(fail, fail)))
    []
    >>> run(fresh(lambda q: disj(unify(q, False), unify(q, True))))
    [False, True]


``conj``
~~~~~~~~

It is a goal ctor that consumes two goals and returns a new goal that can be
satisfied when *both* the former *and* the latter goal can be satisfied:

.. doctest::

    >>> run(conj(succeed, fail))
    []
    >>> run(conj(fail, fresh(lambda q: unify(q, True))))
    []
    >>> run(fresh(lambda q: conj(unify(q, 3), succeed)))
    [3]
    >>> run(fresh(lambda q: conj(unify(q, False), unify(q, True))))
    []
    >>> run(fresh(lambda q: conj(fresh(lambda q: unify(q, False)), 
    ...                          unify(q, True))))
    [True]

More goal ctors
---------------

``conde``
~~~~~~~~~

.. doctest::

    >>> run(fresh(lambda q: conde([unify(q, 'orange'), succeed],
    ...                           [unify(q, 'apple'), succeed]
