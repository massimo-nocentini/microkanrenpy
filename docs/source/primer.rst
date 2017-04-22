
A Primer
========

This short document aims to show the basic concepts underlying *μkanren*,
namely relations as goals, and how to use primitive goals as building blocks to
build and define relations. We start from two primitive relations toward
recursive relations, through constructors, fresh logic variables, unification
and η-inversion.

First of all we start importing objects and definitions of the logic system:

.. doctest::

    >>> from muk.core import *
    >>> from muk.ext import *

We use the interface function :py:func:`run <muk.core.run>` to ask for
substitutions that satisfy the relation under study; moreover, nouns *relation*, 
*goal* and *predicate* are equivalent notions and denotes the same concept in 
the rest of this presentation.

Primitive goals
---------------

The two primitive goals :py:func:`succeed <muk.core.succeed>` and
:py:func:`fail <muk.core.fail>` denote *truth* and *falsehood* in classic
logic, respectively.

``succeed``
~~~~~~~~~~~

Asking for all substitutions that satisfy the ``succeed``
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

Before introducing goal constructors we show how a logic variable is
represented when it doesn't get any association:

.. doctest::

    >>> rvar(0)
    ▢₀

where class ``rvar`` builds a *reified variable* providing an
integer, namely ``0``, to track the variable's birthdate.

``fresh``
~~~~~~~~~

It is a goal ctor that introduces *new* logic variables, namely variables without
associations, according to the plugged-in lambda expression, which receives
vars and returns a goal. Consider the following query where the variable ``q``
is introduced fresh:

.. doctest::

    >>> run(fresh(lambda q: succeed))
    [▢₀]

since the returned goal is ``succeed`` and var ``q`` doesn't get any
association, it remains fresh in the list of values, result of the whole
``run`` invocation, that satisfy the goal ``fresh(lambda q: succeed)``.

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

When two fresh vars are unified it is said that they *share* or *co-refer*:

.. doctest::
    
    >>> run(fresh(lambda q, z: unify(q, z)))
    [▢₀]
    >>> run(fresh(lambda q, z: conj(unify(q, z), unify(z, 3))), 
    ...     var_selector=lambda q, z: q)
    [3]


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

Facts and recursive relations
-----------------------------

In order to represent *facts* we introduce the :py:obj:`conde` goal ctor,
which is defined as a combination of conjs and disjs and we show how to write
recursive relation, possibly satisfied by a countably infinite number of values.

``conde``
~~~~~~~~~
The following simple example resembles facts declaration in Prolog:

.. doctest::

    >>> run(fresh(lambda q: conde([unify(q, 'orange'), succeed],
    ...                           [unify(q, 'lemon'), fail],
    ...                           [unify(q, 'pear'), succeed],
    ...                           [unify(q, 'apple'), succeed])))
    ['orange', 'pear', 'apple']

``η-inversion``
~~~~~~~~~~~~~~~  

Let us define a relation that yields countably many 5 objects; in order to do
that, the usual solution is to write a recursive definition. However, we
proceed step by step, adjusting and learning from the Python semantic of
argument evaluation at *function-call time*.  Consider the following as initial
definition:

.. doctest::

    >>> def fives(x):
    ...     return disj(unify(5, x), fives(x))
    ...
    >>> run(fresh(lambda x: fives(x)))
    Traceback (most recent call last):
    ...
    RecursionError: maximum recursion depth exceeded while calling a Python object

Exception ``RecursionError`` is raised because in the body of function ``fives`` it
is required to evaluate ``fives(x)`` in order to return a ``disj`` object, but this is
the point from were we started, hence no progress for recursion.

Keeping in mind the previous argument, why not wrapping the recursion on
``fives(x)`` inside a ``fresh`` ctor in order to refresh the var ``x`` at
each invocation?

.. doctest::

    >>> def fives(x):
    ...     return disj(unify(5, x), fresh(lambda x: fives(x)))
    ...
    >>> run(fresh(lambda x: fives(x)))
    Traceback (most recent call last):
    ...
    RecursionError: maximum recursion depth exceeded while calling a Python object

Again the same exception as before, this time for a different reason, however:
since we ask for all associations that satisfy the *countably infinite*
relation ``fives``, function ``run`` continue to look for such values which are
infinite, of course. So, select only the first 10 objects:

.. doctest::

    >>> def fives(x):
    ...     return disj(unify(5, x), fresh(lambda x: fives(x)))
    ...
    >>> run(fresh(lambda x: fives(x)), n=10)
    [5, ▢₀, ▢₀, ▢₀, ▢₀, ▢₀, ▢₀, ▢₀, ▢₀, ▢₀]

Although not a list of 10 fives objects, it makes sense: the very first 5 gets
associated to the var ``x`` introduced by the goal provided to ``run`` by the
``fresh`` ctor, and this association is only one way to satisfy the ``disj`` in
the definition of relation ``fives``. Looking for other associations that work,
we attempt to satisfy the second goal in the ``disj``, namely ``fresh(lambda x:
fives(x))``: it introduces a new var ``x``, different from the previous one,
and then recurs, leaving the original var without association. Since associations shown
in the output list refer to the very first var ``x``, we get many ``▢₀`` symbols
which represent the absence of association, therefore ``x`` remains fresh. 

``fives``
^^^^^^^^^

One way to actually get a list of fives is to unify inside the inner ``fresh``, as follows:

.. doctest::

    >>> def fives(x):
    ...     return disj(unify(5, x), 
    ...                 fresh(lambda y: conj(fives(y), unify(y, x))))
    ...
    >>> run(fresh(lambda x: fives(x)), n=10)
    [5, 5, 5, 5, 5, 5, 5, 5, 5, 5]

or to use ``fresh`` as *η-inversion* rule, as follows:

.. doctest::

    >>> def fives(x):
    ...     return disj(unify(5, x), fresh(lambda: fives(x)))
    ...
    >>> run(fresh(lambda x: fives(x)), n=10)
    [5, 5, 5, 5, 5, 5, 5, 5, 5, 5]

``nats``
^^^^^^^^

Just for fun, using the previous trick and abstracting out the 5s, 
we can generate the naturals, taking only the first 10 as follows:

.. doctest::

    >>> def nats(x, n=0):
    ...     return disj(unify(n, x), fresh(lambda: nats(x, n+1)))
    ...
    >>> run(fresh(lambda x: nats(x)), n=10)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

``append``
^^^^^^^^^^^
Here we want to define the relation ``append(r, s, o)`` which holds if
``r + s == o`` where ``r, s, o`` are both lists. First of all we need an
helper relation ``nullo`` which holds if ``l == []``:

.. doctest::
    
    >>> def nullo(l): 
    ...     return unify([], l)

so it follows the recursive definition, as usual:

.. doctest::

    >>> def append(r, s, out):
    ...     def A(r, out): 
    ...         return conde([nullo(r), unify(s, out)],
    ...                      else_clause=[fresh(lambda a, d, res:
    ...                                            conj(unify([a]+d, r),
    ...                                                 unify([a]+res, out),
    ...                                                 fresh(lambda: A(d, res)),))])
    ...     return A(r, out)

Some examples follow:

.. doctest::

    >>> run(fresh(lambda q: append([1,2,3], [4,5,6], q)))
    [[1, 2, 3, 4, 5, 6]]
    >>> run(fresh(lambda l, q: append([1,2,3]+q, [4,5,6], l)), n=4) #doctest: +NORMALIZE_WHITESPACE
    [[1, 2, 3, 4, 5, 6], 
     [1, 2, 3, ▢₀, 4, 5, 6], 
     [1, 2, 3, ▢₀, ▢₁, 4, 5, 6], 
     [1, 2, 3, ▢₀, ▢₁, ▢₂, 4, 5, 6]]
    >>> run(fresh(lambda r, x, y: 
    ...             conj(append(x, y, ['cake', 'with', 'ice', 'd', 't']),
    ...                  unify([x, y], r)))) #doctest: +NORMALIZE_WHITESPACE
    [[[], ['cake', 'with', 'ice', 'd', 't']], 
     [['cake'], ['with', 'ice', 'd', 't']], 
     [['cake', 'with'], ['ice', 'd', 't']], 
     [['cake', 'with', 'ice'], ['d', 't']], 
     [['cake', 'with', 'ice', 'd'], ['t']], 
     [['cake', 'with', 'ice', 'd', 't'], []]]
        



