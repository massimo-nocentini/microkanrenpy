
.. _primer:

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
    >>> from muk.utils import *


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
    >>> run(fresh(lambda q, z: unify(q, z) & unify(z, 3)), 
    ...     var_selector=lambda q, z: q)
    [3]


``disj``
~~~~~~~~

It is a goal ctor that consumes two goals and returns a new goal that can be
satisfied when *either* the former *or* the latter goal can be satisfied:

.. doctest::

    >>> run(succeed | fail)
    [Tautology]
    >>> run(fail | fresh(lambda q: unify(q, True)))
    [Tautology]
    >>> run(fresh(lambda q: fail | fail))
    []
    >>> run(fresh(lambda q: unify(q, False) | unify(q, True)))
    [False, True]


``conj``
~~~~~~~~

It is a goal ctor that consumes two goals and returns a new goal that can be
satisfied when *both* the former *and* the latter goal can be satisfied:

.. doctest::

    >>> run(succeed & fail)
    []
    >>> run(fail & fresh(lambda q: unify(q, True)))
    []
    >>> run(fresh(lambda q: unify(q, 3) & succeed))
    [3]
    >>> run(fresh(lambda q: unify(q, False) & unify(q, True)))
    []
    >>> run(fresh(lambda q: fresh(lambda q: unify(q, False)) &
    ...                     unify(q, True)))
    [True]

Facts and recursive relations
-----------------------------

In order to represent *facts* we introduce the :py:obj:`conde` goal ctor,
which is defined as a combination of conjs and disjs and we show how to write
recursive relation, possibly satisfied by a countably infinite number of values.

``conde``
~~~~~~~~~
The following simple example resembles facts declaration in Prolog about the father and
grandfather toy example:

.. doctest::

    >>> def father(p, s):
    ...     return conde([unify(p, 'paul'), unify(s, 'jason')],
    ...                  [unify(p, 'john'), unify(s, 'henry')],
    ...                  [unify(p, 'jason'), unify(s, 'tom')],
    ...                  [unify(p, 'peter'), unify(s, 'brian')],
    ...                  [unify(p, 'tom'), unify(s, 'peter')])
    ...
    >>> def grand_father(g, s):
    ...     return fresh(lambda p: father(g, p) & father(p, s))
    ...
    >>> run(fresh(lambda rel, p, s: grand_father(p, s) & unify([p, s], rel)))
    [['paul', 'tom'], ['jason', 'peter'], ['tom', 'brian']]


``η-inversion``
~~~~~~~~~~~~~~~  

Let us define a relation that yields countably many 5 objects; in order to do
that, the usual solution is to write a recursive definition. However, we
proceed step by step, adjusting and learning from the Python semantic of
argument evaluation at *function-call time*.  Consider the following as initial
definition:

.. doctest::

    >>> def fives(x):
    ...     return unify(5, x) | fives(x)
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
    ...     return unify(5, x) | fresh(lambda x: fives(x))
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
    ...     return unify(5, x) | fresh(lambda x: fives(x))
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
    ...     return unify(5, x) | fresh(lambda y: fives(y) & unify(y, x))
    ...
    >>> run(fresh(lambda x: fives(x)), n=10)
    [5, 5, 5, 5, 5, 5, 5, 5, 5, 5]

or to use ``fresh`` as *η-inversion* rule, as follows:

.. doctest::

    >>> def fives(x):
    ...     return unify(5, x) | fresh(lambda: fives(x))
    ...
    >>> run(fresh(lambda x: fives(x)), n=10)
    [5, 5, 5, 5, 5, 5, 5, 5, 5, 5]

``nats``
^^^^^^^^

Just for fun, using the previous trick and abstracting out the 5s, 
we can generate the naturals, taking only the first 10 as follows:

.. doctest::

    >>> def nats(x, n=0):
    ...     return unify(n, x) | fresh(lambda: nats(x, n+1))
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
    ...                      else_clause=fresh(lambda a, d, res:
    ...                                            unify([a]+d, r) &
    ...                                            unify([a]+res, out) &
    ...                                            fresh(lambda: A(d, res))))
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
    ...             append(x, y, ['cake', 'with', 'ice', 'd', 't']) &
    ...             unify([x, y], r))) #doctest: +NORMALIZE_WHITESPACE
    [[[], ['cake', 'with', 'ice', 'd', 't']], 
     [['cake'], ['with', 'ice', 'd', 't']], 
     [['cake', 'with'], ['ice', 'd', 't']], 
     [['cake', 'with', 'ice'], ['d', 't']], 
     [['cake', 'with', 'ice', 'd'], ['t']], 
     [['cake', 'with', 'ice', 'd', 't'], []]]
        

Interleaving
~~~~~~~~~~~~

Let us now define an operator ``repeat`` which makes relations that succeed by
unifying the curried variable with some plugged in object, infinitely many
times:

.. doctest::

    >>> def repeat(r):
    ...     def R(x):
    ...         return unify(x, r) | fresh(lambda: R(x))
    ...     return R
    ...

consequently, use it to define four streams of numbers:

.. doctest::

    >>> ones = repeat(1)
    >>> twos = repeat(2)
    >>> threes = repeat(3)
    >>> fours = repeat(4)


In the following example we use ``conde``, which yields solutions of a cond
line staying there when that line supplies multiple satisfying states, here
infinite when it meets ``fives``, by the way:

.. doctest::

    >>> def facts(x):
    ...     return conde([unify(x, 'hello'), succeed],
    ...                  [unify(x, 'pluto'), succeed],
    ...                  [fives(x), succeed],
    ...                  [unify(x, 'topolino'), succeed],
    ...                  else_clause=unify(x, 'paperone'))
    ...
    >>> run(fresh(lambda x: facts(x)), n=10)
    ['hello', 'pluto', 5, 5, 5, 5, 5, 5, 5, 5]
    >>> groups_with_positions_notation(_)
    hello₀
    pluto₁
    5₂, 5₃, 5₄, 5₅, 5₆, 5₇, 5₈, 5₉


On the other hand, ``condi`` allows us to explore the solutions space by interleaving:

.. doctest::

    >>> def facts(x):
    ...     return condi([unify(x, 'hello'), succeed],
    ...                  [unify(x, 'pluto'), succeed],
    ...                  [fives(x), succeed],
    ...                  [ones(x), succeed],
    ...                  else_clause=unify(x, 'paperone'))
    ...
    >>> run(fresh(lambda x: facts(x)), n=15)
    ['hello', 'pluto', 5, 1, 5, 'paperone', 1, 5, 1, 5, 1, 5, 1, 5, 1]
    >>> groups_with_positions_notation(_)
    hello₀
    pluto₁
    5₂, 5₄, 5₇, 5₉, 5₁₁, 5₁₃
    1₃, 1₆, 1₈, 1₁₀, 1₁₂, 1₁₄
    paperone₅

Now, use only streams of numbers defined before and ask for the first 20
associations that satisfy their ``condi`` combination, providing the keyword argument ``dovetail=False``
which *associates streams on the right*:

.. doctest::

    >>> run(fresh(lambda q: condi([succeed, ones(q)],
    ...                           [succeed, twos(q)],
    ...                           [succeed, threes(q)],
    ...                           [succeed, fours(q)], 
    ...                           dovetail=False)), n=20)
    ...
    [1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3]
    >>> groups_with_positions_notation(_)
    1₀, 1₂, 1₄, 1₆, 1₈, 1₁₀, 1₁₂, 1₁₄, 1₁₆, 1₁₈
    2₁, 2₅, 2₉, 2₁₃, 2₁₇
    3₃, 3₁₁, 3₁₉
    4₇, 4₁₅

on the contrary, using ``dovetail=True`` allows us to get a more balanced
interleaving (this is the default behaviour):

.. doctest::

    >>> run(fresh(lambda q: condi([succeed, ones(q)],
    ...                           [succeed, twos(q)],
    ...                           [succeed, threes(q)],
    ...                           [succeed, fours(q)])), n=20)
    ...
    [1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 4, 3, 2, 1, 4, 3, 2, 1, 4, 3]
    >>> groups_with_positions_notation(_)
    1₀, 1₂, 1₅, 1₉, 1₁₃, 1₁₇
    2₁, 2₄, 2₈, 2₁₂, 2₁₆
    3₃, 3₇, 3₁₁, 3₁₅, 3₁₉
    4₆, 4₁₀, 4₁₄, 4₁₈

Previous expression is equivalent to combining streams with ``disj`` getting
the same behavior of the last but one using the same keyword argument:

.. doctest::

    >>> run(fresh(lambda q: disj(ones(q), twos(q), threes(q), fours(q), 
    ...                          dovetail=False)), n=20)
    [1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3]
    >>> groups_with_positions_notation(_)
    1₀, 1₂, 1₄, 1₆, 1₈, 1₁₀, 1₁₂, 1₁₄, 1₁₆, 1₁₈
    2₁, 2₅, 2₉, 2₁₃, 2₁₇
    3₃, 3₁₁, 3₁₉
    4₇, 4₁₅

Finally, it is possible to request a *fair enumeration* by *dovetail* strategy,
setting the keyword argument ``dovetail=True``, which is the default behavior:

.. doctest::

    >>> run(fresh(lambda q: disj(ones(q), twos(q), threes(q), fours(q))), n=20)
    [1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 4, 3, 2, 1, 4, 3, 2, 1, 4, 3]
    >>> groups_with_positions_notation(_)
    1₀, 1₂, 1₅, 1₉, 1₁₃, 1₁₇
    2₁, 2₄, 2₈, 2₁₂, 2₁₆
    3₃, 3₇, 3₁₁, 3₁₅, 3₁₉
    4₆, 4₁₀, 4₁₄, 4₁₈

As the last but one example, combining streams with the binary operator ``|``
yields a yet different result because the *disjunction binary operator
associates on the left*:

.. doctest::

    >>> run(fresh(lambda q: ones(q) | twos(q) | threes(q) | fours(q)), n=20)
    [1, 4, 3, 4, 2, 4, 3, 4, 1, 4, 3, 4, 2, 4, 3, 4, 1, 4, 3, 4]
    >>> groups_with_positions_notation(_)
    1₀, 1₈, 1₁₆
    4₁, 4₃, 4₅, 4₇, 4₉, 4₁₁, 4₁₃, 4₁₅, 4₁₇, 4₁₉
    3₂, 3₆, 3₁₀, 3₁₄, 3₁₈
    2₄, 2₁₂

Difference structures
~~~~~~~~~~~~~~~~~~~~~


The following implementation of ``appendo`` uses *difference lists*:

.. doctest::

    >>> def appendo(X, Y, XY):
    ...     return fresh(lambda α, β, γ: unify(X, α-β) & 
    ...                                  unify(Y, β-γ) & 
    ...                                  unify(XY, α-γ))
    ...

and can be used as follows:

.. doctest::

    >>> run(fresh(lambda αβ, α, β: appendo(([1,2,3]+α)-α, ([4,5,6]+β)-β, αβ)))
    [([1, 2, 3, 4, 5, 6] + ▢₀) - ▢₀]
    >>> run(fresh(lambda out, X, Y, α, β:  
    ...         appendo(([1,2,3]+α)-α, ([4,5,6]+β)-β, X-Y) & 
    ...         unify([X, Y], out)))
    [[[1, 2, 3, 4, 5, 6] + ▢₀, ▢₀]]

