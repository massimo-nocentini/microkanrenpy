
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

`succeed` and `fail`: primitive goals
--------------------

The two primitive goals are ``succedd`` and ``fail`` which denotes *truth* and
*falsehood* in standard logic. Both of them are implemented as functions as any
other goals:

.. doctest::

    >>> succeed
    <function succeed at ...
    >>> fail
    <function fail at ...

On the other hand their interpretation 

.. doctest::
    
    >>> run(succeed)
    [Tautology]
