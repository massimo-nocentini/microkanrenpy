
*****
Intro
*****

I love *Lisp*, *Python* too. The work I'm going to describe has born *for fun*,
for my education, to bang my head against a taugh, beautiful, not so simple to
grasp yet elegant piece of software which is *ηkanren* [HF13]_, in the
*miniKanren* [RS05]_ family of logic languages.

To be honest, this documentations has many targets:
    
    * it (should) describes what I've done
    * it is used to get credits for my PhD course
    * to clear my thoughts about the system I'm keeping alive
    * to understand and play with documentation tools
    * to write down abstract machines that I believe *charming* and *elegant*
    * to keep one foot in Lisp and the other in Python, however keep coding

I would like to structure my exposition following advices from `an interesting
group of people <write_the_doc_>`_, much more experienced that me on writing
this kind of stuff.

Why write docs
==============

You will be using your code in 6 months (aka, *the future of this project*)
---------------------------------------------------------------------------

The reality:

    I find it best to start off with a selfish appeal. The best reason to write
    docs is because you will be using your code in 6 months. Code that you
    wrote 6 months ago is often indistinguishable from code that someone else
    has written. You will look upon a file with a fond sense of remembrance.
    Then a sneaking feeling of foreboding, knowing that someone less
    experienced, less wise, had written it.

I started to document what I've done because I would like to keep this code
alive, after the core has been proven mature enough, I would like to add
*constraints* [HF15]_, *guided search* [CF15]_ and *uncertainty* [GS17]_.

You want people to use your code
--------------------------------

*If people don't know why your project exists, they won't use it.*
    This project exists mainly *for fun*, to code something beautiful and understand
    core and elegant ideas underlying *logic programming*. In parallel, instead of 
    providing a clone implementation again in Scheme as the original authors do, 
    we prefere to target the *Python* language which allows us to characterize our version with respect to:

        * we stick to the original language as possible, so we use the same names for functions and
          objects; moreover, we adopt the same functional style, without messing up with different paradigms

        * we use native *generator* objects provided by Python to handle relations that can be
          satisfied by both a finite or a *countably* infinite set of substitutions for *logic variables*

        * we rewrite the fundamental function that explores the space of substitutions that satisfy a relation
          as an *iterative* process instead of *recursive*, in this way we lose the elegance of recursion (inspite of
          limit on recursive calls imposed by the language), gaining a *fair* exploration of the solutions space
          even if it infinite respect to both the number of streams and the content in each one of them (
          for more details on the topic, have a look at docstring of function :py:func:`muk.core.mplus`)
          
        * try to write concise, powerful and idiomatic python code for a non-trivial problem, 
          we would like to keep functions and definitions as small and simple as possible; remember the mantra
        
          .. doctest::

              >>> import this 
              The Zen of Python, by Tim Peters
              <BLANKLINE>
              Beautiful is better than ugly.
              Explicit is better than implicit.
              Simple is better than complex.
              Complex is better than complicated.
              Flat is better than nested.
              Sparse is better than dense.
              Readability counts.
              Special cases aren't special enough to break the rules.
              Although practicality beats purity.
              Errors should never pass silently.
              Unless explicitly silenced.
              In the face of ambiguity, refuse the temptation to guess.
              There should be one-- and preferably only one --obvious way to do it.
              Although that way may not be obvious at first unless you're Dutch.
              Now is better than never.
              Although never is often better than *right* now.
              If the implementation is hard to explain, it's a bad idea.
              If the implementation is easy to explain, it may be a good idea.
              Namespaces are one honking great idea -- let's do more of those!


*If people can't figure out how to install your code, they won't use it.*
    All that is required is to have a `Git client <https://git-scm.com/>`_
    available, so type the following in a console:
    
    .. code-block:: shell
        
        git clone https://github.com/massimo-nocentini/on-python.git # get stuff
        cd on-python # go into there
        git checkout microkanren # switch to the right branch
        cd microkanren # go into the correct dir
        python3 # start the Python interpreter
    
    Now in the python interpreter it is possible to load our core module:

    .. code-block:: python
         
        >>> from muk.core import *

    that's it!

*If people can't figure out how to use your code, they won't use it.*
    We provide a simple tutorial in a dedicated page :ref:`primer`.

You want people to help out
---------------------------

*You only get contributions after you have put in a lot of work.*
    We work our ηkanren with:
        
        * the little book [RS05]_ or https://mitpress.mit.edu/books/reasoned-schemer,
          reproducing **all relations** and answering **all questions**: definitions are
          literally included in the page :ref:`reasoned_schemer`, while we record with in a
          `unit test file <reasoned_schemer_unitests_>`_ asserts for each answer given in the book.
        * the puzzle **The Mistery of the Monte Carlo lock** from the book [RS82]_ by Raymond Smullyan,
          where we implement a generic machine based on *inference rules*, coding and plugging in
          those rule necessary to build McCulloch's machines to find **he key of the lock**, finally.
          All defs and some comments are recorded in :ref:`montecarlo_lock` and asserts in a `unit test file <mclock_unitests_>`_.

*You only get contributions after you have users (aka, to whet your appetite).*
    Although I've played with ηkanren mostly by writing down definitions in the
    context of sexp, namely ``cons`` cells manipulations, I believe of interest
    the definition of a generic machine to be configured with *arbitrary inference
    rules*: this allows us to implement a relational interpreter for some *process
    algebras*, one of them is Milner's CCS calculus.

*You only get contributions after you have documentation.*
    I'm building it! Moreover, this is an *executable documentation*: every
    snippet of Python code appearing in these pages, in particular in
    :ref:`primer`, is required to pass in the sense of `doctests
    <https://docs.python.org/3/library/doctest.html>`_, in other words a line
    that fails to produce the expected output does preevent the generation of
    the *whole* documentation. This is possible by running Sphinx with the
    corresponding `doctest extension
    <http://www.sphinx-doc.org/en/stable/ext/doctest.html>`_; moreover,
    this extension runs and checks doctests written in docstrings of **any**
    referenced Python definition stored in source files.





It makes your code better
-------------------------
I would like to enhance each definition in the :py:mod:`muk.core` module with a solid and 
consistent docstring, mainly to clarify my thoughts as done for function :py:func:`muk.core.mplus`
in my humble opinion, where we try to explain different enumeration strategies to achieve
*interleaving* of satisfying substitutions.

Moreover, looking for some chunk of code that needs better doc allows us to find new ideas and 
possible refactorings and/or enhancements, the following is a list of ideas:

    * introduce a ``goal`` class, in order to implement magic methods ``__and__, __or__`` to 
      provide syntactic sugar for goal composition;
    * override method ``__radd__`` in class ``var`` in order to write something like ``[1,2,3]+a``,
      where ``a`` is a logic variable; this should construct an object that represent an *extension list*, 
      currently implemented using ``cons`` objects;
    * override method ``__add__`` in class ``var`` in order to write something like ``a+[1,2,3]``,
      where ``a`` is a logic variable; this should construct an object that represent an *append list* , 
      currently not;
    * from the previous two points would be possible to write ``([1,2,3]+a)-a``, namely a *difference list*
      as provided by standard Prolog.
       
You want to be a better writer
------------------------------
Look at the past

What technology
===============

to be written next!

--------------------------------------------------

.. [HF13]
    Jason Hemann and Daniel P. Friedman,
    *microKanren: A Minimal Functional Core for Relational Programming*, 
    In Proceedings of the 2013 Workshop on Scheme and Functional Programming (Scheme '13), Alexandria, VA, 2013.

.. [HF15]
    Jason Hemann and Daniel P. Friedman,
    *A Framework for Extending microKanren with Constraints*,
    In Proceedings of the 2015 Workshop on Scheme and Functional Programming (Scheme '15), Vancouver, British Columbia, 2015.
   
.. [CF15]
    Cameron Swords and Daniel P. Friedman,
    *rKanren: Guided Search in miniKanren*,
    In Proceedings of the 2013 Workshop on Scheme and Functional Programming (Scheme '13), Alexandria, VA, 2013.

.. [GS17]
    N. D. Goodman and A. Stuhlmüller (electronic),
    *The Design and Implementation of Probabilistic Programming Languages*,
    Retrieved 2017-4-27 from http://dippl.org

.. [RS05]
    Daniel P. Friedman, William E. Byrd and Oleg Kiselyov,
    *The Reasoned Schemer*,
    The MIT Press, Cambridge, MA, 2005

.. [RS82]
    Raymond Eric Smullyan,
    *The Lady or the Tiger*,
    Knopf; 1st edition, 1982

.. _write_the_doc: http://www.writethedocs.org/guide/writing/beginners-guide-to-docs/
.. _reasoned_schemer_unitests: https://github.com/massimo-nocentini/on-python/blob/microkanren/microkanren/reasonedschemer_test.py
.. _mclock_unitests: https://github.com/massimo-nocentini/on-python/blob/microkanren/microkanren/mclock_test.py
