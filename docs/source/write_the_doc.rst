
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
group of people <write_the_doc_>`_ much more experienced that me on writing
this kind of stuff; consequently, in what follows you will find the same
sections as you find in the referenced page, hoping to provide answers and to
taylor paragraphs to this particular project. Quoting their `Sidebar on open source
<http://www.writethedocs.org/guide/writing/beginners-guide-to-docs/#you-want-people-to-use-your-code>`_:

    There is a magical feeling that happens when you release your code. It comes in
    a variety of ways, but it always hits you the same. Someone is using my code?!
    A mix of terror and excitement.

        I made something of value!
        What if it breaks?!
        I am a real open source developer!
        Oh god, someone else is using my code...

    Writing good documentation will help alleviate some of these fears. A lot of
    this fear comes from putting something into the world. My favorite quote about
    this is something along these lines:

        Fear is what happens when you're doing something important.
        If you are doing work that isn't scary,
        it isn't improving you or the world.

    Congrats on being afraid! It means you're doing something important.

from my little and humble position, I'm proud to have been afraid as I was doing
all this stuff...

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
          `unit test file <reasoned_schemer_unitests_>`_ about **350 asserts** to cover questions in the book;
        * the puzzle **The Mistery of the Monte Carlo lock** from the book [RS82]_ by Raymond Smullyan,
          where we implement a generic machine based on *inference rules*, coding and plugging in
          those rule necessary to build McCulloch's machines to find **he key of the lock**, finally.
          All defs and some comments are recorded in :ref:`montecarlo_lock` and
          in the `tests suite <mclock_unitests_>`_ there are about **60 asserts**.


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
       
You want to be a better writer (aka, *looking at the past*)
-----------------------------------------------------------
I use this section to summarize references and existing works. 

First of all, thank you `William E. Byrd <http://webyrd.net/>`_ for your hard
work.  Will wrote his PhD thesis [WB09]_ and shared a series of hangout video lectures
known as `miniKanran uncourse
<https://www.youtube.com/playlist?list=PLO4TbomOdn2cks2n5PvifialL8kQwt0aW>`_; moreover,
he is a coauthor of [RS05]_ and maintains a tremendous archive at http://minikanren.org/, 
where it is possible to find references to scientific publications, existing implementation in lots of
different programming languages and, finally, links to talks presented in many confs, all of this stuff
related to the field of *relational programming*.

Python implementations
~~~~~~~~~~~~~~~~~~~~~~

According to Will, we just review the following existing projects:
 
`pykanren <https://github.com/jtauber/pykanren>`_
    which implements the very basic definitions of the core system of both
    miniKanren and ηkanren: variables, unification only for `list` objects,
    reification and a complete enumeration strategy in the style of [RS05]_
    without *interleaving* of satisfying substitutions. Tests are present to
    catch the essentials, no application to particular problems.

`pythological <https://github.com/darius/pythological>`_
    which implements a *domain specific language* in the style of Prolog
    clauses on top of Python. The core interpreter uses primitive *generators*
    as we do, implements all the basic definitions of the logic system with
    *interleaving* and *occur-check* to detect circular substitutions. In my
    opinion it is an interesting project due to the parsing of the dsl which we do
    not provide; for what concerns testing, there are no test suites but simple
    and nice examples written in the defined language.
    
`logpy <https://github.com/logpy/logpy>`_
    which implements the core system, supports relations satisfiable by
    infinite substitutions using primitive Python generator objects and
    the style is close to the canonical version, although not closer; in
    in our humble opinion, the code seems a bit complex to read and understand
    because of the presence of many auxiliary functions to handle streams of
    satisfying substitutions and to combine goals. Moreover, this project
    aims to extend unification over objects of arbitrary types using two
    dependencies to perform *double dispatching* and *structural unification*,
    which we aim to reach just by sending messages in a more pure and fundamental
    way keeping the *Smalltalk way* as tenet.

`microkanren <https://gist.github.com/cheery/d89bfb4c8d6c7a3eb908>`_
    which implements the very very basic implementation in about 100 lines of
    code: due to its brevity, it supplies variables, primitive goals, disjs and
    conjs as combinators, without interleaving and tests. It is released as a
    GitHub gist.

In spite of these existing projects, our main principle is to remain as close
as possible to ideas presented in [HF13]_: we use the same names for functions
as they use in the paper and we write definitions in the same *purely
functional style*. This allows us to preserve compact and concise defs, most of
them do not exceed 5 lines of code.  A drawback is some boilerplate and
redundancy, which can be seen immediately in the unit tests, due to the
presence of many ``lambda`` expressions and to the repeated use of ``run``,
``fresh`` and ``conj``. Finally, our main contribution comprises two test suites,
the first reproduces all examples (including those about the *discrete logarithm*)
of [RS05]_, the second solves a logic puzzle by building an abstract machine composing
inference rules.
 
Lisp implementation
~~~~~~~~~~~~~~~~~~~~
There are many implementation in the Lisp family:

    * for vanilla `Scheme <https://www.call-cc.org/>`_ there are the 
      `canonical one <https://github.com/jasonhemann/microKanren>`_,
      `with symbolic constraints <https://github.com/webyrd/miniKanren-with-symbolic-constraints>`_,
      `with probabilistic inference <https://github.com/webyrd/probKanren>`_ and
      `with guided search <https://github.com/cgswords/rkanren>`_;
      finally, I'm particular interested in a `recent impl <https://github.com/orchid-hybrid/microKanren-sagittarius>`_
      which uses the last `r7rs <http://trac.sacrideo.us/wg/wiki/R7RSHomePage>`_ Scheme standard.
    * for `Clojure <https://clojure.org/>`_ there is the outstanding 
      `core.logic <https://github.com/clojure/core.logic>`_ maintained by `David Nolen <https://github.com/swannodette>`_; 
      otherwise, two plain ports for `Racket <https://github.com/webyrd/miniKanren-with-symbolic-constraints>`_ and for
      `CommonLisp <https://common-lisp.net/project/cl-kanren-trs/>`_, respectively.  

Other languages and links
~~~~~~~~~~~~~~~~~~~~~~~~~
I would like to list some resources that I've discovered in the meanwhile:

`ηkanren in Haskell <https://www.msully.net/blog/2015/02/26/microkanren-%CE%BCkanren-in-haskell/>`_
    a blog post by *Michael J. Sullivan*, also a `recorded talk <https://skillsmatter.com/skillscasts/6523-hello-declarative-world>`_
`ηkanren in Ruby <https://github.com/tomstuart/kanren>`_
    a Ruby implementation by *Tom Stuart*
`Hakaru <http://indiana.edu/~ppaml/HakaruTutorial.html>`_
    an embedded probabilistic programming language in Haskell
`Logic Programming <https://www.cs.cmu.edu/~fp/courses/lp/index.html>`_
    15-819K Logic Programming course, Fall 2006, taught by prof. *Frank Pfenning*
`Prolog course <https://www.cl.cam.ac.uk/teaching/0809/Prolog/>`_
    Prolog course, 2008–09, Principal lecturer: Dr *David Eyers*

What technology
===============

Information for people who want to contribute back
--------------------------------------------------
I think that `GitHub <https://github.com/>`_ is a very strong platform where we
can keep alive this project.  Moreover, I think also that the decentralized
model and the `workflow <https://guides.github.com/introduction/flow/>`_
proposed by GitHub itself, which is based on `pull requests
<https://help.github.com/articles/about-pull-requests/>`_, is a clean and
healthy methodology to do development. Therefore, I would like to accept
contributions according to this settings, using facilities provided by the
platform to do discussions and to track issues.  Finally, here is the address
of the repository:

    https://github.com/massimo-nocentini/on-python

Together with simplicity and elegance, we believe that *automated testing* is a
vital principle to keep the code base healthy. Therefore, we try to capture
almost every idea with unit tests as much as we can and documentation is no
exception, namely every code snippet in the documentation and every doctest in
docstrings should pass against their asserts in order to produce this
documentation itself.

README.rd first
---------------
As raccomanded by `this article <http://tom.preston-werner.com/2010/08/23/readme-driven-development.html>`_,
have a look to our `README.md <https://github.com/massimo-nocentini/on-python/blob/master/README.md>`_ first.

How to get support
------------------
If you are having issues, please let us know and feel free to drop me an
email at massimo.nocentini@unifi.it for any info you would like to known. 


Your project's license
----------------------

Copyright 2017 Massimo Nocentini

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
of the Software, and to permit persons to whom the Software is furnished to do
so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

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

.. [WB09]
     William E. Byrd,
     *Relational Programming in miniKanren: Techniques, Applications, and Implementations*,
     Ph.D. thesis, Indiana University, Bloomington, IN, 2009.

.. _write_the_doc: http://www.writethedocs.org/guide/writing/beginners-guide-to-docs/
.. _reasoned_schemer_unitests: https://github.com/massimo-nocentini/on-python/blob/master/microkanren/reasonedschemer_test.py
.. _mclock_unitests: https://github.com/massimo-nocentini/on-python/blob/master/microkanren/mclock_test.py
