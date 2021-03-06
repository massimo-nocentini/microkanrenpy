
'''

    Laws
    ====

    *law of fresh*
        if x is fresh, then unify(v, x) succeeds and associates x with v    

    *law of unify*
        unify(v, w) is the same as unify(w, v)

    *law of conde*
        to get more values from conde, pretend that the successful conde line
        has failed, refreshing all variables that got an association from that
        line

    Commandments
    ============

    *second*
        to transform a function whose value is not a Boolean into a function
        whose value is a goal, add an extra argument to hold its value, replace
        `cond` with `conde`, and unnest each question and answer. 

    >>> from muk.core import *
    >>> from muk.ext import *
'''

import random, heapq
from collections import namedtuple
from itertools import count, repeat
from contextlib import contextmanager
from inspect import signature
from functools import partial, reduce, wraps

from muk.sexp import *
from muk.utils import *


# STATES {{{

state = namedtuple('state', ['sub', 'next_index'])

def emptystate():
    return state(sub={}, next_index=0)

@contextmanager
def states_stream(g, initial_state=emptystate()):
    α = g(initial_state)
    yield α

# }}}

# DIFFERENCE STRUCTURES {{{

class extend_list:

    def __init__(self, prefix, var):
        self.prefix = prefix
        self.var = var

    def as_cons(self, translate):
        return translate(tuple(self.prefix + [self.var]))

    def walk_star(self, W):
        prefix = W(self.prefix) # foldr(lambda c, acc: [W(c)]+acc, self.prefix, [])
        walked = W(self.var)
        
        if isinstance(walked, extend_list):
            return extend_list(prefix + walked.prefix, walked.var)
        if isinstance(walked, list):
            return prefix + walked
        else:
            return extend_list(prefix, walked)

    def unification(self, other, sub, ext_s, U, E):
        try: 
            UEL = other._unification_extend_list
        except AttributeError:
            try:
                l = len(self.prefix)

                if len(other) < l: raise E

                other_prefix = other[:l]
                other_suffix = other[l:]
            except TypeError: 
                raise E
            else:
                sub_prefix = U(self.prefix, other_prefix, sub, ext_s)
                return U(self.var, other_suffix, sub_prefix, ext_s)
        else: 
            return UEL(self, sub, ext_s, U)

    def _unification_extend_list(self, other, sub, ext_s, U):

        l = len(self.prefix)
        if len(other.prefix) < l:
            return other._unification_extend_list(self, sub, ext_s, U)
        elif l < len(other.prefix):
            other_prefix = other.prefix[:l]
            shorter_extend_list = extend_list(prefix=other.prefix[l:], var=other.var)
            sub_prefix = U(self.prefix, other_prefix, sub, ext_s)
            return U(self.var, shorter_extend_list, sub_prefix, ext_s)
        else:
            sub_prefix = U(other.prefix, self.prefix, sub, ext_s)
            return U(other.var, self.var, sub_prefix, ext_s)

    def _unification_difference_list(self, other, sub, ext_s, U):
        return other.whole._unification_prefix_extend_list(self, sub, ext_s, U)

    def _unification_prefix_extend_list(self, other, sub, ext_s, U):
        return U(self.prefix, other, sub, ext_s)

    def _unification_exclude(self, other, exclude, sub, ext_s, U):
        if exclude == self.var:
            return U(self.prefix, other, sub, ext_s)

        raise NotImplemented

    def reify_s(self, sub, R):
        sub_prefix = foldr(lambda c, sub: R(c, sub), self.prefix, sub)
        return R(self.var, sub_prefix) 

    def occur_check(self, u, O, E):
        for c in self.prefix:
            O(u, c)
        return O(u, self.var)

    def __eq__(self, other):
        try: eq = other.__eq__extend_list
        except AttributeError: return False
        else: return eq(self)

    def __eq__extend_list(self, other):
        return self.prefix == other.prefix and self.var == other.var

    def __repr__(self):
        return '{} + {}'.format(repr(self.prefix), repr(self.var))

    def __radd__(self, other):
        if isinstance(other, list):
            return extend_list(other+self.prefix, self.var)

        raise NotImplemented

    def __sub__(self, other):
        if isinstance(other, var):
            return difference_list(whole=self, suffix=other)

        raise NotImplemented



class difference_list:
    
    def __init__(self, whole, suffix):
        self.whole = whole
        self.suffix = suffix

    def walk_star(self, W):
        whole = W(self.whole)
        suffix = W(self.suffix)
        return [] if whole == suffix else difference_list(whole, suffix)

    def unification(self, other, sub, ext_s, U, E):
        try: 
            UDL = other._unification_difference_list
        except AttributeError:
            if isinstance(other, list):
                try: UP = self.whole._unification_exclude
                except AttributeError: raise E
                else: return UP(other, self.suffix, sub, ext_s, U)
            else:
                raise E
        else: 
            return UDL(self, sub, ext_s, U)

    def _unification_difference_list(self, other, sub, ext_s, U):
        sub_whole = U(other.whole, self.whole, sub, ext_s)
        return U(other.suffix, self.suffix, sub_whole, ext_s)

    def reify_s(self, sub, R):
        sub_whole = R(self.whole, sub)
        return R(self.suffix, sub_whole)

    def occur_check(self, u, O, E):
        raise NotImplemented

        for c in self.prefix: 
            O(u, c)
        return O(u, self.var)

    def __eq__(self, other):
        try: eq = other.__eq__difference_list
        except AttributeError: return False
        else: return eq(self)

    def __eq__difference_list(self, other):
        return self.whole == other.whole and self.suffix == other.suffix

    def __repr__(self):
        return '({}) - {}'.format(repr(self.whole), repr(self.suffix))


# }}}

# VARS {{{


class var:

    def __init__(self, index, name):
        self.index = index
        self.name = name

    def __eq__(self, other):
        try: eq = other.__eq__var
        except AttributeError: return False
        else: return eq(self)

    def __eq__var(self, other):
        return self.index == other.index and self.name == other.name

    def __hash__(self):
        t = self.index, self.name
        return hash(t)

    def __repr__(self):
        return subscript_notation(self.name, self.index)

    def __radd__(self, other):
        
        if isinstance(other, list): 
            return extend_list(prefix=other, var=self)

        raise NotImplemented

    def __sub__(self, other):
        
        if isinstance(other, (list, var)): 
            return difference_list(whole=self, suffix=other)

        raise NotImplemented

    def walk_star(self, W):
        return self

    def reify_s(self, sub, R):
        return ext_s(self, rvar(len(sub)), sub)

    def unification(self, other, sub, ext_s, U, E): 
        try: UV = other._unification_var
        except AttributeError: return ext_s(self, other, sub)
        else: return UV(self, sub, ext_s, U)

    def _unification_var(self, other_var, sub, ext_s, U):
        return sub if self == other_var else ext_s(other_var, self, sub)

    def __getattr__(self, name):

        if not name.startswith('_unification_'): 
            raise AttributeError

        return lambda other, sub, ext_s, U: ext_s(self, other, sub)

    def occur_check(self, u, O, E):
        if self == u: raise E


class rvar(var):

    def __init__(self, index, reifed_name='▢'):
        super().__init__(index, name=reifed_name)
        
    def reify_s(self, sub, R):
        return sub

# }}}

# UNIFICATION {{{

class Tautology:

    def __eq__(self, other):
        return isinstance(other, Tautology)

    def __repr__(self):
        return type(self).__name__

class UnificationError(ValueError):
    pass

def unification(u, v, sub, ext_s):
    '''
    Attempts to augment substitution ``sub`` with associations that makes ``u``
    unify with ``v``.
    '''

    #u, v = walk(u, sub), walk(v, sub)
    u, merged = walk_merging(u, v, sub)
    v = sub[v] if merged else walk(v, sub)

    try: 
        return u.unification(v, sub, ext_s, unification, UnificationError)
    except (AttributeError, UnificationError): pass

    try: 
        return v.unification(u, sub, ext_s, unification, UnificationError)
    except (AttributeError, UnificationError): pass

    if  (type(u) is tuple and type(v) is tuple) or \
        (type(u) is list and type(v) is list):

        if len(u) != len(v): 
            raise UnificationError
        else:
            return reduce(lambda subr, pair: unification(*pair, subr, ext_s), zip(u, v), sub)
    elif u == v:
        return sub

    raise UnificationError()

# }}}

# SUBSTITUTION {{{

def walk_merging(u, other, sub):

    v = u
    changed = False
    merging = False
    try: 
        while True: 
            v = sub[v]
            changed = True
            if v == other: 
                merging = True
    except (TypeError, # to defend against unhashable objs 
            KeyError): # to defend from "ground" objs and stop iter when `u` is a *fresh* var
        pass

    merged = False
    if changed:
        sub[u] = v
        if merging and v != other:
            sub[other] = v
            merged = True

    return v, merged

def walk(u, sub):

    v = u
    changed = False

    try: 
        while True: 
            v = sub[v]
            changed = True
    except (TypeError, # to defend against unhashable objs 
            KeyError): # to defend from "ground" objs and stop iter when `u` is a *fresh* var
        pass

    if changed:
        sub[u] = v

    return v

def walk_star(v, sub):
    v = walk(v, sub)
    if hasattr(v, 'walk_star'): return v.walk_star(partial(walk_star, sub=sub))
    elif isinstance(v, (list, tuple)): return [walk_star(u, sub) for u in v]  
    else: return v

class OccurCheck(ValueError):
    pass

def occur_check(ext_s):

    @wraps(ext_s)
    def E_s(u, v, sub, occur_check=False):
        
        def O(u, v):
            v = walk(v, sub)
            if hasattr(v, 'occur_check'): 
                v.occur_check(u, O, OccurCheck)
            elif type(v) is tuple or isinstance(v, list): 
                for vv in v: O(u, vv)

        if occur_check: O(u, v)

        return ext_s(u, v, sub)

    return E_s

@occur_check
def ext_s(u, v, sub):

    if u in sub: # check to ensure consistency of previously unified values
        if sub[u] != v: raise UnificationError
        else: return sub

    e = sub.copy()
    e[u] = v
    return e

def reify_s(v, sub):
    v = walk(v, sub)
    if hasattr(v, 'reify_s'): return v.reify_s(sub, reify_s)
    elif isinstance(v, list): return reduce(lambda sub, u: reify_s(u, sub), v, sub)
    else: return sub

def reify(v):
    return walk_star(v, reify_s(v, sub={}))

# }}}

# GOAL CTORS {{{

class goal(object):

    def __or__(self, g):
        return _disj(self, g, interleaving=True)

    def __xor__(self, g):
        return _disj(self, g, interleaving=False)

    def __matmul__(self, g):
        return _conj(self, g, interleaving=True)

    def __and__(self, g):
        return _conj(self, g, interleaving=False)

    def __invert__(self):
        return complement(self)

class primitive(goal):

    def __init__(self, rule):
        self.rule = rule

    def __call__(self, s : state):
        yield from iter(self.rule(s))

succeed = primitive(rule=lambda s: [s]) # a goal that is satisfied by *any* substitution
fail = primitive(rule=lambda s: [])     # a goal that is satisfied by *no* substitution

class _unify(goal):
    '''
    Attempts to perform :py:func:`unification <muk.core.unification>` to make
    ``u`` and ``v`` unifiable given a set of associations for logic variables.
    '''

    def __init__(self, u, v, ext_s):
        self.u = u
        self.v = v
        self.ext_s = ext_s


    def __call__(self, s : state):
        try: 
            sub = unification(self.u, self.v, s.sub, self.ext_s)
        except UnificationError: 
            yield from fail(s)
        else: 
            yield from succeed(state(sub, s.next_index))

class fresh(goal):
    '''
    Introduce new logic variables according to the needs of receiver ``f``.

    If ``f`` is a thunk then ``fresh`` is equivalent to the inversion of η-rule 
    as defined in *higher-order* logic::

        def η_inverse(t):

            def I(s : state):
                g = t()
                yield from g(s)

            return I

    having particular application in the definition of *recursive* relations.

    '''

    def __init__(self, f, arity=None):
        self.f = f
        if arity:
            self.params = [(i, n) for i in range(arity) for n in [chr(ord('a') + i)]]
        else:
            f_sig = signature(f)
            arity = len(f_sig.parameters)
            self.params = [(i, v.name) for i, (k, v) in enumerate(f_sig.parameters.items())] 

    def __call__(self, s : state):
        logic_vars = [var(s.next_index+i, n) for (i, n) in self.params]
        setattr(self, 'logic_vars', logic_vars) # set the attr in any case, even if `logic_vars == []` because of η-inversion  
        g = self.f(*logic_vars)
        new_s = state(s.sub, s.next_index + len(logic_vars))
        α = g(new_s)
        yield from α

        ''' 
        for v in logic_vars:
            try:
                del new_s.sub[v]
            except KeyError:
                pass
        '''

class _disj(goal):
    '''
    A goal that is satisfiable if *either* goal ``g1`` *or* goal ``g2`` is satisfiable.

    Formally, it produces the following states space:

    .. math::

         \left( \\begin{array}{c}s \stackrel{g_{1}}{\\mapsto} \\alpha \\\\ s \stackrel{g_{2}}{\\mapsto} \\beta \\end{array}\\right)
          = \left( \\begin{array}{ccccc}        
                s_{00} & s_{01} & s_{02} & s_{03} & \\ldots \\\\
                s_{10} & s_{11} & s_{12} & s_{13} & \\ldots \\\\
                \\end{array}\\right)

    enumerated using ``mplus`` according to ``interleaving`` arg.
    
    '''

    def __init__(self, g1, g2, *, interleaving):
        self.g1 = g1
        self.g2 = g2
        self.interleaving = interleaving
    
    def __call__(self, s : state):
        α, β = self.g1(s), self.g2(s)
        yield from mplus(iter([α, β]), self.interleaving)
        


class _conj(goal):
    '''
    A goal that is satisfiable if *both* goal ``g1`` *and* goal ``g2`` is satisfiable.

    Formally, it produces the following states space:

    .. math::

        s \stackrel{g_{1}}{\\mapsto} \\alpha = \left( \\begin{array}{c}s_{0}\\\\s_{1}\\\\s_{2}\\\\ s_{3}\\\\ \\ldots\\end{array}\\right)
          \stackrel{bind(\\alpha, g_{2})}{\\mapsto} \left( \\begin{array}{ccccc}        
                                                s_{00} & s_{01} & s_{02} & s_{03} & \\ldots \\\\
                                                s_{10} & s_{11} & s_{12} & \\ldots &        \\\\
                                                s_{20} & s_{21} & \\ldots &        &         \\\\
                                                s_{30} & \\ldots &        &        &         \\\\
                                                \\ldots &        &        &        &         \\\\
                                                \\end{array}\\right)
    
    '''

    def __init__(self, g1, g2, *, interleaving):
        self.g1 = g1
        self.g2 = g2
        self.interleaving = interleaving

    def __call__(self, s : state):
        α = self.g1(s)
        yield from bind(α, repeat(self.g2), mplus=partial(mplus, interleaving=self.interleaving))

class complement(goal):

    def __init__(self, g):
        self.g = g

    def __call__(self, s : state):
        α = self.g(s)
        try:
            r = next(α) # r : state 
        except StopIteration:
            yield from succeed(s)
        else:
            yield from fail(s)    


# }}}

# STATE STREAMS {{{

def mplus(streams, interleaving):
    '''
    It enumerates the states space ``streams``, using different strategies
    according to ``interleaving``.

    In order to understand states enumeration can be helpful to use a matrix,
    where we associate a row to each stream of states α belonging to
    ``streams``.  Since ``streams`` is an ``iter`` obj over a *countably*,
    possibly infinite, set of *states streams*, the matrix could have infinite
    rows.  In parallel, since each states stream α lying on a row is a ``iter``
    obj over a *countably*, possibly infinite, set of *satisfying states*, the
    matrix could have infinite columns; therefore, the matrix we are building
    could be infinite in both dimensions. So, let ``streams`` be represented as follows:


    .. math::

        \left( \\begin{array}{ccccc}        
        s_{00} & s_{01} & s_{02} & s_{03} & \\ldots \\\\
        s_{10} & s_{11} & s_{12} & \\ldots &        \\\\
        s_{20} & s_{21} & \\ldots &        &         \\\\
        s_{30} & \\ldots &        &        &         \\\\
        \\ldots &        &        &        &         \\\\
        \\end{array}\\right)

    In order to enumerate this infinite matrix we have the following strategies:

    *depth-first*
        Enumerates a stream α committed to it until it is saturated or continue to yield its
        ``state`` objects forever; in other words, it enumerates row by row. For the sake of clarity,
        assume the first :math:`k` streams are finite and the :math:`k`-th is the first to be infinite, hence
        we are in the following context:

        .. math::

            \left( \\begin{array}{ccccc}        
            s_{00} & s_{01} & \\ldots & s_{0i_{0}} \\\\
            s_{10} & s_{11} & \\ldots & s_{1i_{1}} \\\\
            \ldots_{\\triangle} \\\\
            s_{k-1, 0} & s_{k-1,1} & \\ldots &  s_{k-1,i_{k-1}} \\\\
            s_{k0} & s_{k1} & \\ldots &  \ldots &  \ldots \\\\
            s_{k+1, 0} & \\ldots &        &   \\\\
            \\ldots &        &        &   \\\\
            \\end{array}\\right)

        so enumeration proceeds as follows: :math:`s_{00}, s_{01},\\ldots,
        s_{0i_{0}}, s_{10}, s_{11}, \\ldots, s_{1i_{1}}, \\ldots_{\\triangle}, s_{k-1,0},
        s_{k-1, 1},\\ldots, s_{k-1,i_{k-1}}, s_{k0}, s_{k1},\\ldots` yielding from stream :math:`\\alpha_{k}` forever,
        *never* reaching :math:`s_{k+1, 0}`.

    *breadth-first*
        Enumerates interleaving *state* objects belonging to adjacent streams,
        lying on the same column; in other words, it enumerates column by
        column. If ``streams`` is an iterator over an infinite set of streams,
        the it enumerates only the very first ``state`` objects, namely
        :math:`s_{00}, s_{10}, s_{20}, s_{30},\ldots`. 
        
        The following is a straighforward implementation::

            from itertools import chain

            while True:
                try: 
                    α = next(streams)
                except StopIteration: 
                    break
                else:
                    try:
                        s = next(α) # s : state 
                    except StopIteration:
                        continue
                    else:
                        yield s
                        streams = chain(streams, [α])

    *dovetail*
        Enumerates interleaving `state` objects lying on the same *diagonal*,
        resulting in a *fair scheduler* in the sense that *every* satisfying
        ``state`` object will be reached, eventually. For the sake of clarity,
        enumeration proceeds as follows: 
        
        .. math::

            s_{00}, s_{10}, s_{01}, s_{20}, s_{11}, s_{02}, s_{30}, s_{21},
            s_{12}, s_{03}, \\ldots

        providing a *complete* enumeration strategy.


    :param iter stream: an iterator over a *countable* set of ``state``-streams
    :param bool interleaving: enumeration strategy selector: *dovetail* if ``interleaving`` else *depth-first*
    :return: an ``iter`` object over satisfying ``state`` objects
    
    '''
    
    if interleaving:

        try: α = next(streams)
        except StopIteration: return
        else: S = [α]

        fringe = []
        diagonal = 1

        '''
        class HQ:
            def push(self, s):
                heapq.heappush(fringe, (1/diagonal, random.random(), s))
            def pop(self):
                d, tie_breaker, s = heapq.heappop(fringe)
                return s

        class L:
            def push(self, s):
                fringe.append(s)
            def pop(self):
                return fringe.pop() 

        strategy = L()
        '''

        while S:

            for j in reversed(range(len(S))):
                β = S[j]
                try: s = next(β)
                except StopIteration: del S[j]
                else: yield s
                #else: strategy.push(s)
            
            '''
            if fringe: 
                #yield from iter(fringe)
                #random.shuffle(fringe)
                s = strategy.pop()
                yield s
            '''

            try: α = next(streams)
            except StopIteration: pass
            else: S.append(α)

            diagonal += 1

            #random.shuffle(S) # the following shuffling should be used if `fringe` is a vanilla list
    else:

        for α in streams: yield from α


                

def bind(α, goals, *, mplus):
    '''
    A stream combinator, it applies goal ``g`` to each ``state`` in stream ``α``.

    Such mapping can be *linear* in the sense of vanilla ``map`` application:

    .. math::

        \\alpha = \left( \\begin{array}{c}s_{0}\\\\s_{1}\\\\s_{2}\\\\ s_{3}\\\\ \\ldots\\end{array}\\right)
          \stackrel{map(g, \\alpha)}{\\mapsto} \left( \\begin{array}{ccccc}        
                                                s_{00} & s_{01} & s_{02} & s_{03} & \\ldots \\\\
                                                s_{10} & s_{11} & s_{12} & \\ldots &        \\\\
                                                s_{20} & s_{21} & \\ldots &        &         \\\\
                                                s_{30} & \\ldots &        &        &         \\\\
                                                \\ldots &        &        &        &         \\\\
                                                \\end{array}\\right)

    After the mapping obj is built, it is consumed as argument by ``mplus`` to
    enumerate the states space.

    Moreover, a recursive implementation can be written as found in *The
    Reasoned Schemer*, but in some cases it raises ``RecursionError`` due to
    Python limitation on stack usage::

        try:
            s = next(α) # s : state 
        except StopIteration:
            yield from fail()
        else:
            β = g(s)
            γ = bind(α, g, mplus)
            yield from mplus(iter([β, γ]))

    which produces the following states space:

    .. math::

        \\alpha = \left( \\begin{array}{c}s_{0}\\\\s_{1}\\\\s_{2}\\\\ s_{3}\\\\ \\ldots\\end{array}\\right)
          \stackrel{bind(\\alpha, g)}{\\mapsto} \left( \\begin{array}{l}        
                                                s_{00} \, s_{01} \, s_{02} \, s_{03} \, s_{04} \,s_{05} \,\\ldots \\\\
                                                \left( \\begin{array}{l}
                                                s_{10} \, s_{11} \, s_{12} \, \\ldots \,        \\\\
                                                \left( \\begin{array}{l}        
                                                s_{20} \, s_{21} \, \\ldots \,        \,         \\\\
                                                \left( \\begin{array}{l}        
                                                s_{30} \, \\ldots \,        \,        \,         \\\\
                                                \\ldots \,        \,        \,        \,         \\\\
                                                \\end{array}\\right)
                                            \\end{array}\\right)
                                        \\end{array}\\right)
                                    \\end{array}\\right)

    assuming we want to enumerate using interleaving:

    .. math::

        s_{00}, s_{10}, s_{01}, s_{20}, s_{02}, s_{11}, s_{03}, s_{30}, s_{04}, s_{12}, s_{05}, s_{21}\ldots

    which, although *complete*, is *unbalanced* in favor of first streams.

    :param iter α: an iterator over a *countable* set of ``state`` objects
    :param goal g: a relation to be satisfied
    :param callable mplus: states space enumeration strategy
    :return: an ``iter`` object over satisfying ``state`` objects
    '''
    yield from mplus(g(s) for g, s in zip(goals, α))

# }}}

# INTERFACE {{{

def run(goal, 
        n=False, 
        var_selector=lambda *args: args[0],
        post=lambda r: cons_to_list(r) if isinstance(r, cons) else r):
    '''
    Looks for a list of at most ``n`` associations ``[(u, v) for v in ...]``
    such that when var ``u`` takes value ``v`` the relation ``goal`` is
    satisfied, where ``u`` is the *main var* respect the whole ``run``
    invocation; otherwise, it enumerates the relation if ``n`` is ``False``.

    :param goal: the relation to be satisfied respect to the main var according to :py:obj:`var_selector`.



    '''

    with states_stream(goal) as α:
        domain = range(n) if n else count()
        subs = [a.sub for i, a in zip(domain, α)]

    logic_vars = getattr(goal, 'logic_vars', None) # defaults to `None` instead of `[]` to distinguish attr set by `_fresh` 
    m_var = var_selector(*logic_vars) if logic_vars else Tautology() # any satisfying sub is a Tautology if there are no logic vars

    def λ(sub): 
        w_var = walk_star(m_var, sub) # instantiate every content in the expr associated to `main_var` in `sub` to the most specific value
        r_var = reify(w_var)
        return post(r_var)

    return list(map(λ, subs))


# }}}


