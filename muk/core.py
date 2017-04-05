
'''
    __Laws__

    ● law of fresh
        if x is fresh, then unify(v, x) succeeds and associates x with v    
    ● law of unify
        unify(v, w) is the same as unify(w, v)
    ● law of conde
        to get more values from conde, pretend that the successful conde line
        has failed, refreshing all variables that got an association from that
        line

    __Commandments__

    ● second
        to transform a function whose value is not a Boolean into a function
        whose value is a goal, add an extra argument to hold its value, replace
        `cond` with `conde`, and unnest each question and answer. 
'''

from collections import namedtuple, Iterable
from itertools import chain, count
from contextlib import contextmanager
from inspect import signature
from functools import partial, reduce

from muk.sexp import *


# STATES {{{

state = namedtuple('state', ['sub', 'next_index'])

def emptystate():
    return state(sub={}, next_index=0)

@contextmanager
def states_stream(g, initial_state=emptystate()):
    yield g(initial_state)

# }}}

# VARS {{{


class var:

    _subscripts = {'0':'₀', '1':'₁','2':'₂','3':'₃','4':'₄','5':'₅','6':'₆','7':'₇','8':'₈','9':'₉'}
    _default_var_name = '▢'

    def __init__(self, index, name=None):
        if name == self._default_var_name: 
            raise ValueError

        self.index = index
        self.name = name if name else self._default_var_name
        self.is_var = True

    def __eq__(self, other):
        return self.index == other.index and self.name == other.name if is_var(other) else False

    def __hash__(self):
        t = self.index, self.name
        return hash(t)

    def __repr__(self):
        return '{}{}'.format(self.name, ''.join(self._subscripts[c] for c in str(self.index)))

    def __radd__(self, other):
        
        if isinstance(other, list): 
            # according to *chicken scheme*, function `append` is defined only
            # on proper lists, unless the very last one which is allowed to be
            # an improper list. Therefore, we discard the case of `other` to be
            # a `tuple`, which means `other` is an improper list, so we append
            # `self` to the end and, finally, make the entire obj a `tuple`
            # because `self` is a logic variable that can be unified with *any*
            # value, not just [] to be proper lists.
            return tuple(other + [self])
        #if isinstance(other, str): 
            #return tuple(list(other) + [self])

        raise NotImplemented

    def __add__(self, other):
        
        raise NotImplemented

        # although the following implementation seems reasonable, it permits
        # `unify([3,[4,5],6], x + ([4, y], z))` to bind `x` to `3` whereas the
        # correct deduction should be `x==[3]`.  In other words, it does the
        # work of `appendo`.
        if isinstance(other, (list, tuple)):
            λ = type(other) 
            return λ([self]) + other

def is_var(obj):
    return getattr(obj, 'is_var', False)

class pvar:

    _unique_id = count()

    def __init__(self):
        self.index = next(self._unique_id)

    def __hash__(self):
        t = (self.index, self.__class__.__name__)
        return hash(t)

    def __eq__(self, other):
        return other is self   

# }}}

# UNIFICATION {{{

class Tautology:

    def __eq__(self, other):
        return isinstance(other, Tautology)

    def __repr__(self):
        return type(self).__name__

class UnificationError(ValueError):
    pass

def unification(u, v, sub):
    u, v = walk(u, sub), walk(v, sub)
    if is_var(u) and is_var(v) and u == v: return sub
    elif is_var(u): return ext_s(u, v, sub)
    elif is_var(v): return ext_s(v, u, sub)
    elif isinstance(u, cons) and isinstance(v, cons):
        if u.cdr == tuple():
            return unification(u.car, v, sub)
        if v.cdr == tuple():
            return unification(v.car, u, sub)
        else:
            cars_sub = unification(u.car, v.car, sub)
            return unification(u.cdr, v.cdr, cars_sub)
    elif isinstance(u, (tuple, list)) and isinstance(v, (tuple, list)):
        # this branch permits either `u` or `v` to be `cons` cells too:
        # can be source of trouble or should be a kind of generalization
        u, v = iter(u), iter(v)
        subr = reduce(lambda subr, pair: unification(*pair, subr), zip(u, v), sub)
        try:
            u0 = next(u)
        except StopIteration:
            try:
                v0 = next(v)
            except StopIteration:
                return subr # because both iterables are empty, so there's no counterexample against their unification
    elif u == v:
        return sub

    raise UnificationError()

# }}}

# SUBSTITUTION {{{

def walk(u, sub):
    return walk(sub[u], sub) if is_var(u) and u in sub else u

def walk_star(v, sub):
    v = walk(v, sub)
    if is_var(v): return v  
    elif isinstance(v, list): return [walk_star(u, sub) for u in v]  
    elif isinstance(v, cons): return cons(walk_star(v.car, sub), walk_star(v.cdr, sub))
    else: return v

def ext_s(u, v, sub):

    if u in sub: # check to ensure consistency of previously unified values
        if sub[u] != v: raise UnificationError
        else: return sub

    e = sub.copy()
    e[u] = v
    return e

def reify(v, sub):
    v = walk(v, sub)
    if is_var(v): return ext_s(v, var(len(sub)), sub)
    elif isinstance(v, cons): return reify(v.cdr, reify(v.car, sub))
    elif isinstance(v, list): return reduce(lambda sub, u: reify(u, sub), v, sub)
    else: return sub

# }}}

# GOAL CTORS {{{

def succeed(s : state):
    yield from unit(s)

def fail(s : state):
    yield from mzero()

@adapt_iterables_to_conses(all_arguments)
def unify(u, v):

    def U(s : state):
        try:
            sub = unification(u, v, s.sub)
            yield from unit(state(sub, s.next_index))
        except UnificationError:
            yield from mzero()

    return U


def fresh(f, arity=None):
    '''
    def η_inverse(t):

        def I(s : state):
            g = t()
            yield from g(s)

        return I
    '''

    if arity:
        params = [(i, n) for i in range(arity) for n in [chr(ord('a') + i)]]
    else:
        f_sig = signature(f)
        arity = len(f_sig.parameters)
        params = [(i, v.name) for i, (k, v) in enumerate(f_sig.parameters.items())] 

    def F(s : state):
        logic_vars = [var(s.next_index+i, n) for (i, n) in params]
        setattr(F, 'logic_vars', logic_vars) # set the attribute in any case, even if `logic_vars == []` for η-inversion  
        g = f(*logic_vars)
        yield from g(state(s.sub, s.next_index + arity))

    return F

def _disj(g1, g2, interleaving):
    
    def D(s : state):
        yield from mplus(g1(s), g2(s), interleaving)
        
    return D

def _conj(g1, g2, interleaving):

    def C(s : state):
        yield from bind(g1(s), g2, interleaving)

    return C

def _delimited(d, pv, g):

    def B(s : state):
        sub = s.sub.copy()
        sub[pv] = sub.get(pv, 0) + 1
        yield from g(state(sub, s.next_index)) if sub[pv] <= d else mzero()

    return B

# }}}

# STATE STREAMS {{{

def unit(s : state):
    yield from iter([s])

def mzero(s : state = None):
    yield from iter([])

def mplus(α, β, interleaving):

    if interleaving:
        while True:
            try:
                a = next(α)
            except StopIteration:
                yield from β
                break
            else:
                yield a
                α, β = β, α
    else:
        yield from chain(α, β)

def bind(α, g, interleaving):
    try: a = next(α)
    except StopIteration: yield from mzero()
    else: yield from mplus(g(a), bind(α, g, interleaving), interleaving)


# }}}

# INTERFACE {{{

def run(goal, n=False, 
        var_selector=lambda *args: args[0],
        post=lambda arg: arg):
    '''
    Returns a list [v ...] of associations (u, v) ... for the var `u` subject of the `run`

    __Args__
    goal:
        a goal obj to be satisfied
    var_selector:
        a callable that consumes a list of formal vars used in the goal, usually built by `fresh`.
        It is mandatory to return exactly one var, which becomes the subject of this run.
    post:
        a callable to be applied to each satisfying value `v` for the subject var, before returning.
    '''

    with states_stream(goal) as α:
        subs = [a.sub for i, a in zip(range(n) if n else count(), α)]

    logic_vars = getattr(goal, 'logic_vars', None) # defaults to `None` instead of `[]` to distinguish attr set by `_fresh` 
    main_var = var_selector(*logic_vars) if logic_vars else Tautology() # any satisfying sub is a Tautology if there are no logic vars

    def λ(sub): 
        r = walk_star(main_var, sub) # instantiate every content in the expr associated to `main_var` in `sub` to the most specific value
        reified_sub = reify(r, sub={}) # reify the most specific instantiation in order to hide impl details from vars names
        r = walk_star(r, reified_sub) # finally, reduce the most specific instantiation to use vars hiding
        return post(cons_to_list(r) if isinstance(r, cons) else r) # apply `post` processing for pretty printing

    return list(map(λ, subs))


# }}}


