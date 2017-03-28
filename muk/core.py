
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

'''

from collections import namedtuple
from itertools import chain
from contextlib import contextmanager
from inspect import signature
from functools import partial, reduce
from itertools import count

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

default_var_name = '▢'

class var:

    subscripts = {'0':'₀', '1':'₁','2':'₂','3':'₃','4':'₄','5':'₅','6':'₆','7':'₇','8':'₈','9':'₉'}

    def __init__(self, index, name=default_var_name):
        self.index = index
        self.name = name if name is default_var_name else '{}_{}'.format(default_var_name, name)
        self.is_var = True

    def __eq__(self, other):
        # a more performant, yet not functional, should be 
        #return self is other
        return self.index == other.index and self.name == other.name if is_var(other) else False
        #return self.index == other.index if is_var(other) else False

    def __hash__(self):
        return hash(self.index)

    def __repr__(self):
        return '{}{}'.format(self.name, ''.join(self.subscripts[c] for c in str(self.index)))

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
    else:
        try:
            caru, *cdru = u
            carv, *cdrv = v
            car_sub = unification(caru, carv, sub)
            return unification(cdru, cdrv, car_sub)
        except:
            if u == v: return sub

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

def reify(v, sub, var_name):
    v = walk(v, sub)
    if is_var(v): return ext_s(v, var(len(sub), var_name), sub)
    elif isinstance(v, cons): return reify(v.cdr, reify(v.car, sub, var_name), var_name)
    elif isinstance(v, list) and v: return reduce(lambda sub, u: reify(u, sub, var_name), v, sub)
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


def _fresh(f, assembler):
    '''
    def η_inverse(t):

        def I(s : state):
            g = t()
            yield from g(s)

        return I
    '''

    f_sig = signature(f)
    arity = len(f_sig.parameters)

    def F(s : state):
        logic_vars = [var(s.next_index+i, v.name) 
                      for i, (k, v) in enumerate(f_sig.parameters.items())] 
        if logic_vars:
            setattr(F, 'logic_vars', logic_vars)
        subgoals = f(*logic_vars) # syntactic sugar: it allows `f` to return a tuple of goals
        g = assembler(subgoals) # assemble goal(s) according to the plugged-in strategy (`conj` and `disj` usually)
        yield from g(state(s.sub, s.next_index + arity))

    return F

def _disj(g1, g2, interleaving):
    
    def D(s : state):
        yield from mplus(g1(s), g2(s), interleaving)
        
    return D

def _conj(g1, g2):

    def C(s : state):
        yield from bind(g1(s), g2, interleaving=False)

    return C

# }}}

# STATE STREAMS {{{

def unit(s : state):
    yield from iter([s])

def mzero(s : state = None):
    yield from iter([])

def mplus(α, β, interleaving):

    if interleaving:
        try:
            a = next(α)
        except StopIteration:
            yield from β
        else:
            yield a
            yield from mplus(β, α, interleaving)
    else:
        yield from chain(α, β)

def bind(α, g, interleaving):
    try: a = next(α)
    except StopIteration: yield from mzero()
    else: yield from mplus(g(a), bind(α, g, interleaving), interleaving)

# }}}

# INTERFACE {{{

'''
it should be interesting to add a `str` selector for `run` instead of a
callable selector (which is more general, however), in order to specify the
name of the variable we want to project in the result.
'''

def run(goal, n=False, 
        var_selector=lambda *args: (args[0], default_var_name) if args else (None, None), 
        post=lambda arg: arg):

    with states_stream(goal) as α:
        subs = [a.sub for i, a in zip(range(n) if n else count(), α)]

    def λ(sub): 
        main_var, var_name = var_selector(*getattr(goal, 'logic_vars', (Tautology(), None)))
        r = walk_star(main_var, sub)
        reified = reify(r, {}, var_name)
        r = walk_star(r, reified)
        return post(cons_to_list(r) if isinstance(r, cons) else r)

    return list(map(λ, subs))


# }}}


