
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
'''

from collections import namedtuple
from itertools import chain, count
from contextlib import contextmanager
from inspect import signature
from functools import partial, reduce, wraps

from muk.sexp import *


# STATES {{{

state = namedtuple('state', ['sub', 'next_index'])

def emptystate():
    return state(sub={}, next_index=0)

@contextmanager
def states_stream(g, initial_state=emptystate()):
    α = g(initial_state)
    yield α

# }}}

# VARS {{{


class var:

    _subscripts = {'0':'₀', '1':'₁','2':'₂','3':'₃','4':'₄','5':'₅','6':'₆','7':'₇','8':'₈','9':'₉'}

    def __init__(self, index, name):
        self.index = index
        self.name = name

    def __eq__(self, other):
        try:
            return other.__eq__var(self)
        except AttributeError:
            return False

    def __eq__var(self, other):
        return self.index == other.index and self.name == other.name

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

    def walk_star(self, W):
        return self

    def reify_s(self, sub, R):
        return ext_s(self, rvar(len(sub)), sub)

    def unification(self, other, sub, ext_s, U, E): 
        try:
            UV = other._unification_var
        except AttributeError:
            return ext_s(self, other, sub)   
        else:
            return UV(self, sub, ext_s, U)

    def _unification_var(self, other_var, sub, ext_s, U):
        return sub if self == other_var else ext_s(other_var, self, sub)

    def _unification_cons(self, other_cons, sub, ext_s, U):
        return ext_s(self, other_cons, sub)

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

    u, v = walk(u, sub), walk(v, sub)

    if hasattr(u, 'unification'): 
        try: return u.unification(v, sub, ext_s, unification, UnificationError)
        except UnificationError: pass

    if hasattr(v, 'unification'): 
        try: return v.unification(u, sub, ext_s, unification, UnificationError)
        except UnificationError: pass

    if  (type(u) is tuple and type(v) is tuple) or \
        (isinstance(u, list) and isinstance(v, list)):
        # this branch permits either `u` or `v` to be `cons` cells too:
        # can be source of trouble or should be a kind of generalization
        u, v = iter(u), iter(v)
        subr = reduce(lambda subr, pair: unification(*pair, subr, ext_s), zip(u, v), sub)
        try: next(u)
        except StopIteration:
            try: next(v)
            except StopIteration:
                # because both iterables are empty, so there's no
                # counterexample against their unification
                return subr 
    elif u == v:
        return sub
    else:
        raise UnificationError()

# }}}

# SUBSTITUTION {{{

def walk(u, sub):

    try: 
        while True: u = sub[u]
    except (TypeError, # to defend against unhashable objs 
            KeyError): # to defend from "ground" objs and stop iter when `u` is a *fresh* var
        return u 

def walk_star(v, sub):
    v = walk(v, sub)
    if isinstance(v, list): return [walk_star(u, sub) for u in v]  
    elif hasattr(v, 'walk_star'): return v.walk_star(lambda u: walk_star(u, sub))
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

    if False:
        if not isinstance(u, var): 
            raise ValueError("Non `var` obj {} as key in substitution {}".format(u, sub))

        if u == v: 
            raise ValueError('Illegal identity association between {} and {}, according to 9.12 of The Reasoned Schemer'.format(u, v))
            
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

def succeed(s : state):
    ''' A goal that is satisfied by any substitution '''
    yield from unit(s)

def fail(s : state):
    yield from mzero()

def _unify(u, v, ext_s):

    def U(s : state):
        try: sub = unification(u, v, s.sub, ext_s)
        except UnificationError: yield from mzero()
        else: yield from unit(state(sub, s.next_index))

    return U

def _unify_pure(u, v, occur_check):
    return _unify(u, v, partial(ext_s, occur_check=occur_check))

def _unify_occur_check(u, v):

    U = _unify_pure(u, v, occur_check=True)

    def U_oc(s : state):
        try:
            yield from U(s)
        except OccurCheck:
            yield from mzero()

    return U_oc

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
        setattr(F, 'logic_vars', logic_vars) # set the attr in any case, even if `logic_vars == []` because of η-inversion  
        g = f(*logic_vars)
        α = g(state(s.sub, s.next_index + arity))
        yield from α

    return F

def _disj(g1, g2, *, interleaving):
    
    def D(s : state):
        α, β = g1(s), g2(s)
        yield from mplus(iter([α, β]), interleaving)
        
    return D

def _conj(g1, g2, *, interleaving):

    def C(s : state):
        α = g1(s)
        yield from bind(α, g2, interleaving)

    return C

def if_pure(question, answer, otherwise, *, interleaving):
    
    def I(s : state):
        C = _conj(question, answer, interleaving=False) 
        α, β = C(s), otherwise(s)
        yield from mplus(iter([α, β]), interleaving)

    return I

ife = partial(if_pure, interleaving=False)
ifi = partial(if_pure, interleaving=True)

def if_softcut(question, answer, otherwise, *, doer):

    def I(s : state):
        α = question(s) 
        try:
            r : state = next(α)
        except StopIteration: 
            β = otherwise(s) 
            yield from β
        else:
            γ = doer(r, α, answer)
            yield from γ

    return I

ifa = partial(if_softcut, doer=lambda r, α, answer: bind(chain([r], α), answer, interleaving=False))
ifu = partial(if_softcut, doer=lambda r, α, answer: answer(r))

@contextmanager
def delimited(d):

    available = iter(range(d)) if d else count()

    def one_more():
        try: next(available)
        except StopIteration: return False
        else: return True

    def D(g): 
        def G(s : state):
            α = g(s) if one_more() else mzero()
            yield from α
                
        return G

    yield D

def project(*logic_vars, into):

    def P(s : state):
        walked_vars = [walk_star(v, s.sub) for v in logic_vars]
        g = into(*walked_vars)
        α = g(s) 
        yield from α

    return P

def sub(*logic_vars, of):

    def λ(s : state):  
        lvars = set(logic_vars) if logic_vars else s.sub.keys()
        return state({v:{v:s.sub[v]} for v in lvars if v in s.sub}, s.next_index)
        
    def S(s : state):
        α = of(s) 
        yield from map(λ, α)

    return S

def complement(g):

    def C(s : state):
        α = g(s)
        try:
            r : state = next(α)
        except StopIteration:
            yield from unit(s)
        else:
            yield from mzero()    

    return C

# }}}

# STATE STREAMS {{{

def unit(s : state):
    yield from iter([s])

def mzero(s : state = None):
    yield from iter([])

def mplus(streams, interleaving):

    if interleaving:
        while True:
            try:
                α = next(streams)
            except StopIteration:
                break
            else:
                try:
                    s : state = next(α)
                except StopIteration:
                    continue # to the next stream because stream α has been exhausted 
                else:
                    yield s
                    streams = chain(streams, [α])
    else:
        for α in streams: yield from α

def bind(α, g, interleaving):
    streams = (β for s in α for β in [g(s)])
    yield from mplus(streams, interleaving)
    '''
    try:
        s : state = next(α)
    except StopIteration:
        yield from mzero()
    else:
        β = g(s)
        γ = bind(α, g, interleaving)
        yield from mplus(iter([β, γ]), interleaving)
    '''

# }}}

# INTERFACE {{{

def run(goal, n=False, 
        var_selector=lambda *args: args[0],
        post=lambda r: cons_to_list(r) if isinstance(r, cons) else r):
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


