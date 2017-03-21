
from collections import namedtuple
from itertools import chain

from sexp import *

# STATES {{{

state = namedtuple('state', ['sub', 'next_index'])

def emptystate():
    return state(sub={}, next_index=0)

# }}}

# VARS {{{

class var:

    subscripts = {'0':'₀', '1':'₁','2':'₂','3':'₃','4':'₄','5':'₅','6':'₆','7':'₇','8':'₈','9':'₉'}

    def __init__(self, index):
        self.index = index
        self.is_var = True

    def __eq__(self, other):
        # a more performant, yet not functional, should be 
        #return self is other
        return self.index == other.index if is_var(other) else False

    def __hash__(self):
        return hash(self.index)

    def __repr__(self, varname='v'):
        return '{}{}'.format(varname, ''.join(self.subscripts[c] for c in str(self.index)))

def is_var(obj):
    return getattr(obj, 'is_var', False)
    
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

    if u in sub and sub[u] != v: 
        raise UnificationError

    e = sub.copy()
    e[u] = v
    return e

# }}}

# GOAL CTORS {{{

def succeed(s : state):
    yield from unit(s)

def fail(s : state):
    yield from mzero()

def unify(u, v):

    def U(s : state):
        try:
            sub = unification(u, v, s.sub)
            yield from unit(state(sub, s.next_index))
        except UnificationError:
            yield from mzero()

    return U

def fresh(f, arity=1):
    '''
    def η_inverse(t):

        def I(s : state):
            g = t()
            yield from g(s)

        return I
    '''
    def F(s : state):
        g = f(*[var(s.next_index + i) for i in range(arity)])
        yield from g(state(s.sub, s.next_index + arity))

    return F

def snooze(f, formal_vars):
    return fresh(lambda: f(*formal_vars), arity=0)

def conde(*clauses, else_clause=[fail]):
    conjuctions = [conj(*clause) for clause in clauses]
    return disj(*conjuctions, conj(*else_clause))

def _disj(g1, g2):
    
    def D(s : state):
        yield from mplus(g1(s), g2(s))
        
    return D

def _conj(g1, g2):

    def C(s : state):
        yield from bind(g1(s), g2)

    return C

def disj(*goals):
    g, *gs = goals
    return _disj(g, disj(*gs)) if gs else _disj(g, fail)

def conj(*goals):
    g, *gs = goals
    return _conj(g, conj(*gs)) if gs else _conj(g, succeed)

# }}}

# STATE STREAMS {{{

def unit(s : state):
    yield from iter([s])

def mzero(s : state = None):
    yield from iter([])

def mplus(α, β, interleaving=True):

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

def bind(α, g):
    '''
    try:
        car = next(α)
    except StopIteration:
        yield from mzero()
    else: 
        yield from mplus(g(car), bind(α, g))
    '''
    a = next(α)
    yield from mplus(g(a), bind(α, g))

# }}}

# UNIFICATION {{{

class UnificationError(ValueError):
    pass

def unification(u, v, sub):
    u, v = walk(u, sub), walk(v, sub)
    if is_var(u) and is_var(v) and u == v: return sub
    elif is_var(u): return ext_s(u, v, sub)
    elif is_var(v): return ext_s(v, u, sub)
    elif (hasattr(u, 'func') and hasattr(u, 'args') 
             and hasattr(v, 'func') and hasattr(v, 'args')):
        func_sub = unification(u.func, v.func, sub)
        return unification(u.args, v.args, func_sub)
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

# INTERFACE {{{

def run(goal, n=False, v=var(0), post=lambda arg: arg):
    subs = []
    α = goal(emptystate())
    for i, a in enumerate(α):
        subs.append(a.sub)
        if n and i == n-1: break

    λ = lambda sub: post(walk_star(v, sub))
    return list(map(λ, subs))

# }}}

