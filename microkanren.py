
from collections import namedtuple
from itertools import chain
from contextlib import contextmanager
from inspect import signature
from functools import wraps

from sexp import cons, cons_to_list, list_to_cons 


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

    subscripts = {'0':'₀', '1':'₁','2':'₂','3':'₃','4':'₄','5':'₅','6':'₆','7':'₇','8':'₈','9':'₉'}

    def __init__(self, index, name='v'):
        self.index = index
        self.name = name
        self.is_var = True

    def __eq__(self, other):
        # a more performant, yet not functional, should be 
        #return self is other
        return self.index == other.index if is_var(other) else False

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

class UnificationError(ValueError):
    pass

def adapt_iterables_to_conses(selector=True):
    def decorator(f):
        @wraps(f)
        def D(*args):
            selection = selector(*args) if callable(selector) else args if selector else []
            new_args = [list_to_cons(a) 
                        if a in selection and isinstance(a, (list, tuple, )) else a # should be interesting to handle `str` objects natively
                        for a in args]
            return f(*new_args)
        return D
    return decorator

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

@adapt_iterables_to_conses()
def unify(u, v):

    def U(s : state):
        try:
            sub = unification(u, v, s.sub)
            yield from unit(state(sub, s.next_index))
        except UnificationError:
            yield from mzero()

    return U

def fresh(f):
    '''
    def η_inverse(t):

        def I(s : state):
            g = t()
            yield from g(s)

        return I
    '''
    def F(s : state):
        f_sig = signature(f)
        arity = len(f_sig.parameters)
        logic_vars = [var(s.next_index + i) for i in range(arity)] 
        F.logic_vars = logic_vars
        g = f(*logic_vars)
        yield from g(state(s.sub, s.next_index + arity))

    return F

def snooze(f, formal_vars):
    return fresh(lambda: f(*formal_vars))

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
    try: a = next(α)
    except StopIteration: yield from mzero()
    else: yield from mplus(g(a), bind(α, g))

# }}}

# INTERFACE {{{

def run(goal, n=False, v=lambda *args: args[0] if args else None, post=lambda arg: arg):

    subs = []
    α = goal(emptystate())
    for i, a in enumerate(α):
        subs.append(a.sub)
        if n and i == n-1: break

    def λ(sub): 
        main_var = v(*goal.logic_vars) if hasattr(goal, 'logic_vars') else True
        r = walk_star(main_var, sub)
        return cons_to_list(r) if isinstance(r, cons) else post(r)

    return list(map(λ, subs))

# }}}


