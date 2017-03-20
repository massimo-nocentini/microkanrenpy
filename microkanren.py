
from collections import namedtuple
from itertools import chain

state = namedtuple('state', ['sub', 'next_index'])
cons = namedtuple('cons', ['car', 'cdr'])


def list_to_cons(l):
    try:
        λ = type(l) 
        car, *cdr = l
        cdr = λ(cdr)
        return cons(car=list_to_cons(car), cdr=list_to_cons(cdr))
    except:
        return l

def cons_to_list(c, for_cdr=False):

    try:
        car, cdr = c
    except:
        return ((c, type(c)) if c == [] or c == () else ((c,), tuple)) if for_cdr else c
    
    d, λ = cons_to_list(cdr, for_cdr=True)
    r = λ([cons_to_list(car, for_cdr=False)]) + d
    return (r, λ) if for_cdr else r

def emptystate():
    return state(sub={}, next_index=0)

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
    
def walk(u, sub):
    return walk(sub[u], sub) if is_var(u) and u in sub else u

def walk_star(v, sub):
    v = walk(v, sub)
    if is_var(v): return v  
    elif isinstance(v, list): return [walk_star(u, sub) for u in v]  
    elif isinstance(v, cons): return cons(walk_star(v.car, sub), walk_star(v.cdr, sub))
    else: return v

def ext_s(u, v, sub):
    e = sub.copy()
    e[u] = v
    return e

# Goal ctor {{{

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

def conde(clauses, else_clause=[fail]):
    return disj(*[conj(*clause) for clause in clauses], conj(*else_clause))

def _disj(g1, g2):
    
    def D(s : state):
        yield from mplus(g1(s), g2(s))
        
    return D

def disj(*goals):
    g, *gs = goals
    return _disj(g, disj(*gs)) if gs else _disj(g, fail)

def _conj(g1, g2):

    def C(s : state):
        yield from bind(g1(s), g2)

    return C

def conj(*goals):
    g, *gs = goals
    return _conj(g, conj(*gs)) if gs else _conj(g, succeed)

# }}}

# state-streams ctor {{{

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
    else:
        try:
            caru, *cdru = u
            carv, *cdrv = v
            car_sub = unification(caru, carv, sub)
            return unification(cdru, cdrv, car_sub)
        except:
            if u == v: return sub

    raise UnificationError()

def run(goal, n=False, v=var(0), post=lambda arg: arg):
    subs = []
    α = goal(emptystate())
    for i, a in enumerate(α):
        subs.append(a.sub)
        if n and i == n-1: break

    λ = lambda sub: post(walk_star(v, sub))
    return list(map(λ, subs))

def nullo(l):
    return unify([], l)

def conso(a, d, p):
    return unify(cons(a, d), p) 

def pairo(p):
    return fresh(lambda a, d: conso(a, d, p), arity=2)

def caro(p, a):
    return fresh(lambda d: conso(a, d, p))

def cdro(p, d):
    return fresh(lambda a: conso(a, d, p))

def listo(l):
    return conde([  [nullo(l), succeed],
                    #[pairo(l), fresh(lambda d: conj(cdro(l, d), snooze(listo, [d])))]
                    [pairo(l), fresh(lambda d: conj(cdro(l, d), listo(d)))]
                    ])

'''
def caro(p, a):

    #fresh(lambda d: conj(listo(d), conso(a, d, p)))

    def A(d):
        car, *rest = p
        return conj(unify(car, a), unify(rest, d))

    return fresh(A)

    #return fresh(lambda d: unify([a] + d, p))
'''


