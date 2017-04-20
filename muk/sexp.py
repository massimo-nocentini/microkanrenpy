
from collections import namedtuple
from contextlib import contextmanager
from functools import wraps
from inspect import signature

from muk.utils import identity

class cons(namedtuple('_cons', ['car', 'cdr'])):

    def walk_star(self, W):
        return cons(W(self.car), W(self.cdr))

    def unification(self, other, sub, ext_s, U, E):
        try: UC = other._unification_cons
        except AttributeError: raise E
        else: return UC(self, sub, ext_s, U)

    def _unification_cons(self, other_cons, sub, ext_s, U):

        if other_cons.cdr == (): return U(other_cons.car, self, sub, ext_s)
        if self.cdr == (): return U(self.car, other_cons, sub, ext_s)

        cars_sub = U(other_cons.car, self.car, sub, ext_s)
        return U(other_cons.cdr, self.cdr, cars_sub, ext_s)

    def reify_s(self, sub, R):
        return R(self.cdr, R(self.car, sub))

    def occur_check(self, u, O, E):
        return O(u, self.car) or O(u, self.cdr)

    def __radd__(self, other):
        
        if isinstance(other, list):
            return list_to_cons(other, post=lambda l: self if l == [] else l)

        raise NotImplemented

class ImproperListError(ValueError):
    pass

def list_to_cons(l, post=identity):

    if isinstance(l, (str, cons)): return l # we consider a `str` obj not an iterable obj but as an atom

    λ = type(l) 
    try:
        car, cadr, *cddr = l
    except:
        try:
            car, *cdr = l
        except: 
            return l
        else:
            cdr = λ(cdr) # again, restore correct type of the tail
            if cdr == (): raise ImproperListError # otherwise outer try couldn't fail
            cdr = post(cdr)
            return cons(car=list_to_cons(car), cdr=list_to_cons(cdr))
    else:
        cddr = λ(cddr) # restore correct type of tail collecting obj
        if cddr == (): return cons(car=list_to_cons(car), cdr=list_to_cons(cadr))
        cdr = λ([cadr]) + cddr # reconstruct `cdr` by adapt `[cadr]` to safely apply +
        return cons(car=list_to_cons(car), cdr=list_to_cons(cdr))


def cons_to_list(c, for_cdr=False):

    try:
        car, cdr = c
    except:
        if c == (): raise ImproperListError
        return (([], list) if c == [] else ((c,), tuple)) if for_cdr else c

    d, λ = cons_to_list(cdr, for_cdr=True)
    r = λ([cons_to_list(car, for_cdr=False)]) + d
    return (r, λ) if for_cdr else r

    
def adapt_iterables_to_conses(selector, ctor=list_to_cons):
    def decorator(f):
        f_sig = signature(f)
        formal_args = [v.name for k, v in f_sig.parameters.items()]
        selection = selector(*formal_args)
        if isinstance(selection, set): 
            selection = {s:ctor for s in selection}

        @wraps(f)
        def D(*args, bypass_cons_adapter=False, **kwds):
            new_args = args if bypass_cons_adapter else [c(a) for f, a in zip(formal_args, args) 
                                                              for c in [selection.get(f, identity)]]
            return f(*new_args, **kwds)
        return D
    return decorator


all_arguments = lambda *args: set(args)

def int_to_list(i):
    return list(map(int, reversed(bin(i)[2:]))) if i else []

class num(cons): 

    @classmethod
    def build(cls, obj):
        if isinstance(obj, int): obj = int_to_list(obj)
        c = list_to_cons(obj)
        return num(c.car, c.cdr) if isinstance(c, cons) else c

    def __int__(self):
        def I(c, e):
            return 0 if c == [] else c.car * 2**e + I(c.cdr, e+1)
        return I(self, e=0)




