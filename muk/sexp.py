
from collections import namedtuple
from contextlib import contextmanager
from functools import wraps
from inspect import signature

def identity(a):
    return a

cons = namedtuple('cons', ['car', 'cdr'])

class ImproperListError(ValueError):
    pass

def list_to_cons(l):

    λ = type(l) 
    if λ == str or λ == cons:
        return l # we consider a `str` obj not an iterable obj but as an atom

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


def num(i): 
    return list(map(int, reversed(bin(i)[2:]))) if i else []





