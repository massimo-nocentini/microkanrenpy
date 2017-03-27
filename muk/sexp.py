
from collections import namedtuple
from contextlib import contextmanager
from functools import wraps
from inspect import signature

cons = namedtuple('cons', ['car', 'cdr'])

class ImproperListError(ValueError):
    pass

def list_to_cons(l):

    λ = type(l) 
    if λ == str:
        return l # we consider a `str` obj not an iterable obj but as an atom

    try:
        car, cadr, *cddr = l

        cddr = λ(cddr) # restore correct type of tail collecting obj
        if cddr == (): return cons(list_to_cons(car), list_to_cons(cadr))
         
        cdr = λ([cadr]) + cddr # reconstruct `cdr` by adapt `[cadr]` to safely apply +
        return cons(car=list_to_cons(car), cdr=list_to_cons(cdr))
    except:

        try:
            car, *cdr = l

            cdr = λ(cdr) # again, restore correct type of the tail
            if cdr == (): raise ImproperListError # otherwise outer try couldn't fail

            return cons(car=list_to_cons(car), cdr=list_to_cons(cdr))
        except ImproperListError:
            raise
        except: 
            return l


def cons_to_list(c, for_cdr=False):

    try:
        car, cdr = c
    except:
        if c == (): raise ImproperListError
        return (([], list) if c == [] else ((c,), tuple)) if for_cdr else c

    d, λ = cons_to_list(cdr, for_cdr=True)
    r = λ([cons_to_list(car, for_cdr=False)]) + d
    return (r, λ) if for_cdr else r

    
def adapt_iterables_to_conses(selector):
    def decorator(f):
        f_sig = signature(f)
        formal_args = [v.name for k, v in f_sig.parameters.items()]
        selection = selector(*formal_args)

        @wraps(f)
        def D(*args, bypass_cons_adapter=False, **kwds):
            new_args = args if bypass_cons_adapter else [list_to_cons(a) if f in selection else a 
                                                         for f, a in zip(formal_args, args)]
            return f(*new_args, **kwds)
        return D
    return decorator


all_arguments = lambda *args: set(args)


