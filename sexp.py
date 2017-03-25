
from collections import namedtuple
from contextlib import contextmanager
from functools import wraps

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

    
def adapt_iterables_to_conses(selector=True):
    def decorator(f):
        @wraps(f)
        def D(*args, bypass_cons_adapter=False):
            if bypass_cons_adapter:
                new_args = args
            else:
                selection = selector(*args) if callable(selector) else args if selector else []
                supported_iterables = (list, tuple,)
                adapter = lambda a: list_to_cons(a) if a in selection and isinstance(a, supported_iterables) else a
                new_args = map(adapter, args)
            return f(*new_args)
        return D
    return decorator





