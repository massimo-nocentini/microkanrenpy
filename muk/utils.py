
from itertools import tee

def iterwrap(obj, classes=(tuple,)):
    return obj if isinstance(obj, classes) else [obj]

def foldr(λ, lst, initialize):

    def F(lst):
        if lst:
            car, *cdr = lst
            return λ(car, F(cdr))
        else:
            return initialize

    return F(lst)

def empty_iterable(α):
    α0, α = tee(α)
    try: next(α0)
    except StopIteration: return True
    else: return False

