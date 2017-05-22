
import sys

from itertools import tee
from contextlib import contextmanager
from collections import OrderedDict

numerical_subscripts = {'0':'₀', '1':'₁','2':'₂','3':'₃','4':'₄','5':'₅','6':'₆','7':'₇','8':'₈','9':'₉'}

def identity(a):
    return a

def pairwise(iterable):
    "s -> (s0,s1), (s1,s2), (s2, s3), ..."
    a, b = tee(iterable)
    next(b, None)
    return zip(a, b)

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

@contextmanager
def recursion_limit(n):
    previous = sys.getrecursionlimit()
    sys.setrecursionlimit(n)
    yield
    sys.setrecursionlimit(previous)

@contextmanager
def let(*args):
    yield (args[0] if len(args) == 1 else args)

def subscript_notation(obj, subscript):
    return '{}{}'.format(str(obj), ''.join(numerical_subscripts[c] for c in str(subscript)))

class groups_with_positions_notation:

    def __init__(self, iterable):
        M = OrderedDict()
        for i, o in enumerate(iterable):
            if o not in M: M[o] = [] 
            M[o].append(subscript_notation(o, i))
        
        self.M = M
        self.representation = '\n'.join([', '.join(v) for k, v in M.items()])

    def __repr__(self):
        return self.representation
