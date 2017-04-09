
import collections
from functools import wraps, partial
from contextlib import contextmanager

from muk.core import *
from muk.core import _conj, _disj, _delimited, _unify


def snooze(f, formal_vars):
    return fresh(lambda: f(*formal_vars))

def disj(*goals, interleaving=True):
    g, *gs = goals
    D = partial(_disj, interleaving=interleaving)
    return D(g, disj(*gs, interleaving=interleaving)) if gs else D(g, fail)

def conj(*goals, interleaving=False):
    g, *gs = goals
    C = partial(_conj, interleaving=interleaving)
    return C(g, conj(*gs, interleaving=interleaving)) if gs else C(g, succeed)

@adapt_iterables_to_conses(all_arguments)
def unify(u, v):
    return _unify(u, v)

def cond(*clauses, else_clause=[fail], interleaving):
    C = partial(conj, interleaving=interleaving)
    conjuctions = [C(*clause) for clause in clauses] + [C(*else_clause)]
    return disj(*conjuctions, interleaving=interleaving)

conde = partial(cond, interleaving=False)
condi = partial(cond, interleaving=True)

equalo = unify

conji = partial(conj, interleaving=True)

def iterwrap(obj, classes=(tuple,)):
    return obj if isinstance(obj, classes) else [obj]

@contextmanager
def delimited(d):
    pv = pvar()
    def D(g): 
        return _delimited(d, pv, g)
    yield D


def rel(r):
    def R(res):
        def recv(*args): 
            return conj(r(*args), unify(list(args), res))
        r_sig = signature(r)
        return fresh(recv, arity=len(r_sig.parameters))
    return R



