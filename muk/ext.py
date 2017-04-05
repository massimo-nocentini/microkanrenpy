
import collections
from functools import wraps, partial
from contextlib import contextmanager

from muk.core import *
from muk.core import _conj, _disj, _fresh, _delimited


def snooze(f, formal_vars):
    return fresh(lambda: f(*formal_vars))

def disj(*goals, interleaving=True):
    g, *gs = goals
    if gs: return _disj(g, disj(*gs, interleaving=interleaving), interleaving)  
    else: return _disj(g, fail, interleaving)

def conj(*goals, interleaving=False):
    g, *gs = goals
    C = partial(_conj, interleaving=interleaving)
    return C(g, conj(*gs, interleaving=interleaving)) if gs else C(g, succeed)

def cond(*clauses, else_clause=[fail], interleaving):
    C = partial(conj, interleaving=interleaving)
    conjuctions = [C(*clause) for clause in clauses] + [C(*else_clause)]
    return disj(*conjuctions, interleaving=interleaving)

conde = partial(cond, interleaving=False)
condi = partial(cond, interleaving=True)

equalo = unify

def iterwrap(obj, classes=(tuple,)):
    return obj if isinstance(obj, classes) else [obj]

def fresh(f, assembler=conj, **kwds):

    def A(subgoals):
        return assembler(*iterwrap(subgoals))
        
    return _fresh(f, assembler=A, **kwds)

@contextmanager
def delimited(d):
    pv = pvar()
    def D(g): 
        return _delimited(d, pv, g)
    yield D


def rel(r):
    def R(res):
        def recv(*args): 
            gs = iterwrap(r(*args))
            return conj(*gs, unify(list(args), res))
        r_sig = signature(r)
        return fresh(recv, arity=len(r_sig.parameters))
    return R



