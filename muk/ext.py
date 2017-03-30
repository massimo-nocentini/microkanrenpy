
import collections
from functools import wraps
from contextlib import contextmanager

from muk.core import *
from muk.core import _conj, _disj, _fresh, _delimited


def snooze(f, formal_vars):
    return fresh(lambda: f(*formal_vars))

def disj(*goals, interleaving=True):
    g, *gs = goals
    if gs: return _disj(g, disj(*gs, interleaving=interleaving), interleaving)  
    else: return _disj(g, fail, interleaving)

def conj(*goals):
    g, *gs = goals
    return _conj(g, conj(*gs)) if gs else _conj(g, succeed)

def cond(*clauses, else_clause=[fail], interleaving):
    conjuctions = [conj(*clause) for clause in clauses] + [conj(*else_clause)]
    return disj(*conjuctions, interleaving=interleaving)

conde = partial(cond, interleaving=False)
condi = partial(cond, interleaving=True)

equalo = unify

def fresh(f, assembler=conj):

    def A(subgoals):
        args = subgoals if isinstance(subgoals, tuple) else [subgoals]
        return assembler(*args)
        
    return _fresh(f, assembler=A)

@contextmanager
def delimited(d):
    pv = pvar()
    def D(g): 
        return _delimited(d, pv, g)
    yield D



