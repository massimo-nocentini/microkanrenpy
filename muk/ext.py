

from muk.core import *
from muk.core import _conj, _disj


def snooze(f, formal_vars):
    return fresh(lambda: f(*formal_vars))

def cond(*clauses, else_clause=[fail], interleaving):
    conjuctions = [conj(*clause) for clause in clauses] + [conj(*else_clause)]
    return disj(*conjuctions, interleaving=interleaving)

conde = partial(cond, interleaving=False)
condi = partial(cond, interleaving=True)

def disj(*goals, interleaving=True):
    g, *gs = goals
    if gs: return _disj(g, disj(*gs, interleaving=interleaving), interleaving)  
    else: return _disj(g, fail, interleaving)

def conj(*goals):
    g, *gs = goals
    return _conj(g, conj(*gs)) if gs else _conj(g, succeed)
