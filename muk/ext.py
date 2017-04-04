
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


def rel(r):
    r_sig = signature(r)
    def recv(res, *args): return r(*args), unify(list(args), res) 
    λ = make_callable(arity=len(r_sig.parameters)) 
    λo = λ(recv)
    return fresh(λo)

def make_callable(arity):
    a_ord = ord('a')
    params = [chr(a_ord + i) for i in range(arity)]
    λ_code = 'lambda recv: lambda res, {args}: recv(res, {args})'.format(args=', '.join(params))  
    λ = eval(λ_code)
    return λ
    

