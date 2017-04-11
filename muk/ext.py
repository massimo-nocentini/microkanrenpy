
import collections
from functools import wraps, partial, reduce
from contextlib import contextmanager

from muk.core import *
from muk.core import _conj, _disj, _unify_pure, _unify_occur_check
from muk.utils import *


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

@adapt_iterables_to_conses(lambda u, v, occur_check: {u, v})
def unify(u, v, occur_check=False):
    return _unify_pure(u, v, occur_check)

@adapt_iterables_to_conses(all_arguments)
def unify_occur_check(u, v):
    return _unify_occur_check(u, v)

def cond(*clauses, else_clause=[fail], interleaving):
    C = partial(conj, interleaving=interleaving)
    conjuctions = [C(*clause) for clause in clauses] + [C(*else_clause)]
    return disj(*conjuctions, interleaving=interleaving)

conde = partial(cond, interleaving=False)
condi = partial(cond, interleaving=True)

def cond_if(*clauses, else_clause=[fail], interleaving, committed):

    C = partial(conj, interleaving=interleaving)
    I = partial(ifa, interleaving=interleaving, committed=committed)

    def λ(clause, otherwise):  
        question, *then = clause
        return I(question, C(*then), otherwise)
    
    r = foldr(λ, clauses, initialize=C(*else_clause))  
    return r

conda = partial(cond_if, interleaving=False, committed=False)
condu = partial(cond_if, interleaving=False, committed=True)

equalo = unify

conji = partial(conj, interleaving=True)

def rel(r):
    def R(res):
        def recv(*args): 
            return conj(r(*args), unify(list(args), res))
        r_sig = signature(r)
        return fresh(recv, arity=len(r_sig.parameters))
    return R

def lvars(vars_names, splitter=' '):
    return [var(b, n.strip()) for b, n in enumerate(vars_names.split(splitter))]

