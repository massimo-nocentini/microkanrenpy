
import collections
from functools import wraps, partial, reduce
from contextlib import contextmanager

from muk.core import *
from muk.core import _conj, _disj, _unify_pure, _unify_occur_check
from muk.utils import *


def snooze(f, formal_vars):
    return fresh(lambda: f(*formal_vars))

def disj(*goals, interleaving=True):
    D = partial(_disj, interleaving=interleaving)
    return foldr(D, goals, initialize=fail)

def conj(*goals, interleaving=False):
    C = partial(_conj, interleaving=interleaving)
    return foldr(C, goals, initialize=succeed)

conji = partial(conj, interleaving=True)

@adapt_iterables_to_conses(lambda u, v, occur_check: {u, v})
def unify(u, v, occur_check=False):
    return _unify_pure(u, v, occur_check)

@adapt_iterables_to_conses(all_arguments)
def unify_occur_check(u, v):
    return _unify_occur_check(u, v)

def cond(*clauses, else_clause=[fail], λ_if):

    def λ(clause, otherwise):
        question, *answers = clause
        return λ_if(question, conj(*answers), otherwise)
    
    else_clause = [succeed] + else_clause # to stick to the pattern [question answer ...] of a cond-line
    r = foldr(λ, clauses, initialize=conj(*else_clause))  
    return r

conde = partial(cond, λ_if=ife)
condi = partial(cond, λ_if=ifi)
conda = partial(cond, λ_if=ifa)
condu = partial(cond, λ_if=ifu)

equalo = unify

def rel(r):
    def R(res):
        def recv(*args): 
            return conj(r(*args), unify(list(args), res))
        r_sig = signature(r)
        return fresh(recv, arity=len(r_sig.parameters))
    return R

def lvars(vars_names, splitter=' '):
    return [var(b, n.strip()) for b, n in enumerate(vars_names.split(splitter))]

