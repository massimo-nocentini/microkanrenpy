
import collections
from functools import wraps, partial, reduce
from contextlib import contextmanager
from itertools import chain

from muk.core import *
from muk.core import _conj, _disj, _unify
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

class _unify_pure(_unify):
    
    def __init__(self, u, v, occur_check):
        super(_unify_pure, self).__init__(u, v, partial(ext_s, occur_check=occur_check))

class _unify_occur_check(_unify_pure):

    def __init__(self, u, v):
        super(_unify_occur_check, self).__init__(u, v, occur_check=True)

    def __call__(self, s : state):
        try:
            yield from super(_unify_occur_check, self).__call__(s)
        except OccurCheck:
            yield from fail(s)

@adapt_iterables_to_conses(lambda u, v, occur_check: {u, v})
def unify(u, v, occur_check=False):
    return _unify_pure(u, v, occur_check)

@adapt_iterables_to_conses(all_arguments)
def unify_occur_check(u, v):
    return _unify_occur_check(u, v)

def cond(*clauses, else_clause=fail, λ_if):

    def λ(clause, otherwise):
        question, answer = clause
        return λ_if(question, answer, otherwise)
    
    return foldr(λ, clauses, initialize=else_clause)  

class if_pure(goal):

    def __init__(self, question, answer, otherwise, *, interleaving):
        self.question = question
        self.answer = answer
        self.otherwise = otherwise
        self.interleaving = interleaving
    
    def __call__(self, s : state):
        C = self.question & self.answer
        α, β = C(s), self.otherwise(s)
        yield from mplus(iter([α, β]), self.interleaving)

ife = partial(if_pure, interleaving=False)
ifi = partial(if_pure, interleaving=True)

class if_softcut(goal):

    def __init__(self, question, answer, otherwise, *, doer):
        self.question = question
        self.answer = answer
        self.otherwise = otherwise
        self.doer = doer

    def __call__(self, s : state):
        α = self.question(s) 
        try:
            r = next(α) # r : state
        except StopIteration: 
            β = self.otherwise(s) 
            yield from β
        else:
            γ = self.doer(r, α, self.answer)
            yield from γ

ifa = partial(if_softcut, doer=lambda r, α, answer: 
        bind(chain([r], α), answer, mplus=partial(mplus, interleaving=False)))
ifu = partial(if_softcut, doer=lambda r, α, answer: answer(r))

conde = partial(cond, λ_if=ife)
condi = partial(cond, λ_if=ifi)
conda = partial(cond, λ_if=ifa)
condu = partial(cond, λ_if=ifu)

equalo = unify


@contextmanager
def delimiter(d):

    key = object()

    class D: 
        def __gt__(self, g):
            return delimited(key, d, g)

    yield D()

class delimited(goal):
    
    def __init__(self, key, upper, g):
        self.key = key
        self.upper = upper
        self.g = g

    def __call__(self, s : state):
        v = s.sub.get(self.key, 0)
        if v < self.upper:
            s.sub[self.key] = v + 1
            α = self.g(s)
            yield from α
        else:
            yield from fail(s)

class project(goal):

    def __init__(self, *logic_vars, into):
        self.logic_vars = logic_vars
        self.into = into

    def __call__(self, s : state):
        walked_vars = [walk_star(v, s.sub) for v in self.logic_vars]
        g = self.into(*walked_vars)
        α = g(s) 
        yield from α


class sub(goal):

    def __init__(self, *logic_vars, of):
        self.logic_vars = logic_vars
        self.of = of

    def λ(self, s : state):  
        lvars = set(self.logic_vars) if self.logic_vars else s.sub.keys()
        return state({v:{v:s.sub[v]} for v in lvars if v in s.sub}, s.next_index)
        
    def __call__(self, s : state):
        α = self.of(s) 
        yield from map(self.λ, α)

def rel(r):
    def R(res):
        def recv(*args): 
            return conj(r(*args), unify(list(args), res))
        r_sig = signature(r)
        return fresh(recv, arity=len(r_sig.parameters))
    return R

def lvars(vars_names, splitter=' '):
    return [var(b, n.strip()) for b, n in enumerate(vars_names.split(splitter))]

