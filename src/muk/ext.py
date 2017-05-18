
import collections
from functools import wraps, partial, reduce
from contextlib import contextmanager
from itertools import chain

from muk.core import *
from muk.core import _conj, _disj, _unify
from muk.utils import *


# DISJ, CONJ, CONJI {{{

def disj(*goals, interleaving=True, dovetail=False):
    if dovetail:
        def D(s : state):
            return mplus((α for g in goals for α in [g(s)]), interleaving=True)
        return D
    else:
        D = partial(_disj, interleaving=interleaving)
        return foldr(D, goals, initialize=fail)

def conj(*goals, interleaving=False):
    C = partial(_conj, interleaving=interleaving)
    return foldr(C, goals, initialize=succeed)

conji = partial(conj, interleaving=True)

# }}}

# UNIFY, UNIFY_OCCUR_CHECK {{{

class unify(_unify):
    
    def __init__(self, u, v, occur_check=False):
        super(unify, self).__init__(u, v, partial(ext_s, occur_check=occur_check))

class unify_occur_check(unify):

    def __init__(self, u, v):
        super(unify_occur_check, self).__init__(u, v, occur_check=True)

    def __call__(self, s : state):
        try:
            yield from super(unify_occur_check, self).__call__(s)
        except OccurCheck:
            yield from fail(s)

equalo = unify

# }}}

# COND {{{

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

 # }}}

# DELIMITED {{{

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

# }}}

# PROJECT, REL {{{

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

class rel(goal):

    def __init__(self, r, res, unify=unify):
        self.r = r
        self.res = res
        self.unify = unify

    def __call__(self, s : state):

        def recv(*args): 
            return self.r(*args) & self.unify(list(args), self.res)

        g = fresh(recv, arity=len(signature(self.r).parameters))
        α = g(s)
        yield from α

# }}}

def lvars(vars_names, splitter=' '):
    return [var(b, n.strip()) for b, n in enumerate(vars_names.split(splitter))]

def rectify(α_α, β):
    return unify(α_α, β-[])
