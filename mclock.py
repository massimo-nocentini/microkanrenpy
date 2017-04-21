
from muk.sexp import *
from muk.core import *
from muk.ext import *

def machine(*, rules):
    @adapt_iterables_to_conses(all_arguments)
    def M(α, β):
        return condi(*[[r(α, β, machine=M), succeed] for r in rules])
    return M

@adapt_iterables_to_conses(all_arguments)
def nullo(l):
    return unify([], l)

@adapt_iterables_to_conses(all_arguments)
def appendo(r, s, out):
    
    def A(r, out):
        return conde([nullo(r), unify(s, out)],
                     else_clause=[fresh(lambda a, d, res:
                                            conj(unify([a]+d, r),
                                                 unify([a]+res, out),
                                                 fresh(lambda: A(d, res)),))])
    return A(r, out)

@adapt_iterables_to_conses(all_arguments)
def associateo(γ, γ2γ):
    return appendo(γ, [2]+γ, γ2γ)

def mcculloch_first_ruleo(α, β, *, machine):
    return fresh(lambda η: conj(unify([2]+η, α), unify(η, β)))

def mcculloch_second_ruleo(α, δ2δ, *, machine):
    return fresh(lambda η, δ: conj(unify([3]+η, α), associateo(δ, δ2δ), machine(η, δ)))

mccullocho = machine(rules=[ mcculloch_second_ruleo, mcculloch_first_ruleo, ])

@adapt_iterables_to_conses(all_arguments)
def mcculloch_lawo(α, γ, αγ):    
    return conj(appendo(α, γ, αγ), mccullocho(γ, αγ))

@adapt_iterables_to_conses(lambda α, l: {α})
def lengtho(α, l):

    def L(α, *, acc):
        return conde([nullo(α), unify(l, acc)],
                     else_clause=[fresh(lambda a, β: conj(unify([a]+β, α),  
                                                          fresh(lambda: L(β, acc=acc+1))))])

    return L(α, acc=0)

def leqo(a, b):
    return project(a, b, into=lambda a, b: unify(True, a <= b))



