
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
def associateo(δ, β):
    return appendo(δ, [2]+δ, β)

def mcculloch_first_ruleo(α, β, *, machine):
    return fresh(lambda η: conj(unify([2]+η, α), unify(η, β)))

def mcculloch_second_ruleo(α, β, *, machine):
    return fresh(lambda η, δ: conj(unify([3]+η, α), associateo(δ, β), machine(η, δ)))

mcculloch = machine(rules=[ mcculloch_second_ruleo, mcculloch_first_ruleo, ])

@adapt_iterables_to_conses(all_arguments)
def mcculloch_lawo(α, γ, αγ):    
    return conj(appendo(α, γ, αγ), mcculloch(γ, αγ))








