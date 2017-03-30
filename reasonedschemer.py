
from muk.sexp import *
from muk.core import *
from muk.ext import *

@adapt_iterables_to_conses(all_arguments)
def nullo(l):
    return unify([], l)

@adapt_iterables_to_conses(lambda a, d, p: {d, p})
def conso(a, d, p):
    return unify(cons(a, d), p) 

@adapt_iterables_to_conses(all_arguments)
def pairo(p):
    return fresh(lambda a, d: conso(a, d, p))

@adapt_iterables_to_conses(lambda p, a: {p})
def caro(p, a):
    return fresh(lambda d: conso(a, d, p))

@adapt_iterables_to_conses(all_arguments)
def cdro(p, d):
    return fresh(lambda a: conso(a, d, p))

@adapt_iterables_to_conses(all_arguments)
def listo(l):
    return conde([nullo(l), succeed], 
                 #[pairo(l), fresh(lambda d: conj(cdro(l, d), listo(d)))])
                 [pairo(l), fresh(lambda a, d: conj(unify([a] + d, l), listo(d)))])

@adapt_iterables_to_conses(all_arguments)
def lolo(l):
    return conde([nullo(l), succeed],
                 #[fresh(lambda a: conj(caro(l, a), listo(a))), fresh(lambda d: conj(cdro(l, d), lolo(d)))])
                 [fresh(lambda a, d: conj(unify([a] + d, l), listo(a), lolo(d))), succeed])

@adapt_iterables_to_conses(all_arguments)
def twinso(s):
    #return fresh(lambda a, d: conj(unify([a] + d, s), unify([a], d))) # → unify([a a], s) 
    return fresh(lambda x: unify([x, x], s))

@adapt_iterables_to_conses(all_arguments)
def loto(l):
    return conde([nullo(l), succeed],
                 #[fresh(lambda a: conj(caro(l, a), twinso(a))), fresh(lambda d: conj(cdro(l, d), loto(d)))])
                 [fresh(lambda a, d: conj(unify([a] + d, l), twinso(a), loto(d))), succeed])

@adapt_iterables_to_conses(lambda predo, l: {l})
def listofo(predo, l):
    return conde([nullo(l), succeed],
                 [fresh(lambda a, d: conj(unify([a] + d, l), predo(a), listofo(predo, d))), succeed])

@adapt_iterables_to_conses(lambda x, l: {l})
def membero(x, l):
    return conde([nullo(l), fail],
                 [caro(l, x), succeed],
                 [fresh(lambda d: conj(cdro(l, d), membero(x, d))), succeed])

@adapt_iterables_to_conses(lambda x, l: {l})
def pmembero(x, l):
    return conde([nullo(l), fail],
                 [unify([x], l), succeed], # [caro(l, x), cdro(l, [])], in other words
                 [fresh(lambda d: conj(unify([x] + d, l), pairo(d))), succeed], # [caro(l, x), fresh(lambda a, d: cdro(l, (a, d)))], in other words
                 [fresh(lambda d: conj(cdro(l, d), pmembero(x, d))), succeed])

@adapt_iterables_to_conses(lambda x, l: {l})
def pmemberso(x, l):
    return conde([nullo(l), fail],
                 [fresh(lambda d: conj(unify([x] + d, l), pairo(d))), succeed],
                 [unify([x], l), succeed],
                 [fresh(lambda d: conj(cdro(l, d), pmemberso(x, d))), succeed])

def first_value(l):
    return run(fresh(lambda y: membero(y, l)), n=1)

@adapt_iterables_to_conses(lambda x, l: {l})
def memberrevo(x, l):
    return conde([nullo(l), fail],
                 [fresh(lambda d: conj(cdro(l, d), memberrevo(x, d))), succeed],
                 else_clause=[caro(l, x)])

def reverse_list(l):
    return run(fresh(lambda y: memberrevo(y, l)))

@adapt_iterables_to_conses(lambda x, l, out: {l, out})
def memo(x, l, out):

    def M(a, d):
        return unify([a] + d, l), conde([unify(a, x), unify(l, out)], 
                                         else_clause=[memo(x, d, out)])

    return fresh(M)

@adapt_iterables_to_conses(lambda x, l, out: {l, out})
def rembero(x, l, out):

    def E(a, d, res): return unify([a] + d, l), rembero(x, d, res), unify([a] + res, out)
    return conde([nullo(l), nullo(out)],
                 #[unify([x] + out, l), succeed], # in order to write this one we should promote `cons` to a class and implement __add__ and __radd__
                 [caro(l, x), cdro(l, out)],
                 else_clause=[fresh(E)])

@adapt_iterables_to_conses(lambda s, l: {l})
def surpriseo(s, l):
    return rembero(s, l, l) 

@adapt_iterables_to_conses(all_arguments)
def appendo(l, s, out):
    def E(a, d, res): return unify([a] + d, l), appendo(d, s, res), unify([a] + res, out)
    return conde([nullo(l), unify(s, out)],
                 else_clause=[fresh(E)])

@adapt_iterables_to_conses(all_arguments)
def appendso(l, s, out):
    def E(a, d, res): return unify([a] + d, l), unify([a] + res, out), appendso(d, s, res)
    return conde([nullo(l), unify(s, out)],
                 else_clause=[fresh(E)])

@adapt_iterables_to_conses(all_arguments)
def swappendso(l, s, out):
    def E(a, d, res): return unify([a] + d, l), unify([a] + res, out), swappendso(d, s, res)
    return conde([succeed, fresh(E)],
                 else_clause=[nullo(l), unify(s, out)])

def bswappendso(bound):
    with delimited(bound) as D:
        @adapt_iterables_to_conses(all_arguments)
        def R(l, s, out):
            def E(a, d, res): return unify([a] + d, l), unify([a] + res, out), R(d, s, res)
            return D(conde([succeed, fresh(E)], else_clause=[nullo(l), unify(s, out)]))
        return R

@adapt_iterables_to_conses(lambda x, out: x)
def unwrapo(x, out):
    return conde([fresh(lambda a, d: conj(unify([a] + d, x), unwrapo(a, out))), succeed],
                  else_clause=[unify(x, out)])

@adapt_iterables_to_conses(all_arguments)
def unwrapso(x, out):
    return conde([succeed, unify(x, out)],
                  else_clause=[fresh(lambda a, d: conj(unify([a] + d, x), unwrapso(a, out)))])

@adapt_iterables_to_conses(all_arguments)
def flatteno(s, out):
    def F(a, d, out_a, out_d):
        return (unify([a] + d, s), 
                flatteno(a, out_a), 
                flatteno(d, out_d), 
                appendo(out_a, out_d, out))
    return conde([nullo(s), nullo(out)],
                 [fresh(F), succeed],
                 else_clause=[unify([s], out)])


@adapt_iterables_to_conses(all_arguments)
def flattenrevo(s, out):
    def F(a, d, out_a, out_d):
        return (unify([a] + d, s), 
                flattenrevo(a, out_a), 
                flattenrevo(d, out_d), 
                appendo(out_a, out_d, out))
    return conde([succeed, unify([s], out)],
                 [nullo(s), nullo(out)],
                 else_clause=[fresh(F)])



