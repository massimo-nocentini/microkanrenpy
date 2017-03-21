
from sexp import *
from microkanren import *

@adapt_iterables_to_conses()
def nullo(l):
    return unify([], l)

@adapt_iterables_to_conses(lambda a, d, p: [d, p])
def conso(a, d, p):
    return unify(cons(a, d), p) 

@adapt_iterables_to_conses()
def pairo(p):
    return fresh(lambda a, d: conso(a, d, p))

@adapt_iterables_to_conses(lambda p, a: [p])
def caro(p, a):
    return fresh(lambda d: conso(a, d, p))

@adapt_iterables_to_conses()
def cdro(p, d):
    return fresh(lambda a: conso(a, d, p))

@adapt_iterables_to_conses()
def listo(l):
    return conde([nullo(l), succeed], 
                 [pairo(l), fresh(lambda d: conj(cdro(l, d), listo(d)))])

