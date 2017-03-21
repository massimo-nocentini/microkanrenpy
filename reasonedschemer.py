
from sexp import *
from microkanren import *

def nullo(l):
    return unify([], l)

def conso(a, d, p):
    return unify(cons(a, d), p) 

def pairo(p):
    return fresh(lambda a, d: conso(a, d, p), arity=2)

def caro(p, a):
    return fresh(lambda d: conso(a, d, p))

def cdro(p, d):
    return fresh(lambda a: conso(a, d, p))

def listo(l):
    return conde(   [nullo(l), succeed],
                    #[pairo(l), fresh(lambda d: conj(cdro(l, d), snooze(listo, [d])))]
                    [pairo(l), fresh(lambda d: conj(cdro(l, d), listo(d)))])

