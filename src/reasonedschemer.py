
from muk.sexp import *
from muk.core import *
from muk.ext import *
from muk.ext import unify as _unify, unify_occur_check as _unify_occur_check

@adapt_iterables_to_conses(lambda u, v, occur_check: {u, v})
def unify(u, v, occur_check=False):
    return _unify(u, v, occur_check)

@adapt_iterables_to_conses(all_arguments)
def unify_occur_check(u, v):
    return _unify_occur_check(u, v)

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
                 else_clause=caro(l, x))

def reverse_list(l):
    return run(fresh(lambda y: memberrevo(y, l)))

@adapt_iterables_to_conses(lambda x, l, out: {l, out})
def memo(x, l, out):
    return fresh(lambda a, d: conj(unify([a] + d, l), 
                                   conde([unify(a, x), unify(l, out)], 
                                         else_clause=memo(x, d, out))))


@adapt_iterables_to_conses(lambda x, l, out: {l, out})
def rembero(x, l, out):
    return conde([nullo(l), nullo(out)],
                 [caro(l, x), cdro(l, out)],
                 else_clause=fresh(lambda a, d, res: unify([a] + d, l) & rembero(x, d, res) & unify([a] + res, out)))

@adapt_iterables_to_conses(lambda s, l: {l})
def surpriseo(s, l):
    return rembero(s, l, l) 

@adapt_iterables_to_conses(all_arguments)
def appendo(l, s, out):
    return conde([nullo(l), unify(s, out)],
                 else_clause=fresh(lambda a, d, res: unify([a] + d, l) & appendo(d, s, res) & unify([a] + res, out)))

@adapt_iterables_to_conses(all_arguments)
def appendso(l, s, out):
    return conde([nullo(l), unify(s, out)],
                 else_clause=fresh(lambda a, d, res: conj(unify([a] + d, l), 
                                                           unify([a] + res, out), 
                                                           appendso(d, s, res))))

@adapt_iterables_to_conses(all_arguments)
def swappendso(l, s, out):
    return conde([succeed, fresh(lambda a, d, res: conj(unify([a] + d, l), 
                                                        unify([a] + res, out), 
                                                        swappendso(d, s, res)))],
                 else_clause=nullo(l) & unify(s, out))

def bswappendso(bound):

    with delimiter(bound) as D:
        @adapt_iterables_to_conses(all_arguments)
        def R(l, s, out):
            return conde([succeed, fresh(lambda a, d, res: conj(unify([a] + d, l),
                                                                  unify([a] + res, out),
                                                                  R(d, s, res)))],
                           else_clause=nullo(l) & unify(s, out)) < D
    return R

@adapt_iterables_to_conses(lambda x, out: {x})
def unwrapo(x, out):
    return conde([fresh(lambda a, d: conj(unify([a] + d, x), unwrapo(a, out))), succeed],
                  else_clause=unify(x, out))

@adapt_iterables_to_conses(all_arguments)
def unwrapso(x, out):
    return conde([succeed, unify(x, out)],
                  else_clause=fresh(lambda a, d: conj(unify([a] + d, x), unwrapso(a, out))))

@adapt_iterables_to_conses(all_arguments)
def flatteno(s, out):
    def F(a, d, out_a, out_d):
        return conj(unify([a] + d, s), 
                    flatteno(a, out_a), 
                    flatteno(d, out_d), 
                    appendo(out_a, out_d, out))
    return conde([nullo(s), nullo(out)],
                 [fresh(F), succeed],
                 else_clause=unify([s], out))


@adapt_iterables_to_conses(all_arguments)
def flattenrevo(s, out):
    return conde([succeed, unify([s], out)],
                 [nullo(s), nullo(out)],
                 else_clause=fresh(lambda a, d, out_a, out_d: 
                                    unify([a] + d, s) & 
                                    flattenrevo(a, out_a) & 
                                    flattenrevo(d, out_d) & 
                                    appendo(out_a, out_d, out)))

def anyo(g):
    return conde([g, succeed],
                  else_clause=fresh(lambda: anyo(g))) # by η-inversion  

nevero = anyo(fail) # `nevero` ever succeeds because although the question of the first `conde` line within `anyo` fails,
                    # the answer of the second `conde` line, namely `anyo(fail)` is where we started.
alwayso = anyo(succeed) # `alwayso` always succeeds any number of times, whereas `succeed` can succeed only once

def succeed_at_least(g, times=1):
    return conde(*[[succeed, succeed] for _ in range(times)],
                 else_clause=g)

def bit_xoro(α, β, γ):
    return conde([unify(0, α) & unify(0, β), unify(0, γ)],
                 [unify(1, α) & unify(0, β), unify(1, γ)],
                 [unify(0, α) & unify(1, β), unify(1, γ)],
                 [unify(1, α) & unify(1, β), unify(0, γ)],)

def bit_ando(α, β, γ):
    return conde([unify(0, α) & unify(0, β), unify(0, γ)],
                 [unify(1, α) & unify(0, β), unify(0, γ)],
                 [unify(0, α) & unify(1, β), unify(0, γ)],
                 [unify(1, α) & unify(1, β), unify(1, γ)],)

def half_addero(α, β, γ, δ):
    return conj(bit_xoro(α, β, γ), bit_ando(α, β, δ))

def full_addero(ε, α, β, γ, δ):
    return fresh(lambda w, αβ, wε: conj(half_addero(α, β, w, αβ), 
                                        half_addero(ε, w, γ, wε), 
                                        bit_xoro(αβ, wε, δ)))

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def zeroo(n):
    return unify([], n)

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def oneo(n):
    return unify([1], n)

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def twoo(n):
    return unify([0, 1], n)

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def threeo(n):
    return unify([1, 1], n)

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def poso(n):
    return pairo(n)

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def greater_than_oneo(n):
    return fresh(lambda a, ad, dd: unify([a, ad] + dd, n))

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def rightmost_representative(n):
    raise NotImplemented

@adapt_iterables_to_conses(lambda δ, n, m, r: {n: num.build, m: num.build, r: num.build,})
def addero(δ, n, m, r):
    return condi([unify(0, δ) & zeroo(m), unify(n, r)],
                 [unify(0, δ) & poso(m) & zeroo(n), unify(m, r)],
                 [unify(1, δ) & zeroo(m), fresh(lambda: addero(0, n, [1], r))],
                 [unify(1, δ) & poso(m) & zeroo(n), fresh(lambda: addero(0, [1], m, r))],
                 [oneo(n) & oneo(m), fresh(lambda α, β: conj(full_addero(δ, 1, 1, α, β), unify([α, β], r)))],
                 [oneo(n), _addero(δ, [1], m, r)],
                 [greater_than_oneo(n) & oneo(m), _addero(δ, [1], n, r)], # we delete `greater_than_oneo(r)` respect to The Reasoned Schemer
                 [greater_than_oneo(n), _addero(δ, n, m, r)])


@adapt_iterables_to_conses(lambda δ, n, m, r: {n: num.build, m: num.build, r: num.build,})
def _addero(δ, n, m, r): # alias for `gen_adder` as it appears in The Reasoned Schemer
    return fresh(lambda α, β, γ, ε, x, y, z:
                    conj(unify((α, x), n),
                         unify((β, y), m), poso(y),
                         unify((γ, z), r), poso(z),
                         full_addero(δ, α, β, γ, ε) @ addero(ε, x, y, z)))

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def pluso(n, m, k):
    return addero(0, n, m, k)

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def minuso(n, m, k):
    return pluso(k, m, n)

def not_thingo(x, *, what):
    return conda([unify(what, x), fail],
                 else_clause=succeed)

def onceo(g):
    return condu([g, succeed])

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def bumpo(n, x):
    return conde([unify(n, x), succeed],
                 else_clause=fresh(lambda m: conj(minuso(n, [1], m), bumpo(m, x))))

def gentesto(op, *args):
    return onceo(fresh(lambda *lvars: conj(op(*lvars), *[unify(a, l) for a, l in zip(args, lvars)]), 
                       arity=len(args)))

def enumerateo(op, r, n):
    return fresh(lambda i, j, k: conj(bumpo(n, i),
                                      bumpo(n, j),
                                      op(i, j, k),
                                      gentesto(op, i, j, k),
                                      unify([i, j, k], r)))


@adapt_iterables_to_conses(lambda δ, n, m, r: {n: num.build, m: num.build, r: num.build,})
def _addereo(δ, n, m, r): # alias for `gen_adder` as it appears in The Reasoned Schemer
    return fresh(lambda α, β, γ, ε, x, y, z:
                    conj(unify((α, x), n),
                         unify((β, y), m), poso(y),
                         unify((γ, z), r), poso(z),
                         conj(full_addero(δ, α, β, γ, ε),  
                              addereo(ε, x, y, z))))

@adapt_iterables_to_conses(lambda δ, n, m, r: {n: num.build, m: num.build, r: num.build,})
def addereo(δ, n, m, r):
    return condi([unify(0, δ) & zeroo(m), unify(n, r)],
                 [unify(0, δ) & poso(m) & zeroo(n), unify(m, r)],
                 [unify(1, δ) & zeroo(m), fresh(lambda: addereo(0, n, [1], r))],
                 [unify(1, δ) & poso(m) & zeroo(n), fresh(lambda: addereo(0, [1], m, r))],
                 [oneo(n) & oneo(m), fresh(lambda α, β: full_addero(δ, 1, 1, α, β) & unify([α, β], r))],
                 [oneo(n), _addereo(δ, [1], m, r)],
                 [greater_than_oneo(n) & oneo(m), _addereo(δ, [1], n, r)], # we delete `greater_than_oneo(r)` respect to The Reasoned Schemer
                 [greater_than_oneo(n), _addereo(δ, n, m, r)])

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def pluseo(n, m, k):
    return addereo(0, n, m, k)


@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def multiplyo(n, m, p):
    return condi([zeroo(n), zeroo(p)],
                 [poso(n), zeroo(m) & zeroo(p)],
                 [oneo(n), poso(m) & unify(m, p)],
                 [poso(n), oneo(m) & unify(n, p)],
                 [fresh(lambda x, z: conj(unify((0, x), n), poso(x),
                                          unify((0, z), p), poso(z),
                                          greater_than_oneo(m),
                                          fresh(lambda: multiplyo(x, m, z)))), succeed],
                 [fresh(lambda x, y: conj(unify((1, x), n), poso(x),
                                          unify((0, y), m), poso(y),
                                          fresh(lambda: multiplyo(m, n, p)))), succeed],
                 [fresh(lambda x, y: conj(unify((1, x), n), poso(x),
                                          unify((1, y), m), poso(y),
                                          multiply_oddo(x, n, m, p))), succeed])

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def multiply_oddo(x, n, m, p):
    return fresh(lambda q: conj(multiply_boundo(q, p, n, m),
                                multiplyo(x, m, q),
                                pluso((0, q), m, p)))

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def multiply_boundo(q, p, n, m):
    return conde([nullo(q), pairo(p)],
                 else_clause=fresh(lambda x, y, z:
                                    cdro(q, x) & cdro(p, y) &
                                    condi([nullo(n), cdro(m, z) & fresh(lambda: multiply_boundo(x, y, z, []))],
                                          else_clause=cdro(n, z) & fresh(lambda: multiply_boundo(x, y, z, m)))))

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def length_equalo(n, m):
    return conde([zeroo(n), zeroo(m)],
                 [oneo(n), oneo(m)],
                 else_clause=fresh(lambda α, β, x, y:
                                        conj(unify((α, x), n) & poso(x),
                                             unify((β, y), m) & poso(y),
                                             fresh(lambda: length_equalo(x, y)))))  

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def length_lto(n, m):
    return conde([zeroo(n), poso(m)],
                 [oneo(n), greater_than_oneo(m)],
                 else_clause=fresh(lambda α, β, x, y:
                                        conj(unify((α, x), n), poso(x),
                                             unify((β, y), m), poso(y),
                                             fresh(lambda: length_lto(x, y)))))

def _length_leqo(n, m, condo):
    return condo([length_equalo(n, m), succeed],
                 [length_lto(n, m), succeed])

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def lengthe_leqo(n, m):
    return _length_leqo(n, m, conde)

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def lengthi_leqo(n, m):
    return _length_leqo(n, m, condi)

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def lto(n, m):
    return condi([length_lto(n, m), succeed],
                 [length_equalo(n, m), fresh(lambda x: conj(poso(x), pluso(n, x, m)))])

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def leq(n, m):
    return equalo(n, m) | lto(n, m)

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def divmodo(n, m, q, r):
    return condi([zeroo(q), unify(n, r) & lto(r, m)],
                 [oneo(q) & zeroo(r), equalo(n, m) & lto(r, m)], 
                 [lto(m, n) & lto(r, m), fresh(lambda mq: length_equalo(mq, n) & multiplyo(m, q, mq) & pluso(mq, r, n))])

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def divmod_proo(n, m, q, r):
    return condi([zeroo(q) & lto(n, m), unify(r, n)],
                 [oneo(q) & length_equalo(n, m), pluso(r, m, n) & lto(r, m)],
                 else_clause=conji(length_lto(m, n), lto(r, m), poso(q),
                                    fresh(lambda n_h, n_l, q_h, q_l, qlm, qlmr, rr, r_h:
                                            conji(splito(n, r, n_l, n_h),
                                                  splito(q, r, q_l, q_h),
                                                  conde([zeroo(n_h) & zeroo(q_h), minuso(n_l, r, qlm) & multiplyo(q_l, m, qlm)],
                                                        else_clause=conji(poso(n_h),
                                                                          multiplyo(q_l, m, qlm),
                                                                          pluso(qlm, r, qlmr),
                                                                          minuso(qlmr, n_l, rr),
                                                                          splito(rr, r, [], r_h),
                                                                          fresh(lambda: divmod_proo(n_h, m, q_h, r_h))))))))

def splito(n, r, l, h):
    return condi([zeroo(n), zeroo(l) & zeroo(h)],
                 [fresh(lambda β, n_hat: 
                            conj(unify((0, β, n_hat), n), 
                                 zeroo(r), 
                                 unify((β, n_hat), h), 
                                 zeroo(l))), succeed],
                 [fresh(lambda n_hat: 
                            conj(unify((1, n_hat), n), 
                                 zeroo(r), 
                                 unify(n_hat, h), 
                                 oneo(l))), succeed],
                 [fresh(lambda α, β, n_hat, r_hat: 
                            conj(unify((0, β, n_hat), n), 
                                 unify((α, r_hat), r),  
                                 zeroo(l), 
                                 fresh(lambda: splito((β, n_hat), r_hat, [], h)))), succeed],
                 [fresh(lambda α, n_hat, r_hat: 
                            conj(unify((1, n_hat), n), 
                                 unify((α, r_hat), r),  
                                 oneo(l), 
                                 fresh(lambda: splito(n_hat, r_hat, [], h)))), succeed],
                 [fresh(lambda α, β, n_hat, r_hat, l_hat: 
                            conj(unify((β, n_hat), n), 
                                 unify((α, r_hat), r), 
                                 unify((β, l_hat), l), 
                                 poso(l), 
                                 fresh(lambda: splito(n_hat, r_hat, l_hat, h)))), succeed],)


@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def logo(n, b, q, r):
    return condi([oneo(n) & poso(b), zeroo(q) & zeroo(r)],
                 [zeroo(q) & lto(n, b), pluso(r, [1], n)],
                 [oneo(q) & greater_than_oneo(b) & length_equalo(n, b), pluso(r, b, n)],
                 [oneo(b) & poso(q), pluso(r, [1], n)],
                 [zeroo(b) & poso(q), unify(r, n)],
                 [twoo(b), fresh(lambda a, ad, dd, s: conj(poso(dd),
                                                           unify((a, ad, dd), n),
                                                           expo(n, [], q, base=2),
                                                           splito(n, dd, r, s)))],
                 [fresh(lambda a, ad, add, ddd: conde([threeo(b), succeed],
                                                      else_clause=unify((a, ad, add, ddd), b))) & length_lto(b, n),
                  fresh(lambda bw1, bw, nw, nw1, ql1, q_l, s:
                            conj(expo(b, [], bw1, base=2),
                                 pluso(bw1, [1], bw),
                                 length_lto(q, n),
                                 fresh(lambda q_1, bwq1:
                                            conj(pluso(q, [1], q_1),
                                                 multiplyo(bw, q_1, bwq1),
                                                 lto(nw1, bwq1),
                                                 expo(n, [], nw1, base=2),
                                                 pluso(nw1, [1], nw),
                                                 divmodo(nw, bw, ql1, s),
                                                 pluso(q_l, [1], ql1))),
                                 conde([unify(q, q_l), succeed],
                                       else_clause=length_lto(q_l, q)),
                                 fresh(lambda bql, q_h, s, qdh, qd:
                                            conj(multiply_repeatedo(b, q_l, bql),
                                                 divmodo(nw, bw1, q_h, s),
                                                 pluso(q_l, qdh, q_h),
                                                 pluso(q_l, qd, q),
                                                 conde([unify(qd, qdh), succeed],
                                                       else_clause=lto(qd, qdh)),
                                                 fresh(lambda bqd, bq1, bq:
                                                            conj(multiply_repeatedo(b, qd, bqd),
                                                                 multiplyo(bql, bqd, bq),
                                                                 multiplyo(b, bq, bq1),
                                                                 pluso(bq, r, n),
                                                                 lto(n, bq1))))))), succeed])
                    
@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def expo(n, b, q, *, base):
    return condi([oneo(n), zeroo(q)],
                 [greater_than_oneo(n) & oneo(q), fresh(lambda s: splito(n, b, s, [1]))],
                 [fresh(lambda q_1, b_2:
                            conji(unify((0, q_1), q), poso(q_1),
                                  length_lto(b, n),
                                  appendo(b, (1, b), b_2),
                                  fresh(lambda: expo(n, b_2, q_1, base=base)))), succeed],
                 [fresh(lambda q_1, n_h, b_2, s:
                            conji(unify((1, q_1), q), poso(q_1),
                                  poso(n_h),  
                                  splito(n, b, s, n_h),
                                  appendo(b, (1, b), b_2),
                                  fresh(lambda: expo(n_h, b_2, q_1, base=base)))), succeed])

@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def multiply_repeatedo(n, q, nq):
    return conde([poso(n) & zeroo(q), oneo(nq)],
                 [oneo(q), unify(n, nq)],
                 [greater_than_oneo(q), fresh(lambda q_1, nq1:
                                                conj(pluso(q_1, [1], q),
                                                     fresh(lambda: multiply_repeatedo(n, q_1, nq1)),
                                                     multiplyo(nq1, n, nq)))])


@adapt_iterables_to_conses(all_arguments, ctor=num.build)
def powo(b, q, n):
    return logo(n, b, q, [])

