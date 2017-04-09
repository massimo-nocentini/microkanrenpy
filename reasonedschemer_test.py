
import unittest

from muk.core import *
from muk.ext import *
from muk.sexp import *
from reasonedschemer import *
from reasonedschemer import _addero

def tea_cupo(x):
    return conde([unify('tea', x), succeed],
                 [unify('cup', x), succeed])

class reasonedschemer_test(unittest.TestCase):

    def setUp(self):
        self.maxDiff = None

    def test_succeed_fail(self):
        self.assertEqual(run(succeed), [Tautology()]) # 1.6
        self.assertEqual(run(fail), []) # 1.10
        self.assertEqual(run(fresh(lambda q: unify(True, q))), [True]) # 1.11
        self.assertEqual(run(fresh(lambda q: conj(fail, unify(True, q)))), []) # 1.12
        self.assertEqual(run(fresh(lambda q: conj(succeed, unify(True, q)))), [True]) # 1.13
        self.assertEqual(run(fresh(lambda q: conj(succeed, unify('corn', q)))), ['corn']) # 1.15
        self.assertEqual(run(fresh(lambda q: conj(fail, unify('corn', q)))), []) # 1.17
        self.assertEqual(run(fresh(lambda q: conj(succeed, unify(False, q)))), [False]) # 1.18
        self.assertEqual(run(unify(False, False)), [Tautology()])
        self.assertEqual(run(fresh(lambda q: unify(True, False))), [])
        self.assertEqual(run(unify(True, False)), [])
        self.assertEqual(run(fresh(lambda q, x: conj(unify(False, x), unify(True, q))),
                             var_selector=lambda q, x: q), [True]) # 1.23
        self.assertEqual(run(fresh(lambda q, x: conj(unify(False, x), unify(True, q))),
                             var_selector=lambda q, x: x), [False]) # 1.23.1
        self.assertEqual(run(fresh(lambda x, q: conj(unify(False, x), unify(True, q)))), [False]) # 1.23.2
        self.assertEqual(run(fresh(lambda q, x: conj(unify(False, x), unify(q, True)))), [True]) # 1.26
        self.assertEqual(run(fresh(lambda q: succeed)), [var(0)]) # 1.28
        self.assertEqual(run(fresh(lambda q: unify(False, False))), [var(0)]) # 1.28.1

        def goal(x): 
            let = lambda x: fresh(lambda x: unify(True, x))
            return let(False)
        self.assertEqual(run(fresh(goal)), [var(0)]) # 1.29

        self.assertEqual(run(fresh(lambda r, x, y: unify([x, y], r))), [[var(0), var(1)]]) # 1.30
        self.assertEqual(run(fresh(lambda s, t, u: unify([t, u], s))), [[var(0), var(1)]]) # 1.31

        def goal(r, x):
            let = lambda y: fresh(lambda x: unify([y, x, y], r))
            return let(x)
        self.assertEqual(run(fresh(goal)), [[var(2), var(1), var(2)]]) # 1.32
        
        def goal(r, x):
            let = lambda y: fresh(lambda x: unify([x, y, x], r))
            return let(x)
        self.assertEqual(run(fresh(goal)), [[var(2), var(1), var(2)]]) # 1.33

        self.assertEqual(run(fresh(lambda q: conj(unify(False, q), unify(True, q)))), []) # 1.34
        self.assertEqual(run(fresh(lambda q: conj(unify(False, q), unify(False, q)))), [False]) # 1.35

        def goal(q):
            let = lambda x: unify(True, x)
            return let(q)
        self.assertEqual(run(fresh(goal)), [True]) # 1.36

        self.assertEqual(run(fresh(unify)), [var(0)]) # 1.37
        self.assertEqual(run(fresh(lambda q, x: conj(unify(True, x), unify(x, q)))), [True]) # 1.38
        self.assertEqual(run(fresh(lambda q, x: conj(unify(q, x), unify(True, q)))), [True]) # 1.39

        self.assertEqual(run(fresh(lambda q, x: unify(x is q, q))), [False]) # 1.40.1
        def goal(q):
            let = lambda x: fresh(lambda q: unify(x is q, x))
            return let(q)
        self.assertEqual(run(fresh(goal)), [False]) # 1.40.2

        self.assertEqual(run(fresh(lambda r, y, x: unify([x, y], r))), [[var(0), var(1)]]) # 2.2

        def let(x, y):
            return [x, y]
        self.assertEqual(run(fresh(lambda r, v, w: unify(let(v, w), r))), [[var(0), var(1)]]) # 2.3


    def test_conde(self):
        self.assertEqual(run(conde([fail, succeed])), []) # 1.44
        self.assertEqual(run(conde([fail, fail], else_clause=[succeed])), [Tautology()]) # 1.45
        self.assertEqual(run(conde([fail], [succeed], else_clause=[succeed])), [Tautology(), Tautology()]) # 1.45
        self.assertEqual(run(conde([succeed, succeed])), [Tautology()]) # 1.46
        self.assertEqual(run(fresh(lambda x: conde([unify('olive', x), succeed], 
                                                   [unify('oil', x), succeed]))), 
                         ['olive', 'oil']) # 1.47
        self.assertEqual(run(fresh(lambda x: conde([unify('olive', x), succeed], 
                                                   [unify('oil', x), succeed])), n=1), 
                         ['olive']) # 1.49
        self.assertEqual(run(fresh(lambda x: conde([unify('virgin', x), fail], 
                                                   [unify('olive', x), succeed], 
                                                   [succeed, succeed], 
                                                   [unify('oil', x), succeed]))), 
                         ['olive', var(0), 'oil']) # 1.50
        self.assertEqual(run(fresh(lambda x: conde([unify('extra', x), succeed], 
                                                   [unify('virgin', x), fail], 
                                                   [unify('olive', x), succeed], 
                                                   [unify('oil', x), succeed])), n=2), 
                         ['extra', 'olive'])
        self.assertEqual(run(fresh(lambda r, x, y: conj(unify('split', x), 
                                                        unify('pea', y), 
                                                        unify([x, y], r)))),
                         [['split', 'pea']]) # 1.53
        self.assertEqual(run(fresh(
            lambda r, x, y: conj(conde([unify('split', x), unify('pea', y)],
                                       [unify('navy', x), unify('bean', y)]),
                                 unify([x, y], r)))),
            [['split', 'pea'], ['navy', 'bean']]) # 1.54
        self.assertEqual(run(fresh(
            lambda r, x, y: conj(conde([unify('split', x), unify('pea', y)],
                                       [unify('navy', x), unify('bean', y)]),
                                 unify([x, y, 'soup'], r)))),
            [['split', 'pea', 'soup'], ['navy', 'bean', 'soup']]) # 1.55

        self.assertEqual(run(fresh(tea_cupo)), ['tea', 'cup']) # 1.56
        self.assertEqual(run(fresh(lambda r, x, y: conj(conde([tea_cupo(x), unify(True, y)],
                                                              [unify(False, x), unify('y', y)]),
                                                        unify([x, y], r)))), 
                         [['tea', True], ['cup', True], [False, 'y']]) # 1.57
        self.assertEqual(run(fresh(lambda r, x, y: conj(condi([tea_cupo(x), unify(True, y)],
                                                              [unify(False, x), unify('y', y)]),
                                                        unify([x, y], r)))), 
                         [['tea', True], [False, 'y'], ['cup', True] ]) # 1.57
        self.assertEqual(run(fresh(lambda r, x, y, z: 
            conj(conde([unify(y, x), fresh(lambda x: unify(z, x))],
                       [fresh(lambda x: unify(y, x)), unify(z, x)]),
                 unify([y, z], r)))), [[var(0), var(1)], [var(0), var(1)]]) # 1.58
        self.assertEqual(run(fresh(lambda r, x, y, z: 
            conj(conde([unify(y, x), fresh(lambda x: unify(z, x))],
                       [fresh(lambda x: unify(y, x)), unify(z, x)]),
                 unify(False, x),
                 unify([y, z], r)))), [[False, var(0)], [var(0), False]]) # 1.59

        def goal(q):
            select = lambda a, b: b
            return select(unify(True, q), unify(False, q))
        self.assertEqual(run(fresh(goal)), [False]) # 1.60

        def goal(q):
            select = lambda a, b, c: b
            return select(unify(True, q), 
                          fresh(lambda x: conj(unify(x, q), unify(False, x))),
                          conde([unify(True, q), succeed], else_clause=[unify(False, q)]))
        self.assertEqual(run(fresh(goal)), [False]) # 1.61


    def test_caro(self):
        self.assertEqual(run(fresh(lambda a: caro(list('acorn'), a))), ['a']) # 2.6
        self.assertEqual(run(fresh(lambda a: caro(cons(a, list('corn')), 'a'))), ['a'])
        self.assertEqual(run(fresh(lambda p: caro(p, 'a'))), [('a', var(0))])
        self.assertEqual(run(fresh(lambda q: conj(caro(list('acorn'), 'a'), unify('q', q)))), ['q']) # 2.7
        self.assertEqual(run(fresh(lambda r, x, y: conj(caro([r, y], x), unify('pear', x)))), ['pear']) # 2.8
        self.assertEqual(run(fresh(lambda r, x, y: conj(caro(['grape', 'raisin', 'pear'], x), 
                                                        caro([['a'], ['b'], ['b']], y),
                                                        unify(cons(x, y), r)))), [['grape', 'a']]) # 2.11
        self.assertEqual(run(fresh(lambda r, x, y: conj(caro(['grape', 'raisin', 'pear'], x), 
                                                        caro([['a'], ['b'], ['b']], y),
                                                        unify((x, y), r)))), [['grape', 'a']]) # 2.11.1, remember: (x, y) means cons(x, y)
        self.assertEqual(run(fresh(lambda r, x, y: conj(caro(['grape', 'raisin', 'pear'], x), 
                                                        caro([['a'], ['b'], ['b']], y),
                                                        unify([x] + y, r)))), [['grape', 'a']]) # 2.11.2, remember: [x ...] + y means cons(x, cons(...cons(x, y)...))


    def test_cdro(self):
        self.assertEqual(run(fresh(lambda r, v: conj(cdro(list('acorn'), v), caro(v, r)))), ['c']) # 2.15
        self.assertEqual(run(fresh(lambda r, x, y: conj(cdro(['grape', 'raisin', 'pear'], x), 
                                                        caro([['a'], ['b'], ['b']], y),
                                                        unify([x] + y, r)))), [[['raisin', 'pear'], 'a']]) # 2.18
        self.assertEqual(run(fresh(lambda q: conj(cdro(list('acorn'), list('corn')), unify('q', q)))), ['q']) # 2.19
        self.assertEqual(run(fresh(lambda x: cdro(list('corn'), [x] + list('rn')))), ['o']) # 2.20
        self.assertEqual(run(fresh(lambda l, x: conj(cdro(l, list('corn')), 
                                                     caro(l, x), 
                                                     unify('a', x))), 
                             post=lambda l: ''.join(cons_to_list(l))), ['acorn']) # 2.21
        self.assertEqual(run(fresh(lambda l, x: conj(cdro(l, list('corn')), 
                                                     caro(l, x), 
                                                     unify('a', x)))), [list('acorn')]) # 2.21.1

    def test_conso(self):
        self.assertEqual(run(fresh(lambda p: conso(3, p, cons(3, cons(2, []))))), [[2]])
        self.assertEqual(run(fresh(lambda p: conso(3, p, [3,2,1]))), [[2, 1]])

        self.assertEqual(run(fresh(lambda l: conso(list('abc'), list('de'), l))), [[list('abc')]+list('de')]) # 2.22
        self.assertEqual(run(fresh(lambda l: unify([list('abc')] + list('de'), l))), [[list('abc')]+list('de')]) # 2.22.1

        self.assertEqual(run(fresh(lambda x: conso(x, list('abc'), list('dabc')))), ['d']) # 2.23
        self.assertEqual(run(fresh(lambda x: unify([x] + list('abc'), list('dabc')))), ['d']) # 2.23.1

        self.assertEqual(run(fresh(lambda r, x, y, z: conj(unify(list('ead') + [x], r), 
                                                           unify([y, 'a', z, 'c'], r)))), [list('eadc')]) # 2.24

        self.assertEqual(run(fresh(lambda x: conso(x, ['a', x, 'c'], ['d', 'a', x, 'c']))), ['d']) # 2.25
        self.assertEqual(run(fresh(lambda x: unify([x, 'a', x, 'c'], ['d', 'a', x, 'c']))), ['d']) # 2.25.1

        self.assertEqual(run(fresh(lambda l, x: conj(unify(['d', 'a', x, 'c'], l), 
                                                     unify([x, 'a', x, 'c'], l)))), [list('dadc')]) # 2.26
        self.assertEqual(run(fresh(lambda l, x: conj(unify([x, 'a', x, 'c'], l), 
                                                     unify(['d', 'a', x, 'c'], l)))), [list('dadc')]) # 2.27
        self.assertEqual(run(fresh(lambda l, d, x, y, w, s:
            conj(conso(w, list('ans'), s),
                 conso(x, s, l),
                 unify('b', x),
                 cdro(l, d),
                 caro(d, y),
                 unify('e', y)))), [list('beans')]) # 2.29
        self.assertEqual(run(fresh(lambda l, d, x, y, w, s, r:
            conj(unify([w] + list('ans'), s),
                 unify([x] + s, l),
                 unify('b', x),
                 # conj(cdro(l, d), caro(d, y)) → fresh(lambda t, r: conj(unify([t] + d, l), unify([y] + r, d)))
                 # so, the goal `unify([t] + d, l)` is already present before, therefore use `s` for `d`
                 unify([y] + r, s), 
                 unify('e', y)))), [list('beans')]) # 2.29.1

    def test_nullo(self):
        self.assertEqual(run(nullo([])), [Tautology()]) 
        self.assertEqual(run(nullo([1, 2])), []) 
        self.assertEqual(run(fresh(lambda x: nullo([]))), [var(0)]) 
        self.assertEqual(run(fresh(lambda q: conj(nullo(['grape', 'raisin', 'pear']), unify(True, q)))), []) # 2.32
        self.assertEqual(run(fresh(lambda q: conj(nullo([]), unify('q', q)))), ['q']) # 2.33
        self.assertEqual(run(fresh(lambda x: nullo(x))), [[]]) # 2.34

    def test_equalo(self):
        self.assertEqual(run(fresh(lambda q: conj(equalo('pear', 'plum'), unify(True, q)))), []) # 2.38
        self.assertEqual(run(fresh(lambda q: conj(equalo('plum', 'plum'), unify('q', q)))), ['q']) # 2.39
        self.assertEqual(run(equalo('plum', 'plum')), [Tautology()]) # 2.39.1

    def test_pairo(self):
        self.assertEqual(run(fresh(lambda r, x, y: unify([x, y, 'salad'], r))), [[var(0), var(1), 'salad']]) # 2.53
        self.assertEqual(run(fresh(lambda q: conj(pairo(cons(q, q)), unify('q', q)))), ['q']) # 2.54 
        self.assertEqual(run(fresh(lambda q: conj(pairo((q, q)), unify('q', q)))), ['q']) # 2.54.1
        self.assertEqual(run(fresh(lambda q: conj(pairo([q, q]), unify('q', q)))), ['q']) # 2.54.2 
        self.assertEqual(run(fresh(lambda q: conj(pairo([]), unify('q', q)))), []) # 2.55
        self.assertEqual(run(fresh(lambda q: conj(pairo('pair'), unify('q', q)))), []) # 2.56
        self.assertEqual(run(fresh(lambda x: pairo(x))), [(var(0), var(1))]) # 2.57
        self.assertEqual(run(fresh(lambda r: pairo(cons(r, 'pear')))), [var(0)]) # 2.58
        self.assertEqual(run(fresh(lambda r: pairo((r, 'pear')))), [var(0)]) # 2.58.1

    def test_listo(self):
        self.assertEqual(run(fresh(lambda x: listo(['a', 'b', x, 'd']))), [var(0)]) # 3.7
        self.assertEqual(run(fresh(lambda x: listo(list('abc') + x)), n=1), [[]]) # 3.10
        with self.assertRaises(RecursionError):
            run(fresh(lambda x: listo(list('abc') + x))) # 3.13
        self.assertEqual(run(fresh(lambda l: listo(list('abc') + l)), n=5), 
            [[], 
             [var(0)], 
             [var(0), var(1)],
             [var(0), var(1), var(2)],
             [var(0), var(1), var(2), var(3)]]) # 3.14
        self.assertEqual(run(fresh(lambda l: listo(l)), n=5), 
            [[], 
             [var(0)], 
             [var(0), var(1)],
             [var(0), var(1), var(2)],
             [var(0), var(1), var(2), var(3)]]) # 3.14.1

        self.assertEqual(run(listo((1,2,3,4))), []) # because the list isn't proper
        self.assertEqual(
            run(fresh(lambda w, x: conj(unify((1,2,3,4,x), w), listo(x))), n=3), 
            [[1,2,3,4], [1,2,3,4,var(0)], [1,2,3,4, var(0), var(1)]])
        self.assertEqual(
            run(fresh(lambda w, x: conj(unify([1,2,3,4] + x, w), listo(w))), n=3), 
            [[1,2,3,4], [1,2,3,4,var(0)], [1,2,3,4, var(0), var(1)]])

    def test_lolo(self):
        self.assertEqual(run(fresh(lambda l: lolo(l)), n=1), [[]]) # 3.20
        self.assertEqual(run(fresh(lambda q, x, y: 
            conj(lolo([['a', 'b'], [x, 'c'], ['d', y]]), unify(True, q)))), [True]) # 3.21
        self.assertEqual(run(fresh(lambda q, x: conj(lolo([['a', 'b']] + x), unify(True, q))), n=1), [True]) # 3.22
        self.assertEqual(run(fresh(lambda x: lolo([list('ab'), list('cd')] + x)), n=1), [[]]) # 3.23
        self.assertEqual(run(fresh(lambda x: lolo([list('ab'), list('cd')] + x)), n=5), 
                         [[], [[]], [[], []], [[], [], []], [[], [], [], []]]) # 3.24

    def test_twinso(self):
        self.assertEqual(run(fresh(lambda q: conj(twinso(['tofu', 'tofu']), unify(True, q)))), [True]) # 3.32
        self.assertEqual(run(fresh(lambda z: twinso([z, 'tofu']))), ['tofu']) # 3.33

    def test_loto(self):
        self.assertEqual(run(fresh(lambda z: loto([['g', 'g']] + z)), n=1), [[]]) # 3.38
        self.assertEqual(run(fresh(loto), n=5), 
                         [[], 
                          [[var(1), var(1)]], 
                          [[var(1), var(1)], [var(3), var(3)]], 
                          [[var(1), var(1)], [var(3), var(3)], [var(5), var(5)]], 
                          [[var(1), var(1)], [var(3), var(3)], [var(5), var(5)], [var(7), var(7)]]]) # 3.42
        self.assertEqual(run(fresh(lambda r, g, e, w, x, y, z:
            conj(loto([[g, g], [e, w], [x, y]] + z), 
                 unify([w, [x, y], z], r), 
                 unify(e, 'e'), 
                 unify(g, 'g'))), n=5),
            [['e', [var(1), var(1)], []],
             ['e', [var(1), var(1)], [[var(3), var(3)]]],
             ['e', [var(1), var(1)], [[var(3), var(3)], [var(5), var(5)]]],
             ['e', [var(1), var(1)], [[var(3), var(3)], [var(5), var(5)], [var(7), var(7)]]],
             ['e', [var(1), var(1)], [[var(3), var(3)], [var(5), var(5)], [var(7), var(7)], [var(9), var(9)]]]]) # 3.45
        self.assertEqual(run(fresh(lambda r, g, e, w, x, y, z:
            conj(unify([[g, g], [e, w], [x, y]] + z, r), 
                 loto(r), 
                 unify(e, 'e'), 
                 unify(g, 'g'))), n=3),
            [[['g', 'g'], ['e', 'e'], [var(1), var(1)]],
             [['g', 'g'], ['e', 'e'], [var(1), var(1)], [var(3), var(3)]],
             [['g', 'g'], ['e', 'e'], [var(1), var(1)], [var(3), var(3)], [var(5), var(5)]]]) # 3.47
        self.assertEqual(run(fresh(lambda r, g, e, w, x, y, z:
            conj(unify([[g, g], [e, w], [x, y]] + z, r), 
                 listofo(twinso, r),
                 unify(e, 'e'), 
                 unify(g, 'g'))), n=3),
            [[['g', 'g'], ['e', 'e'], [var(1), var(1)]],
             [['g', 'g'], ['e', 'e'], [var(1), var(1)], [var(3), var(3)]],
             [['g', 'g'], ['e', 'e'], [var(1), var(1)], [var(3), var(3)], [var(5), var(5)]]]) # 3.48

    def test_membero(self):
        self.assertEqual(run(fresh(lambda q: conj(membero('olive', ['virgin', 'olive', 'oil']), unify(True, q)))), [True]) # 3.57
        self.assertEqual(run(fresh(lambda y: membero(y, ['hummus', 'with', 'pita'])), n=1), ['hummus']) # 3.58
        self.assertEqual(run(fresh(lambda y: membero(y, ['hummus', 'with', 'pita'])), n=2), ['hummus', 'with']) # 3.59
        self.assertEqual(run(fresh(lambda y: membero(y, ['hummus', 'with', 'pita'])), n=3), ['hummus', 'with', 'pita']) # 3.60
        self.assertEqual(run(fresh(lambda y: membero(y, []))), []) # 3.61
        self.assertEqual(run(fresh(lambda y: membero(y, ['hummus', 'with', 'pita']))), ['hummus', 'with', 'pita']) # 3.62
        self.assertEqual(run(fresh(lambda x: membero('e', ['pasta', x, 'fagioli']))), ['e']) # 3.66 
        self.assertEqual(run(fresh(lambda x: membero('e', ['pasta', 'e', x, 'fagioli'])), n=1), [var(0)]) # 3.69
        self.assertEqual(run(fresh(lambda x: membero('e', ['pasta', x, 'e', 'fagioli'])), n=1), ['e']) # 3.70
        self.assertEqual(run(fresh(lambda r, x, y: conj(membero('e', ['pasta', x, 'fagioli', y]), unify([x, y], r)))), 
                         [['e', var(0)], [var(0), 'e']]) # 3.71
        self.assertEqual(run(fresh(lambda l: membero('tofu', l)), n=1), [('tofu', var(0))]) # 3.73
        with self.assertRaises(RecursionError):
            run(fresh(lambda l: membero('tofu', l))) # 3.75
        self.assertEqual(run(fresh(lambda l: membero('tofu', l)), n=5), 
                         [('tofu', var(0)),
                          (var(0), 'tofu', var(1)),
                          (var(0), var(1), 'tofu', var(2)),
                          (var(0), var(1), var(2), 'tofu', var(3)),
                          (var(0), var(1), var(2), var(3), 'tofu', var(4))]) # 3.76
        self.assertEqual(run(fresh(lambda q: conj(pmembero('tofu', ['a', 'b', 'tofu', 'd', 'tofu']), unify(True, q)))), 
                         [True, True]) # 3.81
        self.assertEqual(run(fresh(lambda l: pmembero('tofu', l)), n=12), 
                         [['tofu'],
                          ('tofu', var(0), var(1)),
                          [var(0), 'tofu'],
                          (var(0), 'tofu', var(1), var(2)),
                          [var(0), var(1), 'tofu'],
                          (var(0), var(1), 'tofu', var(2), var(3)),
                          [var(0), var(1), var(2), 'tofu'],
                          (var(0), var(1), var(2), 'tofu', var(3), var(4)),
                          [var(0), var(1), var(2), var(3), 'tofu'],
                          (var(0), var(1), var(2), var(3), 'tofu', var(4), var(5)),
                          [var(0), var(1), var(2), var(3), var(4), 'tofu'],
                          (var(0), var(1), var(2), var(3), var(4), 'tofu', var(5), var(6))]) # formely 3.80, actually 3.89
        self.assertEqual(run(fresh(lambda l: pmemberso('tofu', l)), n=12), 
                         [('tofu', var(0), var(1)),
                          ['tofu'],
                          (var(0), 'tofu', var(1), var(2)),
                          [var(0), 'tofu'],
                          (var(0), var(1), 'tofu', var(2), var(3)),
                          [var(0), var(1), 'tofu'],
                          (var(0), var(1), var(2), 'tofu', var(3), var(4)),
                          [var(0), var(1), var(2), 'tofu'],
                          (var(0), var(1), var(2), var(3), 'tofu', var(4), var(5)),
                          [var(0), var(1), var(2), var(3), 'tofu'],
                          (var(0), var(1), var(2), var(3), var(4), 'tofu', var(5), var(6)),
                          [var(0), var(1), var(2), var(3), var(4), 'tofu']]) # 3.94

        self.assertEqual(first_value('hello'), []) # 3.95.1
        self.assertEqual(first_value([]), []) # 3.95.2
        self.assertEqual(first_value(['pasta', 'e', 'fagioli']), ['pasta']) # 3.95.2

    def test_memberrevo(self):
        self.assertEqual(run(fresh(lambda x: memberrevo(x, ['pasta', 'e', 'fagioli']))), ['fagioli', 'e', 'pasta']) # 3.100
        self.assertEqual(list(reversed(['pasta', 'e', 'fagioli'])), reverse_list(['pasta', 'e', 'fagioli'])) # 3.101

    def test_memo(self):

        def question_4_10(out): return fresh(lambda x: memo('tofu', ['a', 'b', 'tofu', 'd', 'tofu', 'e'], out))
        self.assertEqual(run(fresh(question_4_10), n=1), [['tofu', 'd', 'tofu', 'e']])
        
        def question_4_11(out): return fresh(lambda x: memo('tofu', ['a', 'b', x, 'd', 'tofu', 'e'], out))
        self.assertEqual(run(fresh(question_4_11), n=1), [['tofu', 'd', 'tofu', 'e']])

        def question_4_12(r): return memo(r, ['a', 'b', 'tofu', 'd', 'tofu', 'e'], ['tofu', 'd', 'tofu', 'e'])
        self.assertEqual(run(fresh(question_4_12)), ['tofu'])

        def question_4_13(q): return conj(memo('tofu', ['tofu', 'e'], ['tofu', 'e']), unify(True, q))
        self.assertEqual(run(fresh(question_4_13)), [True])

        def question_4_14(q): return conj(memo('tofu', ['tofu', 'e'], ['tofu']), unify(True, q))
        self.assertEqual(run(fresh(question_4_14)), [])

        def question_4_15(x): return memo('tofu', ['tofu', 'e'], [x, 'e'])
        self.assertEqual(run(fresh(question_4_15)), ['tofu'])

        def question_4_16(x): return memo('tofu', ['tofu', 'e'], ['peas', x])
        self.assertEqual(run(fresh(question_4_16)), [])

        def question_4_17(out): return fresh(lambda x: memo('tofu', ['a', 'b', x, 'd', 'tofu', 'e'], out))
        self.assertEqual(run(fresh(question_4_17)), [['tofu', 'd', 'tofu', 'e'], ['tofu', 'e']])

        def question_4_18(z): return fresh(lambda u: memo('tofu', ['a', 'b', 'tofu', 'd', 'tofu', 'e'] + z, u))
        self.assertEqual(run(fresh(question_4_18), n=12), 
                         [var(0), 
                          var(0),
                          ('tofu', var(0)),
                          (var(0), 'tofu', var(1)),
                          (var(0), var(1), 'tofu', var(2)),
                          (var(0), var(1), var(2), 'tofu', var(3)),
                          (var(0), var(1), var(2), var(3), 'tofu', var(4)),
                          (var(0), var(1), var(2), var(3), var(4), 'tofu', var(5)),
                          (var(0), var(1), var(2), var(3), var(4), var(5), 'tofu', var(6)),
                          (var(0), var(1), var(2), var(3), var(4), var(5), var(6), 'tofu', var(7)),
                          (var(0), var(1), var(2), var(3), var(4), var(5), var(6), var(7), 'tofu', var(8)),
                          (var(0), var(1), var(2), var(3), var(4), var(5), var(6), var(7), var(8), 'tofu', var(9)),])

    def test_rembero(self):

        def question_4_30(out): return fresh(lambda y: rembero('peas', ['a', 'b', y, 'd', 'peas', 'e'], out))
        self.assertEqual(run(fresh(question_4_30), n=1), [['a', 'b', 'd', 'peas', 'e']])

        def question_4_31(out): return fresh(lambda y, z: rembero(y, ['a', 'b', y, 'd', z, 'e'], out))
        self.assertEqual(run(fresh(question_4_31)), 
                         [['b', 'a', 'd', var(0), 'e'],
                          ['a', 'b', 'd', var(0), 'e'],
                          ['a', 'b', 'd', var(0), 'e'],
                          ['a', 'b', 'd', var(0), 'e'],
                          ['a', 'b', var(0), 'd', 'e'],
                          ['a', 'b', 'e', 'd', var(0)],
                          ['a', 'b', var(0), 'd', var(1), 'e'],])

        def question_4_49(r, y, z): return conj(rembero(y, [y, 'd', z, 'e'], [y, 'd', 'e']), unify([y, z], r))
        self.assertEqual(run(fresh(question_4_49)), 
                         [['d', 'd'], ['d', 'd'], [var(1), var(1)], ['e', 'e']])

        def question_4_57(w, y, z, out): return rembero(y, ['a', 'b', y, 'd', z] + w, out)
        self.assertEqual(run(fresh(question_4_57), n=14), 
                         [var(0),
                          var(0),
                          var(0),
                          var(0),
                          var(0),
                          [],
                          (var(0), var(1)),
                          [var(0)],
                          (var(0), var(1), var(2)),
                          [var(0), var(1)],
                          (var(0), var(1), var(2), var(3)),
                          [var(0), var(1), var(2)],
                          (var(0), var(1), var(2), var(3), var(4)),
                          [var(0), var(1), var(2), var(3)]])

    def test_surprise(self):

        def question_4_69(r): return conj(unify('d', r), surpriseo(r, list('abc')))
        self.assertEqual(run(fresh(question_4_69)), ['d'])

        def question_4_70(r): return surpriseo(r, list('abc'))
        self.assertEqual(run(fresh(question_4_70)), [var(0)])

        def question_4_71(r): return conj(surpriseo(r, list('abc')), unify('b', r))
        self.assertEqual(run(fresh(question_4_71)), ['b'])

        def question_4_72(r): return conj(unify('b', r), surpriseo(r, list('abc')))
        self.assertEqual(run(fresh(question_4_72)), ['b'])

    def test_appendo(self):

        def question_5_10(x): return appendo(['cake'], ['tastes', 'yummy'], x)
        self.assertEqual(run(fresh(question_5_10)), [['cake', 'tastes', 'yummy']])

        def question_5_11(x, y): return appendo(['cake', 'with', 'ice', y], ['tastes', 'yummy'], x)
        self.assertEqual(run(fresh(question_5_11)), [['cake', 'with', 'ice', var(0), 'tastes', 'yummy']])

        def question_5_12(x, y): return appendo(['cake', 'with', 'ice', 'cream'], y, x)
        self.assertEqual(run(fresh(question_5_12)), [('cake', 'with', 'ice', 'cream', var(0))])

        def question_5_13(x, y): return appendo(['cake', 'with', 'ice'] + y, ['d', 't'], x)
        self.assertEqual(run(fresh(question_5_13), n=1), [['cake', 'with', 'ice', 'd', 't']])
        self.assertEqual(run(fresh(lambda y, x: question_5_13(x, y)), n=1), [[]]) # 5.14.1
        self.assertEqual(run(fresh(question_5_13), n=1, var_selector=lambda x, y: y), [[]]) # 5.14.2

        def question_5_16(x, y): return appendo(['cake', 'with', 'ice'] + y, ['d', 't'], x)
        self.assertEqual(run(fresh(question_5_16), n=5), 
                         [['cake', 'with', 'ice', 'd', 't'],
                          ['cake', 'with', 'ice', var(0), 'd', 't'],
                          ['cake', 'with', 'ice', var(0), var(1), 'd', 't'],
                          ['cake', 'with', 'ice', var(0), var(1), var(2), 'd', 't'],
                          ['cake', 'with', 'ice', var(0), var(1), var(2), var(3), 'd', 't']])
        self.assertEqual(run(fresh(question_5_16), n=5, var_selector=lambda x, y: y), 
                         [[],
                          [var(0)],
                          [var(0), var(1)],
                          [var(0), var(1), var(2)],
                          [var(0), var(1), var(2), var(3)]]) # 5.17

        def question_5_20(x, y): return appendo(['cake', 'with', 'ice'] + y, ['d', 't'] + y, x)
        self.assertEqual(run(fresh(question_5_20), n=5), 
                         [['cake', 'with', 'ice', 'd', 't'],
                          ['cake', 'with', 'ice', var(1), 'd', 't', var(1)],
                          ['cake', 'with', 'ice', var(2), var(3), 'd', 't', var(2), var(3)],
                          ['cake', 'with', 'ice', var(3), var(4), var(5), 'd', 't', var(3), var(4), var(5)],
                          ['cake', 'with', 'ice', var(4), var(5), var(6), var(7), 'd', 't', var(4), var(5), var(6), var(7)]])

        def question_5_21(x, y): return appendo(['cake', 'with', 'ice', 'cream'], ['d', 't'] + y, x)
        self.assertEqual(run(fresh(question_5_21)), [('cake', 'with', 'ice', 'cream', 'd', 't', var(0))])

        def question_5_23(x, y): return appendo(x, y, ['cake', 'with', 'ice', 'd', 't'])
        self.assertEqual(run(fresh(question_5_23), n=6), 
                         [[],
                          ['cake'],
                          ['cake', 'with'],
                          ['cake', 'with', 'ice'],
                          ['cake', 'with', 'ice', 'd'],
                          ['cake', 'with', 'ice', 'd', 't']])

        self.assertEqual(run(fresh(question_5_23), n=6, var_selector=lambda x, y: y), 
                         [['cake', 'with', 'ice', 'd', 't'],
                          ['with', 'ice', 'd', 't'],
                          ['ice', 'd', 't'],
                          ['d', 't'],
                          ['t'],
                          []]) # 5.25

        def question_5_27(r, x, y): return conj(appendo(x, y, ['cake', 'with', 'ice', 'd', 't']), unify([x, y], r))
        self.assertEqual(run(fresh(question_5_27), n=6),
                         [[[], ['cake', 'with', 'ice', 'd', 't']],
                          [['cake'], ['with', 'ice', 'd', 't']],
                          [['cake', 'with'], ['ice', 'd', 't']],
                          [['cake', 'with', 'ice'], ['d', 't']],
                          [['cake', 'with', 'ice', 'd'], ['t']],
                          [['cake', 'with', 'ice', 'd', 't'], []]])

        with self.assertRaises(RecursionError):
            run(fresh(question_5_27), n=7) # 5.29

        def question_5_32(r, x, y): return conj(appendso(x, y, ['cake', 'with', 'ice', 'd', 't']), unify([x, y], r))
        self.assertEqual(run(fresh(question_5_32), n=7),
                         [[[], ['cake', 'with', 'ice', 'd', 't']],
                          [['cake'], ['with', 'ice', 'd', 't']],
                          [['cake', 'with'], ['ice', 'd', 't']],
                          [['cake', 'with', 'ice'], ['d', 't']],
                          [['cake', 'with', 'ice', 'd'], ['t']],
                          [['cake', 'with', 'ice', 'd', 't'], []]])

        self.assertEqual(run(fresh(lambda x, y, z: appendso(x, y, z)), n=7), 
                         [[],
                          [var(0)],
                          [var(0), var(1)],
                          [var(0), var(1), var(2)],
                          [var(0), var(1), var(2), var(3)],
                          [var(0), var(1), var(2), var(3), var(4)],
                          [var(0), var(1), var(2), var(3), var(4), var(5)]]) # 5.33.

        self.assertEqual(run(fresh(lambda y, x, z: appendso(x, y, z)), n=7), 
                         [var(0), var(0), var(0), var(0), var(0), var(0), var(0)]) # 5.34

        self.assertEqual(run(fresh(lambda z, x, y: appendso(x, y, z)), n=7), 
                         [var(0),
                          (var(0), var(1)),
                          (var(0), var(1), var(2)),
                          (var(0), var(1), var(2), var(3)),
                          (var(0), var(1), var(2), var(3), var(4)),
                          (var(0), var(1), var(2), var(3), var(4), var(5)),
                          (var(0), var(1), var(2), var(3), var(4), var(5), var(6))]) # 5.36.

        def question_5_37(r, x, y, z): return conj(appendso(x, y, z), unify([x, y, z], r))
        self.assertEqual(run(fresh(question_5_37), n=7), 
                         [[[], var(1), var(1)], # in other words: unify([] + var(1), var(1))
                          [[var(2)], var(3), (var(2), var(3))],
                          [[var(3), var(4)], var(5), (var(3), var(4), var(5))],
                          [[var(4), var(5), var(6)], var(7), (var(4), var(5), var(6), var(7))],
                          [[var(5), var(6), var(7), var(8)], var(9), (var(5), var(6), var(7), var(8), var(9))],
                          [[var(6), var(7), var(8), var(9), var(10)], var(11), (var(6), var(7), var(8), var(9), var(10), var(11))],
                          [[var(7), var(8), var(9), var(10), var(11), var(12)], var(13), (var(7), var(8), var(9), var(10), var(11), var(12), var(13))]])

        with self.assertRaises(RecursionError):
            run(fresh(swappendso), n=1, var_selector=lambda l, s, out: out) # 5.40

        self.assertEqual(run(fresh(bswappendso(bound=5)), n=1), [[var(0), var(1), var(2), var(3)]]) # 5.40.1
        self.assertEqual(run(fresh(bswappendso(bound=5)), n=5), [[var(0), var(1), var(2), var(3)], [var(0), var(1), var(2)], [var(0), var(1)], [var(0)], []]) # 5.40.2

    def test_unwrapo(self):

        self.assertEqual(run(fresh(lambda x: unwrapo([[['pizza']]], x))), 
                         ['pizza',
                          ['pizza'],
                          [['pizza']],
                          [[['pizza']]]]) # 5.46

        with self.assertRaises(RecursionError):
            run(fresh(lambda x: unwrapo(x, 'pizza')), n=1) # 5.48

        with self.assertRaises(RecursionError):
            run(fresh(lambda x: unwrapo([[x]], 'pizza')), n=1) # 5.49

        self.assertEqual(run(fresh(lambda x: unwrapso(x, 'pizza')), n=5), 
                         ['pizza',
                          ('pizza', var(0)),
                          (('pizza', var(0)), var(1)),
                          ((('pizza', var(0)), var(1)), var(2)),
                          (((('pizza', var(0)), var(1)), var(2)), var(3)),]) # 5.53

        self.assertEqual(run(fresh(lambda x: unwrapso(x, [['pizza']])), n=5), 
                         [[['pizza']],
                          ([['pizza']], var(0)),
                          (([['pizza']], var(0)), var(1)),
                          ((([['pizza']], var(0)), var(1)), var(2)),
                          (((([['pizza']], var(0)), var(1)), var(2)), var(3)),]) # 5.54

        self.assertEqual(run(fresh(lambda x: unwrapso([[x]], 'pizza')), n=5), 
                         ['pizza',
                          ('pizza', var(0)),
                          (('pizza', var(0)), var(1)),
                          ((('pizza', var(0)), var(1)), var(2)),
                          (((('pizza', var(0)), var(1)), var(2)), var(3)),]) # 5.55

    def test_flatteno(self):

        self.assertEqual(run(fresh(lambda x: flatteno([['a', 'b'], 'c'], x)), n=1), [['a', 'b', 'c']]) # 5.60
        self.assertEqual(run(fresh(lambda x: flatteno(['a', ['b', 'c']], x)), n=1), [['a', 'b', 'c']]) # 5.61
        self.assertEqual(run(fresh(lambda x: flatteno(['a'], x))), [['a'], ['a', []], [['a']]]) # 5.62
        self.assertEqual(run(fresh(lambda x: flatteno([['a']], x))), 
                         [['a'], 
                          ['a', []], 
                          ['a', []], 
                          ['a', [], []], 
                          [['a']],
                          [['a'], []],
                          [[['a']]]]) # 5.64
        self.assertEqual(run(fresh(lambda x: flatteno([[['a']]], x))), 
                         [['a'], 
                          ['a', []], 
                          ['a', []], 
                          ['a', [], []], 
                          ['a', []],
                          ['a', [], []],
                          ['a', [], []],
                          ['a', [], [], []],
                          [['a']],
                          [['a'], []],
                          [['a'], []],
                          [['a'], [], []],
                          [[['a']]],
                          [[['a']], []],
                          [[[['a']]]],
                          ]) # 5.66
        self.assertEqual(run(fresh(lambda x: flatteno([['a', 'b'], 'c'], x))), 
                         [['a', 'b', 'c'],
                          ['a', 'b', 'c', []],
                          ['a', 'b', ['c']],
                          ['a', 'b', [], 'c'],
                          ['a', 'b', [], 'c', []],
                          ['a', 'b', [], ['c']],
                          ['a', ['b'], 'c'],
                          ['a', ['b'], 'c', []],
                          ['a', ['b'], ['c']],
                          [['a', 'b'], 'c'],
                          [['a', 'b'], 'c', []],
                          [['a', 'b'], ['c']],
                          [[['a', 'b'], 'c']]]) # 5.68

        with self.assertRaises(RecursionError):
            run(fresh(lambda x: flatteno(x, ['a', 'b', 'c'])))


        self.assertEqual(run(fresh(lambda x: flatteno([['a', 'b'], 'c'], x))), 
                         list(reversed(run(fresh(lambda x: flattenrevo([['a', 'b'], 'c'], x)))))) # 5.75

        self.assertEqual(run(fresh(lambda x: flattenrevo(x, ['a', 'b', 'c'])), n=2), 
                         [('a', 'b', 'c'), ['a', 'b', 'c']]) # 5.77

        self.assertEqual(run(conj(flattenrevo(('a', 'b', 'c'), ['a', 'b', 'c']), 
                                  flattenrevo(['a', 'b', 'c'], ['a', 'b', 'c']))), [Tautology()]) # 5.78

        with self.assertRaises(RecursionError):
            run(fresh(lambda x: flattenrevo(x, ['a', 'b', 'c'])), n=3) # 5.79

        self.assertEqual(run(fresh(lambda x: flatteno([[[['a', [[['b']]], 'c']]], 'd'], x)), n=1), [['a', 'b', 'c', 'd']]) # 5.80.1
        self.assertEqual(len(run(fresh(lambda x: flattenrevo([[[['a', [[['b']]], 'c']]], 'd'], x)))), 574) # 5.80.2


    def test_second_order_predicates(self):

        def question_6_5(q): return conj(nevero, fail)
        with self.assertRaises(RecursionError): run(fresh(question_6_5), n=1)

        def question_6_6(q): return conj(fail, nevero)
        self.assertEqual(run(fresh(question_6_6), n=1), [])

        def question_6_7(q): return conj(alwayso, unify(True, q))
        self.assertEqual(run(fresh(question_6_7), n=1), [True])

        def question_6_9(q): return conj(alwayso, unify(True, q))
        with self.assertRaises(RecursionError): run(fresh(question_6_9))

        def question_6_10(q): return conj(alwayso, unify(True, q))
        self.assertEqual(run(fresh(question_6_10), n=5), [True, True, True, True, True])

        def question_6_11(q): return conj(unify(True, q), alwayso)
        self.assertEqual(run(fresh(question_6_11), n=5), [True, True, True, True, True])

        def question_6_13(q): return conj(succeed_at_least(alwayso), unify(True, q))
        self.assertEqual(run(fresh(question_6_13), n=1), [True])

        def question_6_14(q): return conj(succeed_at_least(nevero), unify(True, q))
        self.assertEqual(run(fresh(question_6_14), n=1), [True])

        def question_6_14_1(q): return conj(succeed_at_least(nevero, times=2), unify(True, q))
        self.assertEqual(run(fresh(question_6_14_1), n=2), [True, True])
        with self.assertRaises(RecursionError): run(fresh(question_6_14_1), n=3)

        with self.assertRaises(RecursionError): run(fresh(question_6_14_1)) # 6.15

        def question_6_16(q): return conj(succeed_at_least(nevero), fail, unify(True, q))
        with self.assertRaises(RecursionError): run(fresh(question_6_16), n=1)
        
        def question_6_17(q): return conj(alwayso, fail, unify(True, q))
        with self.assertRaises(RecursionError): run(fresh(question_6_17), n=1)

        def question_6_18(q): return conj(conde([unify(False, q), alwayso],
                                                else_clause=[anyo(unify(True, q))]),
                                          unify(True, q))
        with self.assertRaises(RecursionError): run(fresh(question_6_18), n=1)

        def question_6_19(q): return conj(condi([unify(False, q), alwayso],
                                                else_clause=[unify(True, q)]),
                                          unify(True, q))
        self.assertEqual(run(fresh(question_6_19), n=1), [True])

        with self.assertRaises(RecursionError): run(fresh(question_6_19), n=2) # 6.20

        def question_6_21(q): return conj(condi([unify(False, q), alwayso],
                                                else_clause=[anyo(unify(True, q))]),
                                          unify(True, q))
        self.assertEqual(run(fresh(question_6_21), n=5), [True,True,True,True,True,])

        def question_6_24(r): return condi([tea_cupo(r), succeed],
                                           [unify(False, r), succeed])
        self.assertEqual(run(fresh(question_6_24), n=5), ['tea', False, 'cup'])

        def question_6_25(q): return conj(condi([unify(False, q), alwayso],
                                                [unify(True, q), alwayso]),
                                          unify(True, q))
        self.assertEqual(run(fresh(question_6_25), n=5), [True, True, True, True, True,])

        def question_6_27(q): return conj(conde([unify(False, q), alwayso],
                                                [unify(True, q), alwayso]),
                                          unify(True, q))
        with self.assertRaises(RecursionError): run(fresh(question_6_27), n=5)

        def question_6_28(q): return conj(conde([alwayso, succeed],
                                                else_clause=[nevero]),
                                          unify(True, q))
        self.assertEqual(run(fresh(question_6_28), n=5), [True,True,True,True,True,])

        def question_6_30(q): return conj(condi([alwayso, succeed],
                                                else_clause=[nevero]),
                                          unify(True, q))
        with self.assertRaises(RecursionError): run(fresh(question_6_30), n=5)

        def question_6_31(q):
            return conj(conde([unify(False, q), succeed],
                              else_clause=[unify(True, q)]),
                        alwayso,
                        unify(True, q))
        with self.assertRaises(RecursionError): run(fresh(question_6_31), n=1)

        def question_6_32(q):
            return conj(
                    conj(conde([unify(False, q), succeed],
                               else_clause=[unify(True, q)]),
                         alwayso,
                         interleaving=True),
                    unify(True, q))
        self.assertEqual(run(fresh(question_6_32), n=1), [True])
        self.assertEqual(run(fresh(question_6_32), n=5), [True, True, True, True, True]) # 6.33
        
        def question_6_33_1(q, interleaving): 
            return conj(conde([unify(False, q), succeed], 
                              else_clause=[unify(True, q)]), 
                        alwayso, 
                        interleaving=interleaving)
        self.assertEqual(run(fresh(lambda q: question_6_33_1(q, False)), n=6), [False, False, False, False, False, False])
        self.assertEqual(run(fresh(lambda q: question_6_33_1(q, True)), n=6), [False, True, False, True, False, True])

        def question_6_34(q):
            return conj(
                    conj(conde([unify(True, q), succeed],
                               else_clause=[unify(False, q)]),
                         alwayso,
                         interleaving=True),
                    unify(True, q))
        self.assertEqual(run(fresh(question_6_34), n=5), [True, True, True, True, True])

        def question_6_34_1(q, interleaving): 
            return conj(conde([unify(True, q), succeed], 
                              else_clause=[unify(False, q)]), 
                        alwayso, 
                        interleaving=interleaving)
        self.assertEqual(run(fresh(lambda q: question_6_34_1(q, False)), n=6), 
                         [True,True,True,True,True,True,])
        self.assertEqual(run(fresh(lambda q: question_6_34_1(q, True)), n=6), 
                         [True, False, True, False, True, False])

        def question_6_35(q):
            return conj(
                    conj(conde([succeed, succeed],
                               else_clause=[nevero]),
                         alwayso),
                    unify(True, q))
        self.assertEqual(run(fresh(question_6_35), n=5), [True, True, True, True, True]) 

        def question_6_36(q):
            return conj(
                    conj(conde([succeed, succeed],
                               else_clause=[nevero]),
                         alwayso,
                         interleaving=True),
                    unify(True, q))
        self.assertEqual(run(fresh(question_6_36), n=1), [True]) 
        with self.assertRaises(RecursionError): run(fresh(question_6_36), n=2)
        with self.assertRaises(RecursionError): run(fresh(question_6_36), n=5)


    def test_bitwise_ops(self):

        def question_7_6(s, x, y): return conj(bit_xoro(x, y, 0), unify([x, y], s))
        self.assertEqual(run(fresh(question_7_6)), [[0,0], [1,1]])

        def question_7_7(s, x, y): return conj(bit_xoro(x, y, 1), unify([x, y], s))
        self.assertEqual(run(fresh(question_7_7)), [[1,0], [0,1]])

        def question_7_8(r, s, x, y): return conj(bit_xoro(x, y, s), unify([x, y, s], r))
        self.assertEqual(run(fresh(question_7_8)), 
                         [[0,0,0], 
                          [1,0,1], 
                          [0,1,1], 
                          [1,1,0]])
        self.assertEqual(run(fresh(rel(bit_xoro))),
                         [[0,0,0], 
                          [1,0,1], 
                          [0,1,1], 
                          [1,1,0]])

        def question_7_11(s, x, y): return conj(bit_ando(x, y, 1), unify([x, y], s))
        self.assertEqual(run(fresh(question_7_11)), [[1,1]])

        def question_7_12(r): return half_addero(1, 1, r, 1)
        self.assertEqual(run(fresh(question_7_12)), [0])

        self.assertEqual(run(fresh(rel(half_addero))), 
                         [[0,0,0,0],
                          [1,0,1,0],
                          [0,1,1,0],
                          [1,1,0,1]]) # 7.13
        
        self.assertEqual(run(fresh(lambda s, r, c: conj(full_addero(0, 1, 1, r, c), unify([r,c], s)))), [[0,1]]) # 7.15
        self.assertEqual(run(fresh(lambda s, r, c: conj(full_addero(1, 1, 1, r, c), unify([r,c], s)))), [[1,1]]) # 7.16
        self.assertEqual(run(fresh(rel(full_addero))), 
                         [
                         [0,0,0,0,0],
                         [1,0,0,1,0],
                         [0,1,0,1,0],
                         [1,1,0,0,1],
                         [0,0,1,1,0],
                         [1,0,1,0,1],
                         [0,1,1,0,1],
                         [1,1,1,1,1],
                         ]) # 7.17

    def test_build_num(self):
        self.assertEqual(num.build(0), [])
        with self.assertRaises(TypeError): self.assertEqual(int([]), 0) # 7.22
        self.assertEqual(int(num(1, [])), 1) # 7.24
        self.assertEqual(int(num(1, num(0, num(1, [])))), 5) # 7.25
        self.assertEqual(int(num(1, cons(1, cons(1, [])))), 7) # 7.26
        self.assertEqual(num.build(9), num(1, num(0, num(0, num(1, []))))) # 7.27
        self.assertEqual(num.build(6), num(0, num(1, num(1, [])))) # 7.29
        self.assertEqual(num.build(19), num(1, num(1, num(0, num(0, num(1, [])))))) # 7.42
        self.assertEqual(num.build(36), num(0, num(0, num(1, num(0, num(0, num(1, []))))))) # 7.43

    def test_a_bit_too_much(self):
        self.assertEqual(run(fresh(lambda q: conj(poso([0, 1, 1]), unify(True, q)))), [True]) # 7.80
        self.assertEqual(run(fresh(lambda q: conj(poso([1]), unify(True, q)))), [True]) # 7.81
        self.assertEqual(run(fresh(lambda q: conj(poso([]), unify(True, q)))), []) # 7.82
        self.assertEqual(run(fresh(poso)), [(var(0), var(1))]) # 7.83
        self.assertEqual(run(fresh(lambda q: conj(greater_than_oneo([0, 1, 1]), unify(True, q)))), [True]) # 7.86
        self.assertEqual(run(fresh(lambda q: conj(greater_than_oneo([0, 1]), unify(True, q)))), [True]) # 7.87
        self.assertEqual(run(fresh(lambda q: conj(greater_than_oneo([1]), unify(True, q)))), []) # 7.88
        self.assertEqual(run(fresh(lambda q: conj(greater_than_oneo([]), unify(True, q)))), []) # 7.89
        self.assertEqual(run(fresh(greater_than_oneo)), [(var(0), var(1), var(2))]) # 7.90
        
        self.assertEqual(run(fresh(lambda s, x, y, r: conj(addero(0, x, y, r), unify([x, y, r], s))), n=3),
                         [[var(1), [], var(1)],
                          [[], (var(2), var(3)), (var(2), var(3))],
                          [[1], [1], [0, 1]]]) # 7. 97

        self.assertEqual(run(fresh(lambda s, x, y, r: conj(addero(0, x, y, r), unify([x, y, r], s))), n=22),
                         [[var(1), [], var(1)],
                          [[], (var(2), var(3)), (var(2), var(3))],
                          [[1], [1], [0, 1]],
                          [[1], (0, var(2), var(3)), (1, var(2), var(3))],
                          [(0, var(2), var(3)), [1], (1, var(2), var(3))],
                          [[1], [1, 1], [0, 0, 1]],
                          [[0, 1], [0, 1], [0, 0, 1]],
                          [[1], (1, 0, var(2), var(3)), (0, 1, var(2), var(3))],
                          [[1, 1], [1], [0, 0, 1]],
                          [[1], [1, 1, 1], [0, 0, 0, 1]],
                          [[1, 1], [0, 1], [1, 0, 1]],
                          [[1], (1, 1, 0, var(2), var(3)), (0, 0, 1, var(2), var(3))],
                          [(1, 0, var(2), var(3)), [1], (0, 1, var(2), var(3))],
                          [[1], [1, 1, 1, 1], [0, 0, 0, 0, 1]],
                          [[0, 1], [1, 1], [1, 0, 1]], # instead of: [[0, 1], (0, 0, var(2), var(3)), (0, 1, var(2), var(3))],
                          [[1], (1, 1, 1, 0, var(2), var(3)), (0, 0, 0, 1, var(2), var(3))],
                          [[1, 1, 1], [1], [0, 0, 0, 1]],
                          [[1], [1, 1, 1, 1, 1], [0, 0, 0, 0, 0, 1]],
                          [[1, 1], [1, 1], [0, 1, 1]], # instead of: [[0, 1], [1, 1], [1, 0, 1]],
                          [[1], (1, 1, 1, 1, 0, var(2), var(3)), (0, 0, 0, 0, 1, var(2), var(3))],
                          [(1, 1, 0, var(2), var(3)), [1], (0, 0, 1, var(2), var(3))],
                          [[1], [1, 1, 1, 1, 1, 1], [0, 0, 0, 0, 0, 0, 1]],
                          ]) # 7.101

        self.assertEqual(run(fresh(lambda s: _addero(1, [0, 1, 1], [1, 1], s))), [[0, 1, 0, 1]]) # 7.120
        self.assertEqual(run(fresh(lambda s, x, y: conj(addero(0, x, y, [1, 0, 1]), unify([x, y], s)))),
                         [[[1, 0, 1], []],
                          [[], [1, 0, 1]],
                          [[1], [0, 0, 1]],
                          [[0, 0, 1], [1]],
                          [[1, 1], [0, 1]],
                          [[0, 1], [1, 1]],]) # 7.126
        self.assertEqual(run(fresh(lambda s, x, y: conj(pluso(x, y, [1, 0, 1]), unify([x, y], s)))),
                         [[[1, 0, 1], []],
                          [[], [1, 0, 1]],
                          [[1], [0, 0, 1]],
                          [[0, 0, 1], [1]],
                          [[1, 1], [0, 1]],
                          [[0, 1], [1, 1]],]) # 7.128

        self.assertEqual(run(fresh(lambda q: minuso([0, 0, 0, 1], [1, 0, 1], q))), [[1, 1]]) # 7.131
        self.assertEqual(run(fresh(lambda q: minuso(8, 5, q))), [int_to_list(3)]) # 7.131.1
        self.assertEqual(run(fresh(lambda q: minuso(8, 5, q)), post=lambda r: int(num(r.car, r.cdr))), [3]) # 7.131.2
        self.assertEqual(run(fresh(lambda q: minuso(6, 6, q)), post=lambda r: 0 if r == [] else r), [0]) # 7.132
        self.assertEqual(run(fresh(lambda q: minuso(6, 8, q)), post=lambda r: 0 if r == [] else r), []) # 7.133


    @unittest.expectedFailure
    def test_rightmost_representative(self):
        self.assertEqual(rightmost_representative(num.build([0, 1, 1])), [[0, 1, 1], [], 2]) # 7.92
        self.assertEqual(rightmost_representative(num.build((0, var(0), 1, 0, var(1), var(2)))), 
                         [[0, var(0), 1], (0, var(1), var(2)), 2]) # 7.93
        self.assertEqual(rightmost_representative(num.build((0, 0, var(0), var(1)))), [[], None, 2]) # 7.94
        self.assertEqual(rightmost_representative(num.build(var(0))), [[], None, 0]) # 7.95


    def test_under_the_hood(self):
        self.assertEqual(run(fresh(lambda q: conj(unify(False, q), project(q, into=lambda q: unify(not(not q), q))))), [False]) # 9.47
        self.assertEqual(run(fresh(lambda q: conj(unify(False, q), unify(not(not q), q)))), []) # 9.47
        self.assertEqual(run(fresh(lambda q: conj(unify(3, q), project(q, into=lambda q: unify(q+1, 4))))), [3]) # 9.47.1
        with self.assertRaises(Exception): run(fresh(lambda q: conj(unify(3, q), unify(q+1, 4)))) # 9.47.2








