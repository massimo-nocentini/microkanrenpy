
import unittest

from muk.core import *
from muk.ext import *
from muk.sexp import *
from reasonedschemer import *

class reasonedschemer_test(unittest.TestCase):

    def test_succeed_fail(self):
        self.assertEqual(run(succeed), [Tautology()]) # 1.6
        self.assertEqual(run(fail), []) # 1.10
        self.assertEqual(run(fresh(lambda q: unify(True, q))), [True]) # 1.11
        
        def question_1_12(q): return fail, unify(True, q)
        self.assertEqual(run(fresh(question_1_12)), [])
        self.assertEqual(run(fresh(lambda q: (fail, unify(True, q)))), []) # 1.12
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

        def tea_cupo(x):
            return conde([unify('tea', x), succeed],
                         [unify('cup', x), succeed])
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
                             post=lambda l: ''.join(l)), ['acorn']) # 2.21
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

        def question_4_13(q): return memo('tofu', ['tofu', 'e'], ['tofu', 'e']), unify(True, q)
        self.assertEqual(run(fresh(question_4_13)), [True])

        def question_4_14(q): return memo('tofu', ['tofu', 'e'], ['tofu']), unify(True, q)
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

        def question_4_49(r, y, z): return rembero(y, [y, 'd', z, 'e'], [y, 'd', 'e']), unify([y, z], r)
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

        def question_4_69(r): return unify('d', r), surpriseo(r, list('abc'))
        self.assertEqual(run(fresh(question_4_69)), ['d'])

        def question_4_70(r): return surpriseo(r, list('abc'))
        self.assertEqual(run(fresh(question_4_70)), [var(0)])

        def question_4_71(r): return surpriseo(r, list('abc')), unify('b', r)
        self.assertEqual(run(fresh(question_4_71)), ['b'])

        def question_4_72(r): return unify('b', r), surpriseo(r, list('abc'))
        self.assertEqual(run(fresh(question_4_72)), ['b'])


