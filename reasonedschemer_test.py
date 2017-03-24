
import unittest

from microkanren import *
from reasonedschemer import *
from sexp import *

class reasonedschemer_test(unittest.TestCase):

    def test_conde(self):
        self.assertEqual(run(fresh(lambda x: conde([unify('extra', x), succeed], 
                                                   [unify('virgin', x), fail], 
                                                   [unify('olive', x), succeed], 
                                                   [unify('oil', x), succeed])), n=2), 
                         ['extra', 'olive'])

    def test_nullo(self):
        self.assertEqual(run(nullo([])), [True]) 
        self.assertEqual(run(nullo([1, 2])), []) 
        self.assertEqual(run(fresh(lambda x: nullo([]))), [var(0)]) 
        self.assertEqual(run(fresh(lambda x: nullo(x))), [[]]) 

    def test_caro(self):
        self.assertEqual(run(fresh(lambda a: caro(list('acorn'), a))), ['a'])
        self.assertEqual(run(fresh(lambda a: caro(cons(a, list('corn')), 'a'))), ['a'])
        self.assertEqual(run(fresh(lambda p: caro(p, 'a'))), [('a', var(0))])

    def test_listo(self):
        self.assertEqual(run(fresh(lambda l: listo(l)), n=5), 
            [[], 
             [var(0)], 
             [var(0), var(1)],
             [var(0), var(1), var(2)],
             [var(0), var(1), var(2), var(3)]])

        self.assertEqual(run(listo((1,2,3,4))), []) # because the list isn't proper
        self.assertEqual(
            run(fresh(lambda w, x: conj(listo((1,2,3,4,x)),
                                        unify((1,2,3,4,x), w))), n=3), 
            [[1,2,3,4], [1,2,3,4,var(0)], [1,2,3,4, var(0), var(1)]])

    def test_pairo(self):
        self.assertEqual(run(fresh(lambda p: pairo(p))), [(var(0), var(1))])

    def test_conso(self):
        self.assertEqual(run(fresh(lambda p: conso(3, p, cons(3, cons(2, []))))), [[2]])
        self.assertEqual(run(fresh(lambda p: conso(3, p, [3,2,1]))), [[2, 1]])



