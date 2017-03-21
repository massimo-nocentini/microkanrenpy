
import unittest

from microkanren import *
from reasonedschemer import *
from sexp import *

class reasonedschemer_test(unittest.TestCase):

    def test_conde(self):
        
        def g_body(x):
            return conde([unify('extra', x), succeed],
                         [unify('virgin', x), fail],
                         [unify('olive', x), succeed],
                         [unify('oil', x), succeed])

        self.assertEqual(run(fresh(g_body), n=2), ['extra', 'olive'])

    def test_nullo(self):
        self.assertEqual(run(nullo([])), [var(0)]) 
        self.assertEqual(run(nullo([1, 2])), []) 
        self.assertEqual(run(fresh(lambda x: nullo([]))), [var(0)]) 
        self.assertEqual(run(fresh(lambda x: nullo(x))), [[]]) 

    def test_caro(self):
        self.assertEqual(run(fresh(lambda a: caro(list_to_cons('acorn'), a))), ['a'])
        self.assertEqual(run(fresh(lambda a: caro(cons(a, list_to_cons('corn')), 'a'))), ['a'])
        self.assertEqual(run(fresh(lambda p: caro(p, 'a'))), [ ('a', var(1)) ])

    def test_listo(self):
        self.assertEqual(run(fresh(lambda l: listo(l)), n=5), 
            [[], 
             [var(1)], 
             [var(1), var(5)],
             [var(1), var(5), var(9)],
             [var(1), var(5), var(9), var(13)]])

        self.assertEqual(run(listo(list_to_cons(l=(1,2,3,4)))), []) # because the list isn't proper
        self.assertEqual(
            run(fresh(lambda w, x: conj(listo(list_to_cons(l=(1,2,3,4,x))),
                                        unify(list_to_cons(l=(1,2,3,4,x)), w)), 
                      arity=2), 
                n=3), 
            [[1,2,3,4], [1,2,3,4,var(18)], [1,2,3,4, var(18), var(22)]])


    def test_pairo(self):
        self.assertEqual(run(fresh(lambda p: pairo(p))), [(var(1), var(2))])

    def test_conso(self):
        self.assertEqual(run(fresh(lambda p: conso(3, p, cons(3, cons(2, []))))), [[2]])



