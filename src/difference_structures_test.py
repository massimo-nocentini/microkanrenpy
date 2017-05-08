
import unittest

from muk.core import *
from muk.ext import *

class difference_structures_test(unittest.TestCase):

    def test_extend_list(self):
        self.assertEqual(run(fresh(lambda α: unify([]+α, []))), [[]])
        self.assertEqual(run(fresh(lambda β, α: unify([]+α, β))), [[]+rvar(0)])
        self.assertEqual(run(fresh(lambda α: unify([1, 2, 3]+α, [1,2]))), [])
        self.assertEqual(run(fresh(lambda α: unify([1, 2, 3]+α, [1,2,3]))), [[]])
        self.assertEqual(run(fresh(lambda α: unify([1, 2, 3]+α, [1,2,3,4,5,6,7]))), [[4,5,6,7]])
        self.assertEqual(run(fresh(lambda α, β: unify([1, 2, 3]+α, [1,2,3,4,5]+β))), [[4,5]+rvar(0)])
        self.assertEqual(run(fresh(lambda out, α, β: unify([1, 2, 3]+α, [1,2,3,4,5]+β) & unify([α, β], out))), [[[4,5]+rvar(0), rvar(0)]])
        self.assertEqual(run(fresh(lambda out, α, β: unify([1, 2, 3]+α, [1,2,3,4,5]+β) & 
                                                     unify(β, [6,7,8]) &
                                                     unify([α, β], out))), [[[4,5,6,7,8], [6,7,8]]])
        self.assertEqual(run(fresh(lambda X, Y, α, β, : 
                                                    unify([1,2,3]+α, X) & 
                                                    unify([4,5,6]+β, Y) & 
                                                    unify(α, Y))), [[1,2,3,4,5,6]+rvar(0)])

    def test_difference_list(self):
        self.assertEqual(run(fresh(lambda out, α: unify(α - α, out))), [ [] ]) # the null difference list
        self.assertEqual(run(fresh(lambda out, α: unify(([]+α) - α, out))), [ ([]+rvar(0))-rvar(0) ]) # the null difference list
        self.assertEqual(run(fresh(lambda β, α: unify(([1,2,3]+α)-α, β))), [([1,2,3]+rvar(0))-rvar(0)])
        self.assertEqual(run(fresh(lambda β, α: rectify(([1,2,3]+α)-α, β))), [ [1,2,3] ])
        self.assertEqual(run(fresh(lambda α: unify(([1,2,3]+α)-α, [1,2,3]))), [rvar(0)])
        self.assertEqual(run(fresh(lambda α: unify(([1,2,3]+α)-α, [1,2]))), [])
        self.assertEqual(run(fresh(lambda α: unify(([1,2,3]+α)-α, [1,2,3,4]))), [])
        self.assertEqual(run(fresh(lambda β, α: unify(([1,2,3]+α)-α, [1,2,3]+β))), [[]])
        self.assertEqual(run(fresh(lambda α, β: unify(([1,2,3]+α)-α, [1,2,3]+β))), [rvar(0)]) 
        self.assertEqual(run(fresh(lambda β, α: unify(([1,2,3]+α)-α, [1,2,3,4]+β))), [])
        self.assertEqual(run(fresh(lambda β, α: unify(([1,2,3]+α)-α, [1,2]+β))), [[3]])
        self.assertEqual(run(fresh(lambda α, β: unify(([1,2,3]+α)-α, [1,2]+β))), [rvar(0)])
        self.assertEqual(run(fresh(lambda out, X, Y, x, y, α, β, : 
                                                    unify([1,2,3]+α, x) & unify(x-α, X) &
                                                    unify([4,5,6]+β, y) & unify(y-β, Y) &
                                                    unify(x-β, out))), [([1,2,3]+rvar(0))-rvar(1)])
        self.assertEqual(run(fresh(lambda out, X, Y, x, y, α, β, : 
                                                    unify([1,2,3]+α, x) & unify(x-α, X) &
                                                    unify([4,5,6]+β, y) & unify(y-β, Y) &
                                                    unify(α, y) &
                                                    unify(x-β, out))), [([1,2,3,4,5,6]+rvar(0))-rvar(0)])
        self.assertEqual(run(fresh(lambda out, X, Y, x, y, α, β, : 
                                                    unify([1,2,3]+α, x) & unify(x-α, X) &
                                                    unify([4,5,6]+β, y) & unify(α-β, Y) &
                                                    unify(x-β, out))), [([1,2,3]+rvar(0))-rvar(1)])
        self.assertEqual(run(fresh(lambda out, X, Y, x, α, β, : 
                                                    unify([1,2,3]+α, x) & unify(x-α, X) &
                                                    unify([4,5,6]+β, α) & unify(α-β, Y) &
                                                    unify(x-β, out))), [([1,2,3,4,5,6]+rvar(0))-rvar(0)])

        
    def test_appendo(self):

        def appendo(X, Y, XY):
            return fresh(lambda α, β, γ: unify(X, α-β) & unify(Y, β-γ) & unify(XY, α-γ))

        self.assertEqual(run(fresh(lambda αβ, α, β: appendo(([1,2,3]+α)-α, ([4,5,6]+β)-β, αβ))), 
                         [([1,2,3,4,5,6]+rvar(0))-rvar(0)])
        self.assertEqual(run(fresh(lambda out, X, Y, α, β:  appendo(([1,2,3]+α)-α, ([4,5,6]+β)-β, X-Y) & 
                                                            unify([X, Y], out))), 
                         [[[1, 2, 3, 4, 5, 6] + rvar(0), rvar(0)]])




