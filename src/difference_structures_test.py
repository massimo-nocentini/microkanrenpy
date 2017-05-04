
import unittest

from muk.core import *
from muk.ext import *

class difference_structures_test(unittest.TestCase):

    def test_extend_list(self):
        self.assertEqual(run(fresh(lambda α: unify([]+α, []))), [[]])
        self.assertEqual(run(fresh(lambda α: unify([1, 2, 3]+α, [1,2]))), [])
        self.assertEqual(run(fresh(lambda α: unify([1, 2, 3]+α, [1,2,3]))), [[]])
        self.assertEqual(run(fresh(lambda α: unify([1, 2, 3]+α, [1,2,3,4,5,6,7]))), [[4,5,6,7]])
        self.assertEqual(run(fresh(lambda α, β: unify([1, 2, 3]+α, [1,2,3,4,5]+β))), [[4,5]+rvar(0)])
        self.assertEqual(run(fresh(lambda out, α, β: unify([1, 2, 3]+α, [1,2,3,4,5]+β) & unify([α, β], out))), [[[4,5]+rvar(0), rvar(0)]])
        self.assertEqual(run(fresh(lambda out, α, β: unify([1, 2, 3]+α, [1,2,3,4,5]+β) & 
                                                     unify(β, [6,7,8]) &
                                                     unify([α, β], out))), [[[4,5,6,7,8], [6,7,8]]])
