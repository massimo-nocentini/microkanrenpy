
import unittest

from muk.core import *
from muk.ext import *
from muk.sexp import *
from muk.utils import *

from mclock import *

class mcculloch_test(unittest.TestCase):

    def test_fst_rule(self):
        self.assertEqual(run(mcculloch([2,3,4,5], [3,4,5])), [Tautology()])   
        self.assertEqual(run(fresh(lambda α, β: mcculloch([4]+β, α))), [])   
        self.assertEqual(run(fresh(lambda α: mcculloch([2,3,4,5], α))), [[3,4,5]])   
        self.assertEqual(run(fresh(lambda α: mcculloch(α, [3,4,5]))), [[2,3,4,5]])   

    def test_snd_rule(self):
        self.assertEqual(run(mcculloch([3,2,5], [5,2,5])), [Tautology()])   
        self.assertEqual(run(fresh(lambda α: mcculloch([3,3,2,5], α)), n=1), [[5,2,5,2,5,2,5]])   
        self.assertEqual(run(fresh(lambda α, β: conj(mcculloch(β, [5,2,5,2,5,2,5]), 
                                                     appendo(α, [5], β)))), 
                         [[3, 3, 2], [2, 5, 2, 5, 2, 5, 2], [3, 2, 5, 2],])   

    def test_a_curious_number_machine(self):
        self.assertEqual(run(fresh(lambda α: mcculloch(α, α)), n=1), [[3,2,3]]) # 1
        self.assertEqual(run(fresh(lambda α, β: conj(associateo(α, β), mcculloch(α, β))), n=1), [[3, 3, 2, 3, 3]]) # 2
        with let([3, 3, 2, 3, 3]) as N: self.assertEqual(run(fresh(lambda α: mcculloch(N, α)), n=1), [N+[2]+N]) # 2.1
        self.assertEqual(run(fresh(lambda α: mcculloch(α, [7]+α)), n=1), [[3,2,7,3]]) # 5
        self.assertEqual(run(fresh(lambda α, β: conj(mcculloch([3]+α, β), associateo(α, β),)), n=1), [[3, 2, 3]]) # 6
        self.assertEqual(run(fresh(lambda α, β: conj(associateo([3]+α, β), mcculloch(α, β),)), n=1), [[3, 3, 2, 3, 3, 3]]) # 7
        self.assertEqual(run(fresh(lambda γ: mcculloch_lawo([7], γ, [7]+γ)), n=1), [[3, 2, 7, 3]]) # 8, generalizes 5
        self.assertEqual(run(fresh(lambda out, α, γ, β: conj(appendo([3, 2]+α, [3], γ), 
                                                          mcculloch_lawo(α, γ, β),
                                                          unify([α, γ], out))), n=4), 
                         [[[], [3, 2, 3]],
                          [[rvar(0)], [3, 2, rvar(0), 3]],
                          [[rvar(0), rvar(1)], [3, 2, rvar(0), rvar(1), 3]],
                          [[rvar(0), rvar(1), rvar(2)], [3, 2, rvar(0), rvar(1), rvar(2), 3]]]) # 8
        with let([5,6]) as A:
            self.assertEqual(run(fresh(lambda γ, Aγ, β: conj(appendo(A, γ, Aγ),
                                                             associateo(Aγ, β),
                                                             mcculloch(γ, β))), n=1), [[3, 3, 2, 5, 6, 3, 3]]) # 9
        self.assertEqual(run(fresh(lambda out, α, γ, αγ, β: conj(appendo([3, 3, 2]+α, [3, 3], γ), 
                                                          appendo(α, γ, αγ),
                                                          associateo(αγ, β),
                                                          unify([α, γ], out))), n=4),
                         [[[], [3, 3, 2, 3, 3]],
                          [[rvar(0)], [3, 3, 2, rvar(0), 3, 3]],
                          [[rvar(0), rvar(1)], [3, 3, 2, rvar(0), rvar(1), 3, 3]],
                          [[rvar(0), rvar(1), rvar(2)], [3, 3, 2, rvar(0), rvar(1), rvar(2), 3, 3]]]) # 9
        self.assertEqual(run(fresh(lambda ν, ν2ν, ν2ν2ν2ν: conj(associateo(ν, ν2ν), 
                                                                associateo(ν2ν, ν2ν2ν2ν), 
                                                                mcculloch(ν, ν2ν2ν2ν))), n=1), [[3, 3, 3, 2, 3, 3, 3]]) # 10
