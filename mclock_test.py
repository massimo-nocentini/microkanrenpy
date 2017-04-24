
import unittest

from muk.core import *
from muk.ext import *
from muk.sexp import *
from muk.utils import *

from mclock import *

class mcculloch_test(unittest.TestCase):

    def test_fst_rule(self):
        self.assertEqual(run(mccullocho([2,3,4,5], [3,4,5])), [Tautology()])   
        self.assertEqual(run(fresh(lambda α, β: mccullocho([4]+β, α))), [])   
        self.assertEqual(run(fresh(lambda α: mccullocho([2,3,4,5], α))), [[3,4,5]])   
        self.assertEqual(run(fresh(lambda α: mccullocho(α, [3,4,5]))), [[2,3,4,5]])   

    def test_snd_rule(self):
        self.assertEqual(run(mccullocho([3,2,5], [5,2,5])), [Tautology()])   
        self.assertEqual(run(fresh(lambda α: mccullocho([3,3,2,5], α)), n=1), [[5,2,5,2,5,2,5]])   
        self.assertEqual(run(fresh(lambda α, β: conj(mccullocho(β, [5,2,5,2,5,2,5]), 
                                                     appendo(α, [5], β)))), 
                         [[3, 3, 2], [2, 5, 2, 5, 2, 5, 2], [3, 2, 5, 2],])   

    def test_third_rule(self):
        self.assertEqual(run(fresh(lambda α: mcculloch_o([4,2,7,6,9,5], α)), n=1), [[5,9,6,7]])

    def test_a_curious_number_machine_chapter(self):

        self.assertEqual(run(fresh(lambda α: mccullocho(α, α)), n=1), [[3,2,3]]) # 1
        self.assertEqual(run(fresh(lambda α, β: conj(associateo(α, β), mccullocho(α, β))), n=1), [[3, 3, 2, 3, 3]]) # 2
        with let([3, 3, 2, 3, 3]) as N: self.assertEqual(run(fresh(lambda α: mccullocho(N, α)), n=1), [N+[2]+N]) # 2.1
        self.assertEqual(run(fresh(lambda α: mccullocho(α, [7]+α)), n=1), [[3,2,7,3]]) # 5
        self.assertEqual(run(fresh(lambda α, β: conj(mccullocho([3]+α, β), associateo(α, β),)), n=1), [[3, 2, 3]]) # 6
        self.assertEqual(run(fresh(lambda α, β: conj(associateo([3]+α, β), mccullocho(α, β),)), n=1), [[3, 3, 2, 3, 3, 3]]) # 7
        self.assertEqual(run(fresh(lambda γ: mcculloch_lawo([7], γ, [7]+γ)), n=1), [[3, 2, 7, 3]]) # 8, generalizes 5
        self.assertEqual(run(fresh(lambda out, α, γ, β: conji(appendo([3, 2]+α, [3], γ), 
                                                              mcculloch_lawo(α, γ, β),
                                                              unify([α, γ], out))), n=4), 
                         [[[], [3, 2, 3]],
                          [[rvar(0)], [3, 2, rvar(0), 3]],
                          [[rvar(0), rvar(1)], [3, 2, rvar(0), rvar(1), 3]],
                          [[rvar(0), rvar(1), rvar(2)], [3, 2, rvar(0), rvar(1), rvar(2), 3]]]) # proof of 8
        with let([5,6]) as A:
            self.assertEqual(run(fresh(lambda γ, Aγ, Aγ2Aγ: conji(appendo(A, γ, Aγ), 
                                                                  associateo(Aγ, Aγ2Aγ), 
                                                                  mccullocho(γ, Aγ2Aγ))), n=1), [[3, 3, 2, 5, 6, 3, 3]]) # 9
        self.assertEqual(run(fresh(lambda out, α, γ, αγ, αγ2αγ: conji(appendo([3, 3, 2]+α, [3, 3], γ), 
                                                                      appendo(α, γ, αγ),
                                                                      associateo(αγ, αγ2αγ),
                                                                      mccullocho(γ, αγ2αγ),
                                                                      unify([α, γ], out))), n=4),
                         [[[], [3, 3, 2, 3, 3]],
                          [[rvar(0)], [3, 3, 2, rvar(0), 3, 3]],
                          [[rvar(0), rvar(1)], [3, 3, 2, rvar(0), rvar(1), 3, 3]],
                          [[rvar(0), rvar(1), rvar(2)], [3, 3, 2, rvar(0), rvar(1), rvar(2), 3, 3]]]) # proof of 9
        self.assertEqual(run(fresh(lambda ν, ν2ν, ν2ν2ν2ν: conji(associateo(ν, ν2ν), 
                                                                 associateo(ν2ν, ν2ν2ν2ν), 
                                                                 mccullocho(ν, ν2ν2ν2ν))), n=1), [[3, 3, 3, 2, 3, 3, 3]]) # 10
        self.assertEqual(run(fresh(lambda α: mccullocho([3]+α, [3]+α)), n=1), [[2,3]]) # 12, a particular case of 1
        self.assertEqual(run(fresh(lambda α: mccullocho([3]+α, [2]+α)), n=1), [[2,2]]) # 13
        self.assertEqual(run(fresh(lambda α: mccullocho([3]+α, [3, 2]+α)), n=1), [[2,3,2]]) # 13
        self.assertEqual(run(fresh(lambda α, αα, ααα, ααα2, _3α2, β: 
                                        conji(appendo(α, α, αα), appendo(α, αα, ααα), appendo(ααα, [2], ααα2), 
                                              appendo([3]+α, [2], _3α2), 
                                              mccullocho(ααα2, β), 
                                              mccullocho(_3α2, β),)), n=1), [[2]]) # 15
        self.assertEqual(run(fresh(lambda γ, γ2γ, γγ: conji(associateo(γ, γ2γ), 
                                                            appendo(γ, γ, γγ), 
                                                            mccullocho(γ2γ, γγ))), n=10), 
                         [[],
                          [2]*1,
                          [2]*2,
                          [2]*3,
                          [2]*4,
                          [2]*5,
                          [2]*6,
                          [2]*7,
                          [2]*8,
                          [2]*9,
                          ]) # 16
        self.assertEqual(run(fresh(lambda γ, γ2γ, γγ: conji(associateo(γ, γ2γ), 
                                                            appendo(γ, γ, γγ), 
                                                            mccullocho(γγ, γ2γ))), n=1), # just as the previous one with swapped args
                         [[3,2]]) # 17
        self.assertEqual(run(fresh(lambda ν, ν2ν, ν2ν2ν2ν: conji(associateo(ν, ν2ν), 
                                                                 associateo(ν2ν, ν2ν2ν2ν), 
                                                                 mccullocho(ν2ν, ν2ν2ν2ν))), n=1), [[3,3]]) # 18
        self.assertEqual(run(fresh(lambda α, α23: conji(appendo(α, [2,3], α23), mccullocho(α, α23))), n=1), [[3,2,3,2,3]]) # 19


    @unittest.skip('Unsatisfiable goals but running forever')
    def test_hopeless(self):

        # TODO: fix the following when we'll have the constraint system
        self.assertEqual(run(fresh(lambda α, α2, α2α, α2_l, α2α_l: 
                                        conji(mccullocho(α, α2α), lengtho(α2α, α2α_l),
                                              appendo(α, [2], α2), lengtho(α2, α2_l),
                                              leqo(α2α_l, α2_l), # having constraints could be helpful
                                              mccullocho(α, α2))), n=1), []) # 20

    def test_lengtho(self):
        self.assertEqual(run(fresh(lambda l: lengtho([3,2,8,7], l))), [4])
        with self.assertRaises(RecursionError): 
            self.assertEqual(run(fresh(lambda l, α: lengtho([3,2,8,7]+α, l))), [5])

    @unittest.skip("They takes too long")
    def test_longrunning(self):

        with let([7,8]) as A:
            self.assertEqual(run(fresh(lambda γ, Aγ, Aγ2Aγ, Aγ2Aγ2Aγ2Aγ:
                                            conji(appendo(A, γ, Aγ),
                                                  associateo(Aγ, Aγ2Aγ),
                                                  associateo(Aγ2Aγ, Aγ2Aγ2Aγ2Aγ),
                                                  mccullocho(γ, Aγ2Aγ2Aγ2Aγ))), n=1), [[3, 3, 3, 2, 7, 8, 3, 3, 3]]) # 11

        self.assertEqual(run(fresh(lambda out, α, γ, αγ, αγ2αγ, αγ2αγ2αγ2αγ: 
                                        conji(appendo([3, 3, 3, 2]+α, [3, 3, 3], γ), 
                                              mccullocho(γ, αγ2αγ2αγ2αγ), 
                                              appendo(α, γ, αγ), 
                                              associateo(αγ, αγ2αγ), 
                                              associateo(αγ2αγ, αγ2αγ2αγ2αγ), 
                                              unify([α, γ], out))), n=4),
                         [[[], [3, 3, 3, 2, 3, 3, 3]],
                          [[rvar(0)], [3, 3, 3, 2, rvar(0), 3, 3, 3]],
                          [[rvar(0), rvar(1)], [3, 3, 3, 2, rvar(0), rvar(1), 3, 3, 3]],
                          [[rvar(0), rvar(1), rvar(2)], [3, 3, 3, 2, rvar(0), rvar(1), rvar(2), 3, 3, 3]]]) # proof of 11


    def test_craigs_law_chapter(self):
        self.assertEqual(run(fresh(lambda α: mcculloch_o(α, α)), n=3),
                         [[3, 2, 3], [4, 3, 4, 2, 4, 3, 4], [3, 4, 4, 2, 3, 4, 4]]) # 1
        self.assertEqual(run(fresh(lambda α, α_reversed: conji(reverseo(α, α_reversed), 
                                                              mcculloch_o(α, α_reversed), 
                                                              complement(symmetrico(α)))), n=6), 
                         [[3, 4, 2, 3, 4], 
                          [4, 3, 2, 4, 3],
                          [3, 4, 4, 4, 2, 3, 4, 4, 4],
                          [4, 3, 4, 4, 2, 4, 3, 4, 4],
                          [4, 4, 3, 4, 2, 4, 4, 3, 4],
                          [4, 4, 4, 3, 2, 4, 4, 4, 3]]) # 2
        self.assertEqual(run(fresh(lambda α, α_reversed, α_reversed2α_reversed: 
                                        conj(reverseo(α, α_reversed), 
                                             associateo(α_reversed, α_reversed2α_reversed),
                                             mcculloch_o(α, α_reversed2α_reversed),)), n=5), 
                         [[3, 3, 2, 3, 3],
                          [3, 3, 4, 2, 3, 3, 4],
                          [4, 3, 3, 2, 4, 3, 3],
                          [3, 4, 3, 2, 3, 4, 3],
                          [3, 4, 4, 3, 2, 3, 4, 4, 3], 
                          ]) # 3.e
        self.assertEqual(run(fresh(lambda α, α_reversed, α_reversed2α_reversed: 
                                        conji(reverseo(α, α_reversed), 
                                              associateo(α_reversed, α_reversed2α_reversed),
                                              mcculloch_o(α, α_reversed2α_reversed),)), n=5),
                         [[3, 3, 2, 3, 3],
                          [3, 3, 4, 2, 3, 3, 4],
                          [4, 3, 3, 2, 4, 3, 3],
                          [3, 4, 4, 3, 2, 3, 4, 4, 3],
                          [3, 4, 3, 2, 3, 4, 3],
                          ]) # 3.i
        self.assertEqual(run(fresh(lambda α, αα: conji(repeato(α, αα), mcculloch__o(α, αα))), n=2), 
                         [[5, 3, 2, 5, 3], [5, 5, 2, 5, 5, 2]]) # 4
        self.assertEqual(run(fresh(lambda α, αα, αα_reversed:
                                        conji(reverseo(αα, αα_reversed), 
                                              repeato(α, αα), 
                                              mcculloch__o(α, αα_reversed),)), n=2),
                         [[5, 3, 4, 2, 5, 3, 4], [4,5,3,2,4,5,3]]) # 5
        self.assertEqual(run(fresh(lambda α, αα: conji(repeato(α, αα), mcculloch__o([5]+α, αα))), n=3),
                         [[3, 2, 3], [5, 2, 5, 2], [3, 4, 4, 2, 3, 4, 4]]) # 7
        self.assertEqual(run(fresh(lambda α, α2α, α2αα2α:
                                        conji(associateo(α, α2α), 
                                             repeato(α2α, α2αα2α), 
                                             mcculloch__o(α, α2αα2α),)), n=1), 
                         [[5, 3, 3, 2, 5, 3, 3]]) # 8
        self.assertEqual(run(fresh(lambda α, αα, αα2αα:        
                                        conji(repeato(α, αα), 
                                             associateo(αα, αα2αα), 
                                             mcculloch__o(α, αα2αα),)), n=2), 
                         [[3, 5, 3, 2, 3, 5, 3], 
                          [3, 5, 5, 2, 3, 5, 5, 2]]) # 9



