
import unittest

from muk.core import *
from muk.ext import *
from muk.sexp import *

class microkanren_tests(unittest.TestCase):

    def test_infinte_recursion_not_guarded(self):

        def fives(x):
            return disj(unify(x, 5), fives(x))
        
        with self.assertRaises(RecursionError), states_stream(fresh(fives)) as α:
            next(α)

    def test_infinte_recursion_guarded_refreshing(self):

        def fives(x):
            return disj(unify(x, 5), fresh(fives))

        with states_stream(fresh(fives)) as α:
            self.assertEqual([state(sub={var(i, 'x'): 5}, next_index=i+1) for i in range(10)], 
                             [next(α) for _ in range(10)])

    def test_infinte_recursion_guarded_ηinverse(self):

        def fives(x):
            return disj(unify(x, 5), fresh(lambda: fives(x)))

        with states_stream(fresh(fives)) as α:
            self.assertEqual(   [state(sub={var(0, 'x'): 5}, next_index=1)]*10, 
                                [next(α) for _ in range(10)])

    def test_ηinverse_and_snooze(self):

        def sixes_η(x):
            return disj(unify(x, 6), fresh(lambda: sixes_η(x)))

        def sixes_snooze(x):
            return disj(unify(x, 6), snooze(sixes_snooze, [x]))

        with states_stream(fresh(sixes_η)) as α,\
             states_stream(fresh(sixes_snooze)) as β:
            self.assertEqual(   [next(α) for _ in range(10)], 
                                [next(β) for _ in range(10)])


    def test_interleaving_of_5s_and_6s(self):

        def ns(x, n):
            return disj(unify(x, n), snooze(ns, [x, n]))

        with states_stream(fresh(lambda x: disj(ns(x, 5), ns(x, 6)))) as α:
            numbers = [state(sub={var(0, 'x'): 5}, next_index=1), 
                       state(sub={var(0, 'x'): 6}, next_index=1)]
            self.assertEqual(numbers * 5, [next(α) for _ in range(10)])


    def test_nats(self):

        def ns(x, n):
            return disj(unify(x, n), snooze(ns, [x, n+1]))

        with states_stream(fresh(lambda x: ns(x, 0))) as α:
            nats = [state(sub={var(0, 'x'): i}, next_index=1) for i in range(10)]
            self.assertEqual(nats, [next(α) for _ in range(10)])

    def test_nats_by_evens_and_odds(self):

        def ns(x, n):
            return disj(unify(x, n), snooze(ns, [x, n+2]))

        with states_stream(fresh(lambda x: disj(ns(x, 0), ns(x, 1)))) as α:
            nats = [state(sub={var(0, 'x'): i}, next_index=1) for i in range(10)]
            self.assertEqual(nats, [next(α) for _ in range(10)])

    def test_fail_goal(self):

        def ns(x, n):
            return disj(unify(x, n), snooze(ns, [x, n]))

        self.assertEqual(run(fresh(lambda x: conj(fail, ns(x, 5)))), [])

    def test_divergent_goal_despite_fail_in_conj(self):

        def ns(x, n):
            return disj(unify(x, n), snooze(ns, [x, n]))

        with self.assertRaises(RecursionError):
            run(fresh(lambda x: conj(ns(x, 5), fail)))

    def test_simple_list_unification(self):

        def gbody(r):
            return fresh(lambda x, y: unify([y, 4, x], r))

        results = run(fresh(gbody))
        self.assertEqual(results, [[var(0), 4, var(1)]])
        self.assertEqual(str(results[0]), '[v₀, 4, v₁]')


    def test_unify(self):

        self.assertEqual(
            run(fresh(lambda w, x, y, z: 
                conj(unify([3,[4,5],6], [3, [x, y], z]),
                     unify([x, y, z], w)))), [[4,5,6]])

        self.assertEqual(
            run(fresh(lambda w, x, y, z: 
                conj(unify([3,[4,5],6], (3, [x, y], z)),
                     unify([x, y, z], w)))), [[4,5,[6]]])

        self.assertEqual(
            run(fresh(lambda w, x, y, z: 
                conj(unify([3,[4,5],6], [3, [x, y]] + z),
                     unify([x, y, z], w)))), [[4,5,[6]]])

        self.assertEqual(
            run(fresh(lambda w, x, y, z: 
                conj(unify((3,[4,5],6), [3, [x, y]] + z),
                     unify([x, y, z], w)))), [[4,5,6]])

        with self.assertRaises(TypeError):
            self.assertEqual(
                run(fresh(lambda w, x, y, z: 
                    conj(unify([3,[4,5],6], x + ([4, y], z)),
                         unify([x, y, z], w)))), [[3,5,[6]]])





