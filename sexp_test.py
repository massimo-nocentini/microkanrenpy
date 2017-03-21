
import unittest

from sexp import *

class sexp_tests(unittest.TestCase):
         
    def test_null_list(self):
        self.isomorphism(l=[], c=[])

    def test_singleton_proper_list_to_cons(self):
        self.isomorphism(l=[1], c=cons(1, []))

    def test_plain_proper_list_to_cons(self):
        self.isomorphism(l=[1,2,3], c=cons(1, cons(2, cons(3, []))))

    def test_plain_improper_list_to_cons(self):
        self.isomorphism(l=(1,2,3), c=cons(1, cons(2, 3)))

    def test_nested_improper_list_to_cons(self):
        self.isomorphism(l=(1,[2,3], 4), c=cons(1, cons(cons(2, cons(3, [])), 4)))

    def test_more_nested_improper_list_to_cons(self):
        self.isomorphism(l=([3],(4,5), 6), c=cons(cons(3, []), cons(cons(4, 5), 6)))

    @unittest.expectedFailure
    def test_invalid_improper_list(self):
        list_to_cons(l=(3,))

    @unittest.expectedFailure
    def test_invalid_improper_cons(self):
        cons_to_list(c=cons(3, ()))

    def isomorphism(self, l, c):
        self.assertEqual(c, list_to_cons(l))
        self.assertEqual(l, cons_to_list(c))

         




