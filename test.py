
from microkanren import *
from sympy import Add, S, symbols

def fives(x):
    return disj(unify(x, 5), fresh(fives))

def fives_(x):
    return disj(unify(x, 5), fresh(lambda: fives_(x), arity=0))

def sixes(x):
    return disj(unify(x, 6), fresh(lambda: sixes(x), arity=0))

def sixes_(x):
    return disj(unify(x, 6), snooze(sixes_, [x]))

fives_and_sixes = fresh(lambda x: disj(fives_(x), sixes_(x)))
frooney = fresh(lambda x: conj(fail, fives_(x)))
frooney_ = fresh(lambda x: conj(fives_(x), fail))

α = fives_and_sixes(emptystate())
β = frooney(emptystate())

print([next(α) for i in range(10)])
print(run(fives_and_sixes, n=10))
print(run(frooney, n=10))
#print(run(frooney_, n=1))

def gbody(r):
    return fresh(lambda x, y: unify([y, 4, x], r), arity=2)

print(run(fresh(gbody), n=10))

def gbody(x):
    return conde(   [unify('extra', x), succeed],
                    [unify('virgin', x), fail],
                    [unify('olive', x), succeed],
                    [unify('oil', x), succeed])

print(run(fresh(gbody), n=2))

def gbody(q):
    return caro('acorn', q)

print(run(fresh(gbody)))

print(run(nullo([2,3])))

print('list_to_cons')
c = list_to_cons([1,2,3]) 
print(c)
print(cons_to_list(c))

c = list_to_cons((1,[2,3], 4))
print(c)
print(cons_to_list(c))
print('hello')
print(cons_to_list(cons(cons(3, []), cons(cons(4, 5), 6))))
print('hello')
print(run(fresh(lambda w, x, y, z: conj(unify(  list_to_cons([3,[4,5],6]), 
                                                #list_to_cons((3, [x, y], [z]),)),
                                                list_to_cons((3, [x, y], z),)),
                                        unify([x, y, z], w)), arity=4)))
print('hello')
print(run(fresh(lambda p: conso(3, p, cons(3, cons(2, [])))), post=cons_to_list))
print(run(fresh(lambda p: caro(p, 'a'))))
print(run(fresh(lambda p: pairo(p))))
print(run(fresh(lambda l: listo(l)), n=5, post=cons_to_list))
print(run(listo((1,2,3,4))))
print('hello')
print(run(fresh(lambda x: listo(list_to_cons((1,2,3,4,x)))), n=5, post=cons_to_list))

#x = symbols('x')
#print(run(fresh(lambda y: unify(S(3), Add(4, x)))))

def gbody(q):
    return caro(q, 'a')

print(run(fresh(gbody)))




