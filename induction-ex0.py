from __future__ import print_function

import z3

# This file shows how one would use Z3 to prove that
# the following transition system satisfies the invariant
# a <= b.
#
# M = (X, Init, R)
# X = {a, b}
# Init(X) = (a == 0 && b == 1)
# R(X, X') = (a' = a + 1 && b' = b + 1)
# prop(X) = (a <= b)

def main():
    # create the variables a and b.
    a, b = z3.Ints('a b')
    # create the variables a' and b'
    a_p, b_p = z3.Ints('a_p b_p')
    
    # now we will check the base case for the induction

    # first create a solver object.
    S = z3.Solver()
    # create the init predicate. 
    Init = z3.And(a == 0, b == 1)
    # create the property
    prop = a <= b
    # we want to check whether Init(X) ==> prop(X) is valid.
    # we do this by checking whether Not(Init(X) ==> prop(X)) is UNSAT
    S.add(z3.Not(z3.Implies(Init, prop)))
    if S.check() == z3.sat:
        print ('Base case does not hold. Property is FALSE.')
        print ('Counterexample: ')
        m = S.model()
        print ('\ta =', m.eval(a))
        print ('\tb =', m.eval(b))
    else:
        print ('Base case HOLDS.')

    # now we will check the inductive step.

    # create a new solver object.
    S = z3.Solver()
    R = z3.And(a_p == a + 1, b_p == b + 1)
    prop   = a <= b
    prop_p = a_p <= b_p
    # we want to check if R(X, X') && prop(X) ==>  prop(X')
    # we will do this by checking if the negation of the above is UNSAT
    S.add(z3.Not(z3.Implies(z3.And(prop, R), prop_p)))
    if S.check() == z3.sat:
        print ('Inductive step does not hold. Property is UNDEF.')
        print ('Counterexample to induction:')
        m = S.model()
        print ('\ta =', m.eval(a))
        print ('\tb =', m.eval(b))
        print ('\ta_p =', m.eval(a_p))
        print ('\tb_p =', m.eval(b_p))
    else:
        print ('Inductive step HOLDS.')

if __name__ == '__main__':
    main()
