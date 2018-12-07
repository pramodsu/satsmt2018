from __future__ import print_function

import z3

# This file shows how one would use Z3 to prove that
# the following transition system satisfies the invariant
# a <= b.
#
# The difference from induction-ex1.py is that we need
# to introduce a strengthening invariant below in the 
# definition of phi.
#
# M = (X, Init, R)
# X = {a, b}
# Init(X) = (a == 0 && b == 1)
# R(X, X') = (a' = b && b' = a + b)
# phi(X) = (a <= b)
# psi(X) = ??? && (a <= b)

def main():
    # create the variables a and b.
    a, b = z3.Ints('a b')
    # create the variables a' and b'
    a_p, b_p = z3.Ints('a_p b_p')
    
    # now we will check the base case for the induction

    # create the property
    phi = a <= b

    # this is the invariant.
    # TODO: replace True with something that proves the property
    def psi(a, b):
        return True

    # first create a solver object.
    S = z3.Solver()
    # first we will check if psi(X) ==> phi(X)
    # we do this by checking whether Not(psi(X) ==> phi(X)) is UNSAT
    S.add(z3.Not(z3.Implies(psi(a, b), phi)))
    if S.check() == z3.sat:
        print ('Invariant does not imply property.')
        print ('Counterexample:')
        m = S.model()
        print ('\ta =', m.eval(a))
        print ('\tb =', m.eval(b))
        return
    else:
        print ('Invariant implies property.')


    # again create a solver object.
    S = z3.Solver()
    # create the init predicate. 
    Init = z3.And(a == 0, b == 1)
    # we want to check whether Init(X) ==> psi(X) is valid.
    # we do this by checking whether Not(Init(X) ==> psi(X)) is UNSAT
    S.add(z3.Not(z3.Implies(Init, psi(a, b))))
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
    R = z3.And(a_p == b, b_p == a + b)
    # we want to check if R(X, X') && psi(X) ==>  psi(X')
    # we will do this by checking if the negation of the above is UNSAT
    S.add(z3.Not(z3.Implies(z3.And(psi(a, b), R), psi(a_p, b_p))))
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

