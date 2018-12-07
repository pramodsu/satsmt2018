from __future__ import print_function

import z3

def main():
    N = 9
    frames = []
    for p in range(N):
        frames.append(z3.BitVec('cnt_%d' % p, 3))

    def init(cnt):
        return (cnt == 0)

    def R(cnt, cntp):
        return (cntp == cnt + 1)

    def to_gray(cnt): return (cnt ^ z3.LShR(cnt, 1))
    def hd(n1, n2):
        d = (n1 ^ n2)
        d0 = z3.ZeroExt(1, z3.Extract(0, 0, d))
        d1 = z3.ZeroExt(1, z3.Extract(1, 1, d))
        d2 = z3.ZeroExt(1, z3.Extract(2, 2, d))
        return (d0 + d1 + d2)

    S = z3.Solver()
    S.add(init(frames[0]))

    checks = []
    for p in range(1, N):
        # get count in previous step
        cnt_prev = frames[p - 1]
        # get count in current step.
        cnt_curr = frames[p]

        # ADD constraint to solver.
        S.add(R(cnt_prev, cnt_curr))

        # get gray encoded version of count previous.
        gray_cnt_prev = to_gray(cnt_prev)
        # get gray encoded version of count current.
        gray_cnt_curr = to_gray(cnt_curr)

        # compute hamming distance b/w gray cnt prev and curr
        dist = hd(gray_cnt_prev, gray_cnt_curr)
        # check if this is not equal to one.
        check_curr = (dist != 1)
        # add to the list or checks.
        checks.append(check_curr)

    S.push()
    S.add(z3.Or(*checks))
    result = S.check()
    if result == z3.unsat:
        print ("Property HOLDS.")
    else:
        print ("Property does not HOLD.")
    S.pop()

    S.push()
    # add a constraint stating that all the states must be distict
    # check for satisfiability and fix the condition below
    if True: # FIXME: change this condition.
        print ('Reachability diameter not reached.')
    else:
        print ('Reachability diameter reached.')

if __name__ == '__main__':
    main()
