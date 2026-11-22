"""E72: finite C-state event schedules and first-return witnesses.

Independently transcribed L17 transition table, complete tapes and arbitrary
right exteriors. This is bounded M evidence, NOT a Lean first-return proof.
"""
import random
import unittest

OPS = (((1, +1, 1), (0, +1, 4)),
       ((1, -1, 2), (0, +1, 0)),
       ((0, -1, 3), (1, -1, 1)),
       ((1, -1, 0), (1, -1, 4)),
       ((0, -1, 1), (0, -1, 5)),
       ((1, -1, 3), None))


def guard(family, M):
    return ("1" if family == 1 else "111") + "10" * 7 + "1101" + "10" * M + "111"


def clock(family, M, u, v):
    return (214 if family == 1 else 268) + 6*M + 2*u + (4 if family == 1 else 2)*v


def c_schedule(family, M, u, v):
    if M < 1:
        raise ValueError("M=0 is excluded: known E60 clock counterexample")
    if family == 1:
        return ([0, 25, 42, 67, 80, 105+6*M, 143+6*M, 155+6*M,
                 159+6*M, 194+6*M+4*v, 206+6*M+4*v]
                + [210+6*M+4*v+2*j for j in range(u+3)])
    if family == 3:
        return ([0, 25, 68, 105, 118, 143+6*M, 205+6*M, 217+6*M]
                + [221+6*M+2*j for j in range(v+4)]
                + [252+6*M+2*v, 264+6*M+2*v]
                + [268+6*M+2*v+2*j for j in range(u+1)])
    raise ValueError(family)


def simulate(family, M, u, v, R, offset):
    left = "10"*(u+6)+"0"+"10"*(v+7)+"0"+"10"+"01"*2
    right = "0111"+guard(family,M)+R
    origin = offset-len(left)
    tape = {origin+i for i,b in enumerate(left+right) if b == "1"}
    q, h = 2, offset
    observed = []
    for t in range(clock(family,M,u,v)+1):
        if q == 2:
            observed.append((t, any(x<h for x in tape)))
        if t == clock(family,M,u,v):
            break
        op = OPS[q][int(h in tape)]
        if op is None:
            raise AssertionError(("unexpected halt",family,M,u,v,t))
        bit, d, q = op
        if bit: tape.add(h)
        else: tape.discard(h)
        h += d
    final_word = (
        "1"*(2*u+6)+"01"*(v+8)+"010100"+"10"*(16+M)+R
        if family == 1 else
        "1"*(2*u+1)+"10"*7+"1"*(2*v+4)+"01"*(21+M)+"0"+R
    )
    expected = (2,origin,frozenset(origin+i for i,b in enumerate(final_word) if b=="1"))
    return observed,(q,h,frozenset(tape)),expected


class E72FirstReturnCensus(unittest.TestCase):
    def test_440_full_C_event_schedules_and_left_witnesses(self):
        rng = random.Random(720072)
        checked = 0
        for family in (1,3):
            for M in (1,2,3,4,5,8,16,30,50,100,200):
                for u,v in ((0,0),(0,1),(1,0),(1,2),(2,3),
                            (3,1),(4,5),(7,9),(10,0),(0,10)):
                    for rep in range(2):
                        R = "".join(rng.choices("01",k=rng.randrange(51)))+"1"
                        offset = rng.randrange(-2000,2001)
                        seen, actual, expected = simulate(family,M,u,v,R,offset)
                        self.assertEqual([t for t,_ in seen],c_schedule(family,M,u,v))
                        self.assertTrue(all(has_left for t,has_left in seen[:-1]))
                        self.assertEqual(seen[-1],(clock(family,M,u,v),False))
                        self.assertEqual(actual,expected)
                        self.assertEqual(len(seen),(14+u) if family==1 else (15+u+v))
                        prelude = 88 if family==1 else 126
                        post_sweep = prelude+6*M
                        post_bridge = post_sweep+(77 if family==1 else 95)
                        pre = [t for t,_ in seen if t < prelude]
                        scanner_sweep = [t for t,_ in seen if prelude <= t < post_sweep]
                        bridge = [t for t,_ in seen if post_sweep <= t < post_bridge]
                        final = [t for t,_ in seen if t >= post_bridge]
                        self.assertEqual(
                            (len(pre),len(scanner_sweep),len(bridge),len(final)),
                            (5,0,4,u+5) if family==1 else (5,0,3,u+v+7))
                        checked += 1
        self.assertEqual(checked,440)

    def test_control_state_C_alone_is_not_a_return(self):
        for family in (1,3):
            seen,actual,expected = simulate(family,1,0,0,"101110101011",0)
            self.assertGreater(len(seen),1)
            self.assertEqual(seen[0][0],0)
            self.assertTrue(seen[0][1]) # The source is C with a nonblank left
            self.assertFalse(seen[-1][1])
            self.assertEqual(actual,expected)

    def test_M0_affine_clock_extrapolation_stays_retired(self):
        for family,actual in ((1,222),(3,256)):
            self.assertNotEqual(actual,clock(family,0,0,0))
            with self.assertRaises(ValueError):
                c_schedule(family,0,0,0)


if __name__ == "__main__":
    unittest.main()
