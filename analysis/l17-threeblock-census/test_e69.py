"""E69 five-phase raw-machine checkpoints, independent of Lean composition."""
import random
import unittest

OPS = (((1, 1, 1), (0, 1, 4)),
       ((1, -1, 2), (0, 1, 0)),
       ((0, -1, 3), (1, -1, 1)),
       ((1, -1, 0), (1, -1, 4)),
       ((0, -1, 1), (0, -1, 5)),
       ((1, -1, 3), None))
P, Q = '01', '10'
FAMILIES = {
  1: (88, 24, 77, '101001', '0111110101010101010110110',
      '010100100101010101010100101010'),
  3: (126, 26, 95, '101001001', '011111110101010101010110110',
      '01010010010101010101010101010101010'),
}

def encode(head, left, right):
    return frozenset([head - 1 - j for j, x in enumerate(left) if x == '1']
                     + [head + j for j, x in enumerate(right) if x == '1'])

def step(q, h, tape, count):
    tape = set(tape)
    for j in range(count):
        op = OPS[q][int(h in tape)]
        if op is None:
            raise AssertionError(('unexpected halt', j))
        bit, direction, q = op
        if bit:
            tape.add(h)
        else:
            tape.discard(h)
        h += direction
    return q, h, frozenset(tape)

def frame(family, m, u, v, R, origin):
    N, shift, bridge, X, W, Y = FAMILIES[family]
    left_tail = '0'+P*(v+7)+'0'+P*(u+6) if family == 1 else P*(v+6)+'0'+P*(u+6)
    full_left = X + left_tail
    left_post_bridge = P*(v+5)+'0'+P*(u+6) if family == 1 else P*(v+2)+'0'+P*(u+6)
    M = m+1
    states = []
    states.append((2, origin, full_left, W+Q*m+'111'+R))
    states.append((0, origin+shift+2*M, P*M+Y+left_tail, '11'+R))
    states.append((0, origin+shift, Y+left_tail, '11'+Q*M+R))
    if family == 1:
        states.append((0, origin+shift-35, left_post_bridge, '11100'+Q*16+Q*M+R))
        states.append((2, origin-len(full_left), '', '1'*(2*u+6)+P*5+P*(v+5)+'00'+Q*(16+M)+R))
        clocks = (N+2*M, 4*M, bridge, 4*(v+5)+29+2*u)
    else:
        states.append((2, origin+shift-43, left_post_bridge, '11'+P*21+'0'+Q*M+R))
        states.append((2, origin-len(full_left), '', '1'+'11'*u+Q*7+'1'*(2*(v+2))+P*21+'0'+Q*M+R))
        clocks = (N+2*M, 4*M, bridge, 2*((v+2)+1)+41+2*u)
    q, h, t = states[0][0], states[0][1], encode(states[0][1], *states[0][2:])
    for clock, (q2, h2, left2, right2) in zip(clocks, states[1:]):
        q, h, t = step(q, h, t, clock)
        assert (q, h, t) == (q2, h2, encode(h2, left2, right2)), (family, m, u, v, clock, q, q2, h, h2)
    return sum(clocks), h, states[-1][3]

class E69FullPhaseReplay(unittest.TestCase):
    def test_360_complete_four_segment_compositions(self):
        rng = random.Random(690169)
        checked = 0
        for family in (1, 3):
            for m in (*range(12), 15, 31, 63, 127, 200, 400):
                for u, v in ((0,0),(0,1),(1,0),(1,3),(3,1),
                             (5,7),(2,6),(4,3),(8,4),(3,9)):
                    R = ''.join(rng.choices('01', k=rng.randrange(56)))+'1'
                    origin = rng.randrange(-2000,2000)
                    clock, head, tape = frame(family, m, u, v, R, origin)
                    M=m+1
                    self.assertEqual(clock, (214 if family==1 else 268)+6*M+2*u+(4 if family==1 else 2)*v)
                    target = ('1'*(2*u+6)+P*(v+8)+'010100'+Q*(16+M)+R if family==1
                              else '1'*(2*u+1)+Q*7+'1'*(2*v+4)+P*(21+M)+'0'+R)
                    self.assertEqual(tape,target)
                    self.assertEqual(head, origin-(34+2*u+2*v))
                    checked += 1
        self.assertEqual(checked,360)

if __name__ == '__main__':
    unittest.main()
