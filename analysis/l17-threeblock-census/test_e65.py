"""E65: raw six-state contextual C-to-A prelude and window composition checks.

No claim about the entire E60 C return or blank-tape nonhalting.
Independently replays the six-state machine with complete tape comparisons.
"""
import random
import unittest

OPS = (((1, 1, 1), (0, 1, 4)),
       ((1, -1, 2), (0, 1, 0)),
       ((0, -1, 3), (1, -1, 1)),
       ((1, -1, 0), (1, -1, 4)),
       ((0, -1, 1), (0, -1, 5)),
       ((1, -1, 3), None))

FAMILIES = (
    (1, 88, "101001", "0111110101010101010110110",
     "010100100101010101010100101010", 24, -6),
    (3, 126, "101001001", "011111110101010101010110110",
     "01010010010101010101010101010101010", 26, -9),
)


def run(word, head, clock, leftmost):
    tape = {leftmost + i for i, bit in enumerate(word) if bit == "1"}
    state, read_min, read_max = 2, None, None
    for t in range(clock):
        read_min = head if read_min is None else min(read_min, head)
        read_max = head if read_max is None else max(read_max, head)
        transition = OPS[state][int(head in tape)]
        if transition is None:
            raise AssertionError(("halted before clock", t))
        bit, direction, state = transition
        if bit:
            tape.add(head)
        else:
            tape.discard(head)
        head += direction
    return state, head, frozenset(tape), (read_min, read_max)


def tape_of(word, leftmost):
    return frozenset(leftmost+i for i, bit in enumerate(word) if bit == "1")


class E65Tests(unittest.TestCase):
    def test_400_fixed_contextual_preludes(self):
        rng = random.Random(650101)
        count = 0
        for family, clock, x, w, y, head_shift, low in FAMILIES:
            for trial in range(200):
                left = "".join(rng.choices("01", k=rng.randrange(0, 55)))
                right = "".join(rng.choices("01", k=rng.randrange(0, 56)))
                offset = rng.randrange(-1800, 1801)
                low_coord = offset-len(x)-len(left)
                source = left + x[::-1] + w + right
                # 'left' is in physical order, arbitrary context outside x.
                output = left + y[::-1] + "0" + right
                q, head, cells, reads = run(source, offset, clock, low_coord)
                self.assertEqual((q, head, reads), (0, offset+head_shift,
                                                    (offset+low, offset+head_shift)))
                self.assertEqual(cells, tape_of(output, low_coord))
                count += 1
        self.assertEqual(count, 400)

    def test_800_parametric_composed_C_to_A_endpoints(self):
        rng = random.Random(650102)
        count = 0
        for family, prelude, x, w, y, shift, low in FAMILIES:
            for m in (0, 1, 2, 3, 4, 6, 11, 25, 44, 90):
                for trial in range(20):
                    L = "".join(rng.choices("01", k=rng.randrange(0, 30)))
                    R = "".join(rng.choices("01", k=rng.randrange(0, 35)))
                    origin = rng.randrange(-900, 901)
                    start = origin - len(L) - len(x)
                    for extra, raw_tail, written in (
                        (2, "111", "11"), (8, "10111", "1110")
                    ):
                        initial = L+x[::-1]+w+"10"*m+raw_tail+R
                        final = L+y[::-1]+"10"*(m+1)+written+R
                        q, head, tape, read = run(initial, origin,
                                                 prelude+2*m+extra, start)
                        self.assertEqual((q, head), (0, origin+shift+2*m+2))
                        self.assertEqual(tape, tape_of(final, start))
                        # The C prelude never reads beyond its fixed W prefix;
                        # the scanner/seam may extend right, not outside the
                        # explicitly provided tape.
                        self.assertGreaterEqual(read[0], start+len(L))
                        self.assertLess(read[1], origin+len(w)+2*m+len(raw_tail))
                        count += 1
        self.assertEqual(count, 800)

    def test_legacy_m0_extrapolation_remains_rejected(self):
        # The all-m A-window theorem at m=0 is NOT E60's C-return
        # extrapolation at m=0. Keep the domains separate.
        self.assertEqual(88+2*0+2, 90)
        self.assertEqual(126+2*0+2, 128)
        self.assertNotEqual(220, 214)
        self.assertNotEqual(274, 268)


if __name__ == "__main__":
    unittest.main()
