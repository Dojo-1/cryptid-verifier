"""E67: independent six-state exact-tape regression for two fixed bridges.

Finite tests cannot substitute for the contextual Lean theorem or prove
the global E60 first-return/nonhalting claims.
"""
import random
import unittest

OPS = (((1, 1, 1), (0, 1, 4)),
       ((1, -1, 2), (0, 1, 0)),
       ((0, -1, 3), (1, -1, 1)),
       ((1, -1, 0), (1, -1, 4)),
       ((0, -1, 1), (0, -1, 5)),
       ((1, -1, 3), None))

BRIDGES = (
    ("one", 77, "01010010010101010101010010101000101",
     "11100" + "10" * 16, 0, -34),
    ("three", 95, "0101001001010101010101010101010101001010101",
     "11" + "01" * 21 + "0", 2, -42),
)


def literal(q, h, tape, steps):
    tape = set(tape)
    seen = []
    for clock in range(steps):
        seen.append(h)
        op = OPS[q][int(h in tape)]
        if op is None:
            return ("halt", clock)
        bit, direction, q = op
        if bit:
            tape.add(h)
        else:
            tape.discard(h)
        h += direction
    return q, h, frozenset(tape), (min(seen), max(seen))


def ones(s, start):
    return frozenset(start + i for i, b in enumerate(s) if b == "1")


class E67FixedBridgeTests(unittest.TestCase):
    def test_800_arbitrary_context_bridges(self):
        rng = random.Random(67001)
        count = 0
        for name, clock, left_word, output, qwant, minread in BRIDGES:
            for trial in range(400):
                L = "".join(rng.choices("01", k=rng.randrange(70)))
                R = "".join(rng.choices("01", k=rng.randrange(71)))
                origin = rng.randint(-2000, 2000)
                start = origin-len(L)-len(left_word)
                src = L + left_word[::-1] + "11" + R
                dest = L + output + R
                actual = literal(0, origin, ones(src, start), clock)
                want = (qwant, origin-len(left_word), ones(dest, start),
                        (origin+minread, origin+1))
                self.assertEqual(actual, want, (name, trial))
                count += 1
        self.assertEqual(count, 800)

    def test_mutated_head_nearest_bit_blocks_both_bridges(self):
        for name, clock, word, output, qwant, _ in BRIDGES:
            L, R = "101001", "10010100010011"
            head = len(L) + len(word)
            original = literal(0, head, ones(L + word[::-1] + "11" + R, 0), clock)
            flip = ("0" if word[0] == "1" else "1") + word[1:]
            mutant = literal(0, head, ones(L + flip[::-1] + "11" + R, 0), clock)
            self.assertNotEqual(mutant[:3], original[:3], name)


if __name__ == "__main__":
    unittest.main()
