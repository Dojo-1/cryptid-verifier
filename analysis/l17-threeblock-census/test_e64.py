"""E64: independently transcribed exact A-scanner insertion diamond tests.

Finite checks only. These checks do not establish E60 C-checkpoint entry,
the global moving-frame transport, any first-return theorem, or nonhalting.
"""
import random
import unittest

OPS = (
    ((1, +1, 1), (0, +1, 4)),
    ((1, -1, 2), (0, +1, 0)),
    ((0, -1, 3), (1, -1, 1)),
    ((1, -1, 0), (1, -1, 4)),
    ((0, -1, 1), (0, -1, 5)),
    ((1, -1, 3), None),
)

def run_a(word, origin, steps):
    tape = {i for i, bit in enumerate(word) if bit == "1"}
    head, state = origin, 0
    reads = []
    for t in range(steps):
        reads.append(head)
        op = OPS[state][int(head in tape)]
        if op is None:
            raise AssertionError(("halted before target", t))
        bit, direction, state = op
        if bit:
            tape.add(head)
        else:
            tape.discard(head)
        head += direction
    return state, head, frozenset(tape), (min(reads), max(reads))


class E64ParametricScannerTests(unittest.TestCase):
    def test_both_contextual_scanner_branches(self):
        rng = random.Random(640164)
        total = 0
        for m in (0, 1, 2, 3, 4, 8, 16, 32, 80):
            for trial in range(30):
                left = "".join(rng.choices("01", k=rng.randrange(48)))
                right = "".join(rng.choices("01", k=rng.randrange(49)))
                n = len(left)
                prefix = "01" * m
                for suffix, extra, written in (
                    ("0111", 2, "11"),
                    ("010111", 8, "1110"),
                ):
                    input_word = left + prefix + suffix + right
                    out = run_a(input_word, n, 2 * m + extra)
                    expect_word = left + "10" * (m + 1) + written + right
                    expected = frozenset(i for i, bit in enumerate(expect_word) if bit == "1")
                    self.assertEqual(out[0], 0)
                    self.assertEqual(out[1], n + 2 * (m + 1))
                    self.assertEqual(out[2], expected)
                    self.assertGreaterEqual(out[3][0], n)
                    self.assertLess(out[3][1], n + 2*m + len(suffix))
                    total += 1
        self.assertEqual(total, 540)

    def test_two_paths_have_six_step_difference_and_distinct_residue(self):
        right = "010011101010111"
        for m in (0, 1, 3, 13, 47):
            left = "10010101101"
            short = run_a(left + "01"*m + "0111" + right, len(left), 2*m+2)
            long = run_a(left + "01"*m + "010111" + right, len(left), 2*m+8)
            self.assertEqual(long[1], short[1])
            self.assertNotEqual(short[2], long[2])
            self.assertEqual((2*m+8)-(2*m+2), 6)

if __name__ == "__main__":
    unittest.main()
