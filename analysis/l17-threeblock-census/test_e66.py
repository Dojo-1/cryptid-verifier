"""E66 raw six-state regression for the exact A two-ones pair sweep.

The table is transcribed independently. These are finite tests, not a
substitute for the Lean induction or an E60 C-to-C return proof.
"""
import random
import unittest

OPS = (((1, 1, 1), (0, 1, 4)),
       ((1, -1, 2), (0, 1, 0)),
       ((0, -1, 3), (1, -1, 1)),
       ((1, -1, 0), (1, -1, 4)),
       ((0, -1, 1), (0, -1, 5)),
       ((1, -1, 3), None))


def run(word, head, origin, steps):
    tape = {origin + i for i, bit in enumerate(word) if bit == "1"}
    state = 0
    visits = []
    for clock in range(steps):
        visits.append(head)
        move = OPS[state][int(head in tape)]
        if move is None:
            raise AssertionError(("unexpected halt", clock))
        bit, direction, state = move
        if bit:
            tape.add(head)
        else:
            tape.discard(head)
        head += direction
    return state, head, frozenset(tape), (
        (min(visits), max(visits)) if visits else None
    )


def bits(word, origin):
    return frozenset(origin + i for i, char in enumerate(word) if char == "1")


class ExactTwoOnesSweep(unittest.TestCase):
    def test_1320_contextual_sweeps(self):
        rng = random.Random(6601)
        cases = 0
        widths = (*range(41), 100, 200, 500)
        for n in widths:
            for _ in range(30):
                left = "".join(rng.choices("01", k=rng.randrange(51)))
                right = "".join(rng.choices("01", k=rng.randrange(52)))
                origin = rng.randint(-1700, 1700)
                initial = left + "10" * n + "11" + right
                final = left + "11" + "10" * n + right
                state, head, written, reads = run(
                    initial, origin + len(left) + 2 * n, origin, 4 * n
                )
                self.assertEqual((state, head), (0, origin + len(left)))
                self.assertEqual(written, bits(final, origin))
                if n:
                    self.assertEqual(
                        reads,
                        (origin + len(left) + 1, origin + len(left) + 2*n + 1)
                    )
                else:
                    self.assertIsNone(reads)
                cases += 1
        self.assertEqual(cases, 1320)

    def test_wrong_guard_is_not_admitted(self):
        left, right = "1010110", "010010011"
        start = len(left) + 2
        source = left + "10" + "10" + right
        result = run(source, start, 0, 4)
        claimed = bits(left + "11" + "10" + right, 0)
        self.assertNotEqual((result[0], result[1], result[2]),
                            (0, len(left), claimed))


if __name__ == "__main__":
    unittest.main()
