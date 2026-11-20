"""E60: finite, falsifiable full-tape return conjectures for moving windows.

This test intentionally does not claim a Lean proof, global stack coverage,
or nonhalting. Raw L17 transitions provide the computational oracle.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from random import Random
import unittest

PATH = Path(__file__).resolve().parent / "test_census.py"
spec = spec_from_file_location("l17_e60_census", PATH)
base = module_from_spec(spec)
spec.loader.exec_module(base)

K = "10" * 7
MS = (*range(1, 17), 19, 20, 25, 30, 40, 50, 75, 100, 200)
PARAMETERS = ((0, 0), (0, 1), (1, 0), (1, 3), (3, 1), (5, 7))


def guard(family, m):
    if family not in (1, 3) or m < 0:
        raise ValueError((family, m))
    return ("1" if family == 1 else "111") + K + "11" + "01" + "10" * m + "111"


def cut_clock(family, m, u, v):
    return (214 if family == 1 else 268) + 6 * m + 2 * u + (4 if family == 1 else 2) * v


def right_word(family, m, u, v, R):
    if family == 1:
        return "1" * (2 * u + 6) + "01" * (v + 8) + "010100" + "10" * (m + 16) + R
    return "1" * (2 * u + 1) + K + "1" * (2 * v + 4) + "01" * (21 + m) + "0" + R


def cut_source(family, m, u, v, R, offset):
    left = "10" * (u+6) + "0" + "10" * (v+7) + "0" + "10" + "01" * 2
    right = "0111" + guard(family, m) + R
    return left + right, offset - len(left), offset, 2


def expect_full_return(test, source, family, m, u, v, R):
    result = base.first_return(source, limit=12000)
    with test.subTest(family=family, m=m, u=u, v=v, R=R[:10]):
        test.assertEqual(result["kind"], "C")
        test.assertEqual(result["steps"], cut_clock(family, m, u, v))
        test.assertEqual(result["head"], source[1])
        expect = right_word(family, m, u, v, R)
        test.assertEqual(result["tape"], tuple(i for i, x in enumerate(expect) if x == "1"))
        test.assertEqual(result["read"], (source[2] - (33 + 2*u + 2*v),
                                         source[2] + (25 if family == 1 else 27) + 2*m))


class MovingWindowTests(unittest.TestCase):
    def test_full_tape_clocks_head_and_read_extrema(self):
        rng = Random(606060)
        checked = 0
        for family in (1, 3):
            for m in MS:
                for u, v in PARAMETERS:
                    R = "".join(rng.choices("01", k=rng.randrange(50))) + "1"
                    offset = rng.randrange(-2000, 2000)
                    source = cut_source(family, m, u, v, R, offset)
                    expect_full_return(self, source, family, m, u, v, R)
                    checked += 1
        self.assertEqual(checked, 300)

    def test_exact_output_transport_and_six_step_clock(self):
        for family in (1, 3):
            for m in range(1, 41):
                for u, v in ((0, 0), (1, 2)):
                    R = "010011101010111"
                    self.assertEqual(right_word(family, m+1, u, v, R),
                                     right_word(family, m, u, v, "") + "10" + R)
                    self.assertEqual(cut_clock(family, m+1, u, v) -
                                     cut_clock(family, m, u, v), 6)
                    self.assertEqual(len(guard(family, m+1))-len(guard(family, m)), 2)

    def test_zero_boundary_is_not_an_inductive_base(self):
        for family, actual_clock, bad_extension in ((1, 222, 214), (3, 256, 268)):
            for R in ("1", "1111", "1010010110101"):
                result = base.first_return(cut_source(family, 0, 0, 0, R, 0),
                                           limit=2000)
                self.assertEqual(result["kind"], "C")
                self.assertEqual(result["steps"], actual_clock)
                self.assertNotEqual(result["steps"], bad_extension)

    def test_real_scanner_parses_compose_with_checkpoint(self):
        cases = 0
        for outer in (1, 2):
            family = 1 if outer == 1 else 3
            for first in (("bridge", 0), ("short-two", 0),
                          ("short-two", 2), ("short-two", 20)):
                for term in ("00", "100"):
                    blocks = (first, ("pair", 0), ("wide", outer))
                    specs = [base.l17.return_block(name, j) for name, j in blocks]
                    tokens = [t for k in reversed(specs) for t in k[0]]
                    self.assertEqual(tokens[:5], ["01"] * 5)
                    scanned = tokens[5:]
                    if term == "100":
                        self.assertEqual(scanned.pop(), "101")
                    m = 5 if first[0] == "bridge" else 8 + first[1]
                    u, v = 1, 3
                    R = "01011101011101011"
                    source = base.initial(blocks, specs, term, tokens,
                        "", u, v, R, 159, mode="B")
                    result = base.first_return(source, limit=12000)
                    scanner_clock = sum(base.l17.CLOCK[t] for t in scanned)
                    block_clock = sum(k[1] for k in specs)
                    total = 136 + scanner_clock + (10 if term == "00" else 19) + block_clock
                    expected = right_word(family, m, u, v,
                            "1" * (3 if term == "00" else 1) + R)
                    self.assertEqual((result["kind"], result["steps"], result["head"]),
                                     ("C", total+cut_clock(family, m, u, v), source[1]))
                    self.assertEqual(result["tape"],
                            tuple(i for i, bit in enumerate(expected) if bit == "1"))
                    cases += 1
        self.assertEqual(cases, 16)


if __name__ == "__main__":
    unittest.main()
