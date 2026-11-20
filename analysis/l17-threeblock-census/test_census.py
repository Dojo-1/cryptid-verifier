"""Reproducible finite L17 three-block census and contextual falsification tests.

The grammar is explicitly bounded at wide j=0..3 and shortTwo j=0..3.
This module deliberately does not infer blank-orbit reachability or nonhalting.
"""
from collections import Counter
from importlib.util import module_from_spec, spec_from_file_location
from itertools import product
from pathlib import Path
from random import Random
import re
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = spec_from_file_location("l17_interleaved_checker", ROOT / "analysis/l17-interleaved/check.py")
l17 = module_from_spec(spec)
spec.loader.exec_module(l17)
OPS = l17.OPS

KINDS = (("pair", 0), ("double", 0), ("bridge", 0),
         *(("wide", j) for j in range(4)),
         *(("short-two", j) for j in range(4)))
NEW = {"oneWideWide", "threeWideWide"}  # E59 introduced these
E62 = {"threePairDouble"}             # later guard, excluded from historical E59 counts
E63 = {"oneTripleWide", "threeTripleWide"} # two new exact candidate guards
CLOCK = {
    "zero": 104, "ones": 192, "onePlain": 180, "oneC6": 182,
    "threePlain": 234, "threeC6": 216, "oneTwoWide": 258,
    "threeTwoWide": 292, "onePairDouble": 228,
    "oneWideWide": 252, "threeWideWide": 286, "threePairDouble": 262,
    "oneTripleWide": 328, "threeTripleWide": 362,
}
KERNELS = {
    "oneWideWide": {
        "left": "101010100100101",
        "word": "1101010101010101101010101010100",
        "written": "010101010101010101101010101010101111111111111111",
        "steps": 203, "read": (-14, 34),
    },
    "threeWideWide": {
        "left": "101010101010100100101",
        "word": "111101010101010101101010101010100",
        "written": "01010101010101111111111111101010101010101111111111111111",
        "steps": 243, "read": (-20, 36),
    },
}


def lean_words():
    text = (ROOT / "link/CryptidLink/L17FiveRun.lean").read_text(encoding="utf-8")
    section = text.split("def WidthFourGuard.word :", 1)[1].split(
        "def WidthFourGuard.clock", 1)[0]
    words = {}
    for line in section.splitlines():
        match = re.match(r"\s*\|\s*\.(\w+)\s*=>\s*\[([0-9, ]+)\]\s*$", line)
        if match:
            words[match.group(1)] = "".join(x.strip() for x in match.group(2).split(","))
    return words


def parser_cases():
    for blocks in product(KINDS, repeat=3):
        specs = [l17.return_block(kind, j) for kind, j in blocks]
        tokens = tuple(t for spec in reversed(specs) for t in spec[0])
        if tokens[:5] != ("01",) * 5:
            continue
        for term in ("00", "100"):
            if term == "100" and tokens[-1] != "101":
                continue
            fixed = "".join(spec[2] for spec in reversed(specs))
            fixed += "1" * (6 if term == "00" else 4)
            yield blocks, specs, term, tokens, fixed


def classify(fixed, words):
    hits = [name for name, word in words.items() if fixed.startswith(word)]
    if len(hits) > 1:
        raise AssertionError(("non-disjoint guards", hits, fixed))
    return hits[0] if hits else None


def initial(blocks, specs, term, tokens, fixed, u=0, v=0,
            suffix="1010011101", offset=0, mode="C"):
    if mode == "C":
        left = "10"*(6+u) + "0" + "10"*(7+v) + "0" + "10" + "01"*2
        right = "0111" + fixed + suffix
        state = 2
    else:
        left = "10"*(6+u) + "0" + "10"*(7+v) + "0" + "10" + "01"*5
        scanned = list(tokens[5:])
        if term == "100":
            assert scanned.pop() == "101"
        right = l17.MIXED + "100" + "".join(scanned) + term + suffix
        state = 1
    word = left + right
    return word, offset-len(left), offset, state


def first_return(config, limit=14000):
    word, start, head, state = config
    cells = {start+i for i, bit in enumerate(word) if bit == "1"}
    lo, hi = None, None
    for t in range(limit+1):
        if state == 2 and not any(p < head for p in cells):
            return {"kind":"C", "steps":t, "head":head,
                    "tape":tuple(sorted(p-head for p in cells)),
                    "read":(lo, hi)}
        if t >= limit:
            break
        op = OPS[state][int(head in cells)]
        if op is None:
            return {"kind":"halt", "steps":t}
        if lo is None: lo, hi = head, head
        lo = min(lo, head)
        hi = max(hi, head)
        val, direction, state = op
        if val: cells.add(head)
        else: cells.discard(head)
        head += direction
    return {"kind":"cap", "steps":limit}


def exact_local(word, head, count):
    cells = {i for i, bit in enumerate(word) if bit == "1"}
    q = 2
    touched = []
    for n in range(count):
        touched.append(head)
        op = OPS[q][int(head in cells)]
        if op is None:
            return {"kind":"halt", "step":n}
        val, direction, q = op
        if val: cells.add(head)
        else: cells.discard(head)
        head += direction
    return {"kind":"exact", "q":q, "head":head, "cells":cells,
            "window":(min(touched),max(touched))}


def b_clock(specs, term, tokens, cut_clock):
    actual = list(tokens[5:])
    if term == "100":
        assert actual.pop() == "101"
    return (136 + sum(l17.CLOCK[t] for t in actual)
            + (10 if term == "00" else 19)
            + sum(s[1] for s in specs) + cut_clock)


class ThreeBlockCensusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.words = lean_words()
        cls.cases = list(parser_cases())

    def test_lean_guard_mirror_and_census(self):
        self.assertEqual(set(self.words), set(CLOCK))
        self.assertEqual(self.words["oneWideWide"], KERNELS["oneWideWide"]["word"])
        self.assertEqual(self.words["threeWideWide"], KERNELS["threeWideWide"]["word"])
        self.assertEqual(len(self.cases), 1016)
        base = {name:w for name,w in self.words.items() if name not in NEW | E62 | E63}
        e59 = {name:w for name,w in self.words.items() if name not in E62 | E63}
        e62 = {name:w for name,w in self.words.items() if name not in E63}
        before = [classify(c[4], base) for c in self.cases]
        e59_after = [classify(c[4], e59) for c in self.cases]
        e62_after = [classify(c[4], e62) for c in self.cases]
        after = [classify(c[4], self.words) for c in self.cases]
        self.assertEqual(Counter(before)[None], 54)
        self.assertEqual(Counter(e59_after)[None], 26)  # preserve E59 baseline
        self.assertEqual(Counter(e62_after)[None], 24)  # preserve E62 baseline
        self.assertEqual(Counter(after)[None], 20)     # E63 closes four
        self.assertEqual(Counter(after)["oneWideWide"], 14)
        self.assertEqual(Counter(after)["threeWideWide"], 14)
        self.assertEqual(Counter(after)["threePairDouble"], 2)
        self.assertEqual(Counter(after)["oneTripleWide"], 2)
        self.assertEqual(Counter(after)["threeTripleWide"], 2)
        self.assertEqual(Counter(after)["onePairDouble"], 2)

    def test_all_baseline_guards_against_literal_clock(self):
        for blocks, specs, term, tokens, fixed in self.cases:
            g = classify(fixed, self.words)
            actual = first_return(initial(blocks,specs,term,tokens,fixed))
            self.assertEqual(actual["kind"], "C")
            if g is not None:
                self.assertEqual(actual["steps"], CLOCK[g], (blocks,term,g))

    def test_54_previous_gaps_paired_b_and_c_with_context(self):
        base = {name:w for name,w in self.words.items() if name not in NEW | E62 | E63}
        slope_counts = Counter()
        checked = 0
        for blocks, specs, term, tokens, fixed in self.cases:
            if classify(fixed, base) is not None:
                continue
            c00 = first_return(initial(blocks,specs,term,tokens,fixed))
            d_u = first_return(initial(blocks,specs,term,tokens,fixed,u=1))["steps"]-c00["steps"]
            d_v = first_return(initial(blocks,specs,term,tokens,fixed,v=1))["steps"]-c00["steps"]
            slope_counts[(d_u,d_v)] += 1
            for u,v,tail,offset in ((0,0,"0"*17,0),(0,0,"1"*17,150),
                                    (1,3,"10010101001110010110101",-71),
                                    (3,1,"010010110101110101001",999)):
                ck = first_return(initial(blocks,specs,term,tokens,fixed,u,v,tail,offset,"C"))
                bb = first_return(initial(blocks,specs,term,tokens,fixed,u,v,tail,offset,"B"))
                want_ck = c00["steps"] + d_u*u + d_v*v
                self.assertEqual((ck["kind"], ck["steps"]),("C", want_ck))
                self.assertEqual((bb["kind"], bb["steps"]),
                                 ("C", b_clock(specs,term,tokens,want_ck)))
                self.assertEqual(ck["tape"], bb["tape"])
                checked += 1
        self.assertEqual(checked,216)
        self.assertEqual(slope_counts,Counter({(2,2):44,(2,4):10}))

    def test_arbitrary_exteriors_and_guard_flip_controls(self):
        rng = Random(595921)
        for name,k in KERNELS.items():
            core,guard,written=k["left"],k["word"],k["written"]
            self.assertEqual(len(core)+4+len(guard),2+len(written))
            for trial in range(140):
                left = "".join(rng.choices("01",k=trial%31))
                right = "".join(rng.choices("01",k=(trial*7)%37))
                entry=left+core+"0111"+guard+right
                r=exact_local(entry,len(left+core),k["steps"])
                want={i for i,bit in enumerate(left+"11"+written+right) if bit=="1"}
                self.assertEqual((r["kind"],r["q"],r["head"]),
                                 ("exact",2,len(left)))
                self.assertEqual(r["window"],(len(left+core)+k["read"][0],
                                               len(left+core)+k["read"][1]))
                self.assertEqual(r["cells"],want)
            left="100110";right="10100111001011101101"
            source=left+core+"0111"+guard+right
            baseline=exact_local(source,len(left+core),k["steps"])
            for i,bit in enumerate(guard):
                mutated=guard[:i]+("1" if bit=="0" else "0")+guard[i+1:]
                candidate=exact_local(left+core+"0111"+mutated+right,
                                      len(left+core),k["steps"])
                self.assertNotEqual(candidate,baseline)

if __name__ == "__main__":
    unittest.main()
