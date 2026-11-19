"""Literal differential replay of L17's interleaved scanner and suffix witnesses."""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import random
import subprocess
import sys

sys.dont_write_bytecode = True
BASE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BASE / "l17-b-dispatch"))
from claims import MACHINE
from raw import OPS, replay

TOKENS = ("01", "101")
CLOCK = {"01": 2, "101": 13}
WRITE = {"01": "01", "101": "010"}  # spatial left-to-right
MIXED = "1101" + "101" + "01"
FIXED_LEFT = "10"*6 + "0" + "10"*7 + "0" + "10" + "01"*5
RETURN_CASES = (
    ("00", "", 110, "110101010101010111111111111010111111101011111111111"),
    ("100", "00", 348, "110101010101010111101010101010101010101010101111111111"),
    ("100", "11", 272, "110101010101010110101010101010011010101010101010101010"),
)


def ones(word, start):
    return [start+i for i, b in enumerate(word) if b == "1"]


def scan_cases(rng):
    # Exhaust every token list of length <= 5, then use long mixed lists.
    words = [w for k in range(6) for w in product(TOKENS, repeat=k)]
    words += [tuple(rng.choices(TOKENS, k=rng.randrange(6, 60))) for _ in range(65)]
    for entry, term, ts in product(("A", "B"), ("00", "100"), words):
        left = "".join(rng.choices("01", k=rng.randrange(30)))
        r = "".join(rng.choices("01", k=rng.randrange(30)))
        offset = rng.randrange(-800, 801)
        if entry == "A":
            header, source_left, fringe, steps = "", "0101010", left, 0
        else:
            header, source_left, fringe, steps = "1101", "0101", left + "0", 14
        right = header + "".join(ts) + term
        start = offset - len(left + source_left)
        out_left = fringe + "".join(WRITE[t] for t in ts)
        if term == "100":
            out_left += "010"
        nine = term == "00"
        steps += sum(CLOCK[t] for t in ts) + (10 if nine else 19)
        req = dict(q=int(entry == "B"), head=offset, limit=steps,
                   ones=ones(left+source_left+right+r, start))
        want = dict(q=2, head=start+len(out_left)-1, steps=steps, halted=False,
                    ones=ones(out_left+"1"*(9 if nine else 7)+r, start))
        yield f"scan-{entry}-{term}", req, want, (start, offset+len(right)-1), False


def witness_cases(rng):
    for _ in range(64):
        offset = rng.randrange(-800, 801)
        l = "".join(rng.choices("01", k=rng.randrange(25)))
        r = "".join(rng.choices("01", k=rng.randrange(25)))
        start = offset - len(l) - 5
        w = MIXED + "100"
        after = l + "01"*8 + "0"
        for b in ("0", "1"):
            req = dict(q=1, head=offset, limit=136, ones=ones(l+"10101"+w+b+r, start))
            want = dict(q=0, head=offset+12, steps=136, halted=False, ones=ones(after+b+r, start))
            yield "suffix-boundary", req, want, (offset-5, offset+11), False
            req = {**req, "limit": 137}
            want = dict(q=1 if b == "0" else 4, head=offset+13, steps=137,
                        halted=False, ones=ones(after+str(1-int(b))+r, start))
            yield f"suffix-branch-{b}", req, want, (offset-5, offset+12), False
        for term, guard, clock, result in RETURN_CASES:
            start = offset - len(FIXED_LEFT)
            right = MIXED + term + guard
            req = dict(q=1, head=offset, limit=clock, ones=ones(FIXED_LEFT+right+r, start))
            want = dict(q=2, head=start, steps=clock, halted=False, ones=ones(result+r, start))
            yield f"first-return-{term}-{guard}", req, want, (start+1, offset+len(right)-1), True


def transport_cases(rng):
    """Predict both sides from the old two-block clock and compare frames."""
    for n, m, r, term in product(range(6, 12), range(4), range(5), ("00", "100")):
        u, v = rng.randrange(20), rng.randrange(20)
        offset = rng.randrange(-800, 801)
        tail = "".join(rng.choices("01", k=rng.randrange(25)))
        rest = "01"*m + "101"*r + term
        inner = "10"*(6+u) + "0" + "10"*(7+v) + "0" + "10"
        left = inner + "01"*n
        alt = inner + "01"*(n-1)
        start = offset - len(left)
        k = n-6
        cut = 2*u + 2*v + {0: 104, 1: 120, 2: 100}.get(k, 2*k+96)
        if term == "100":
            base = 86 if r % 2 == 0 else 72
            virtual_clock = cut + 4*m + 32*(r//2) + base
        elif r == 0:
            virtual_clock = cut + 4*m + 44
        elif r % 2:
            virtual_clock = cut + 4*m + 32*(r//2) + 90
        else:
            virtual_clock = cut + 4*m + 32*(r//2-1) + 76
        right = MIXED + "100" + rest
        virtual = "1101" + "01"*5 + rest
        entries = (
            ("mixed", offset, left, right, 136, virtual_clock+112),
            ("virtual", offset-2, alt, virtual, 24, virtual_clock),
        )
        for name, head, prefix, word, ct, end in entries:
            req = dict(q=1, head=head, ones=ones(prefix+word+tail, start))
            boundary = {**req, "limit": ct}
            yield (name+"-frame", boundary, dict(q=0, head=offset+12, steps=ct, halted=False),
                   (start, offset+11), False)
            finish = {**req, "limit": end}
            yield (name+"-return", finish, dict(q=2, head=start, steps=end, halted=False),
                   (start+1, offset+len(right)-1), False)


def mixed_00_cases(rng):
    for k, _ in product(range(12), range(12)):
        u, v = rng.randrange(22), rng.randrange(22)
        offset = rng.randrange(-800, 801)
        tail = "".join(rng.choices("01", k=rng.randrange(24)))
        left = "10"*(6+u) + "0" + "10"*(7+v) + "0" + "10" + "01"*(5+k)
        right = MIXED + "00"
        start = offset-len(left)
        clock = 110+2*u+2*v+2*k
        out = "1"*(2*u+1) + "10"*7 + "1"*(2*v+11) + "1010" + "1"*(2*k+6) + "1010" + "1"*11
        req = dict(q=1, head=offset, limit=clock, ones=ones(left+right+tail, start))
        want = dict(q=2, head=start, steps=clock, halted=False, ones=ones(out+tail, start))
        yield "mixed-00-all-widths", req, want, (start+1, offset+len(right)-1), True


def check_first_return(req, trace):
    tape = set(req["ones"])
    for q, head, bit in trace:
        assert q != 2 or any(i < head for i in tape), ("earlier blank-left C", req, head)
        value, _, _ = OPS[q][bit]
        (tape.add if value else tape.discard)(head)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cpp", required=True, type=Path)
    exe = parser.parse_args().cpp.resolve()
    rng = random.Random(19112049)
    cases = [*scan_cases(rng), *witness_cases(rng), *mixed_00_cases(rng), *transport_cases(rng)]
    lines = []
    for i, (_, req, _, _, _) in enumerate(cases):
        bits = req["ones"]
        lines.append(" ".join(map(str, [i, MACHINE, req["q"], req["head"], req["limit"], 1, len(bits), *bits])))
    output = subprocess.run([str(exe)], input="\n".join(lines)+"\n", text=True,
                            capture_output=True, check=True).stdout.splitlines()
    counts = Counter()
    mixed_frames = {}
    for i, ((name, req, want, bounds, first), raw) in enumerate(zip(cases, output, strict=True)):
        cpp, py = json.loads(raw), replay(req)
        assert cpp.pop("id") == i
        assert cpp == py, (name, i, "literal trace disagreement")
        assert {k: py[k] for k in want} == want, (name, i, "endpoint disagreement")
        assert bounds[0] <= py["read_min"] <= py["read_max"] <= bounds[1]
        if name in ("mixed-frame", "mixed-return"):
            mixed_frames[name.removeprefix("mixed-")] = py["ones"]
        elif name in ("virtual-frame", "virtual-return"):
            assert py["ones"] == mixed_frames.pop(name.removeprefix("virtual-")), (name, i, "transport mismatch")
        if first:
            check_first_return(req, py["reads"])
        counts[name] += 1
    assert not mixed_frames
    print(json.dumps(dict(cases=len(cases), full_traces=len(cases), by_kind=counts), sort_keys=True))


if __name__ == "__main__":
    main()
