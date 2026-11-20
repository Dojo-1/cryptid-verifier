"""Literal differential replay of L17's interleaved scanner and suffix witnesses."""
import argparse
from collections import Counter
from itertools import chain, product
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


K41_STRIP = "10101010101010"
ONE_PAIR_DOUBLE_GUARD = "1" + K41_STRIP + "11" + "010111"
ONE_PAIR_DOUBLE_WRITTEN = "0101010101010101011111101010101010101010"
NARROW_GUARDS = (
    ('zero', '0', '01010011111111111', 3, 104, True),
    ('ones', '111111', '0101010101010101010101010', 2, 192, False),
    ('one-plain', '110101010101010111', '0101001010101010101010101010101010', 3, 180, True),
    ('one-c6', '1101010101010100', '010101010101010101111111111111111', 3, 182, False),
    ('three-plain', '11110101010101010111', '010101010101010101010101010101010101010', 2, 234, False),
    ('three-c6', '111101010101010100', '01010101010101111111111111111111111111111', 0, 216, False),
)


def narrow_cases(rng):
    # Cover every checkpoint guard, both terminations, positive C6 repeats,
    # and the j=3 boundary where the sixth 1 comes from the K41 strip.
    for m, r, term, trial in product(range(7), range(9), ("00", "100"), range(8)):
        u, v = ((0, 0), (0, 1), (1, 0), (9, 6))[trial % 4]
        if trial >= 4:
            u, v = rng.randrange(22), rng.randrange(22)
        tail = "".join(rng.choices("01", k=rng.randrange(32))) + "1"
        h = r // 2
        pairs = "1" * (2 * (m + 5))
        if term == "00" and r == 0:
            cut, scanner = pairs + "1"*6, 4*m + 44
        elif term == "100" and r % 2:
            cut, scanner = pairs + "010" + "111010"*h + "1"*7, 4*m + 32*h + 72
        elif term == "00" and not r % 2:
            cut, scanner = pairs + "010" + "111010"*(h-1) + "1"*9, 4*m + 32*(h-1) + 76
        else:
            e = 4 if term == "100" else 6
            guard_tail = "1"*e if h == 0 else "010" + "111010"*(h-1) + "1"*(e+3)
            cut = ("0" + "10"*6 if m == 0 else "1"*(2*m-1) + K41_STRIP) + guard_tail
            scanner = 4*m + 32*h + (86 if term == "100" else 90)
        name, guard, written, remaining, fixed, via_a = next(
            row for row in NARROW_GUARDS if cut.startswith(row[1]))
        suffix = cut[len(guard):] + tail
        if via_a:
            out = "1"*(2*u+6) + "01"*5 + "01"*(v+remaining) + written + suffix
        else:
            out = "1"*(2*u+1) + K41_STRIP + "1"*(2*(v+remaining)) + written + suffix
        steps = 112 + scanner + fixed + 2*u + (4 if via_a else 2)*v
        offset = rng.randrange(-800, 801)
        left = "10"*(6+u) + "0" + "10"*(7+v) + "0" + "10" + "01"*5
        right = MIXED + "100" + "01"*m + "101"*r + term
        start = offset - len(left)
        req = dict(q=1, head=offset, limit=steps, ones=ones(left+right+tail, start))
        expected = dict(q=2, head=start, steps=steps, halted=False, ones=ones(out, start))
        yield f"mixed-width-five-{name}", req, expected, (start+1, offset+len(right)-1), True


def return_block(kind, j=0):
    """Forward tokens, return clock, and the output after the restored 111."""
    if kind == "pair":
        return ("01",), 2, "11"
    if kind == "double":
        return ("101", "101"), 6, "010111"
    if kind == "bridge":
        return ("101", "01", "01", "01", "101"), 34, "011010101010"
    if kind == "short-two":
        return (("101", "01", "101") + ("01",)*j + ("101", "01", "01", "101"),
                48+4*j, "01"+"10"*(j+8))
    return ("01",)*(j+5) + ("101",), 41+2*(j+1), (
        "0"+"10"*6 if j == 0 else "1"*(2*j-1) + K41_STRIP)


def block_cases(rng):
    pair, double, bridge = (return_block(k) for k in ("pair", "double", "bridge"))
    kinds = (pair, double, bridge, *(return_block("wide", j) for j in range(5)))
    # All short lists of blocks with an obligatory bridge, plus long seeded chains.
    chains = [[bridge, *bs] for length in range(3) for bs in product(kinds[:5], repeat=length)]
    chains += [[bridge, *rng.choices(kinds, k=rng.randrange(3, 8))] for _ in range(49)]
    # Retain the original campaign, then add chains anchored by the new bridge.
    original = product(chains, ("00", "100"), ("B", "mixed"))
    new_kinds = (*kinds, *(return_block("short-two", j) for j in (0, 1, 3, 7)))
    new_chains = [[return_block("short-two", j), *rng.choices(new_kinds, k=i % 4)]
                  for j, i in product((0, 1, 2, 7, 17), range(8))]
    additional = product(new_chains, ("00", "100"), ("short-two-B", "short-two-mixed", "width-five"))
    for blocks0, term, mode in chain(original, additional):
        mixed = mode not in ("B", "short-two-B")
        narrow = mode == "width-five"
        # The first bridge can absorb the 100 stop's implicit 101 deposit.
        blocks = blocks0 + ([pair]*5 if mixed else [])
        tokens = [t for spec in reversed(blocks) for t in spec[0]]
        if term == "100":
            assert tokens.pop() == "101"
        if mixed:
            assert tokens[:5] == ["01"]*5
            del tokens[:5]
        u, v = rng.randrange(19), rng.randrange(19)
        k = -1 if narrow else rng.randrange(7)
        tail = "".join(rng.choices("01", k=rng.randrange(1, 32))) + "1"
        residue = "".join(b[2] for b in reversed(blocks)) + "1"*(6 if term == "00" else 4)
        clock_to_cut = (136 if mixed else 14) + sum(CLOCK[t] for t in tokens) + (
            10 if term == "00" else 19) + sum(b[1] for b in blocks)
        middle_clock = {-1: 192, 0: 104, 1: 120, 2: 100}.get(k, 2*k+96)
        steps = clock_to_cut + middle_clock + 2*u + 2*v
        if narrow:
            assert residue.startswith("1"*10)
            out = "1"*(2*u+1) + K41_STRIP + "1"*(2*(v+2)) + "01"*12 + "0"
            residue = residue[6:]
        elif k == 0:
            out = "1"*(2*u+1) + K41_STRIP + "1"*(2*v+5) + "10"*10
        elif k == 1:
            out = "1"*(2*u+1) + K41_STRIP + "1"*(2*v+1) + "10101010101010011010101010"
        elif k == 2:
            out = "1"*(2*u+1) + K41_STRIP + "1"*(2*v+11) + "10"*9
        else:
            out = "1"*(2*u+1) + K41_STRIP + "1"*(2*v+11) + "1010" + "1"*(2*k-4) + K41_STRIP
        left = "10"*(6+u) + "0" + "10"*(7+v) + "0" + "10" + "01"*(k+5+mixed)
        right = (MIXED+"100" if mixed else "1101") + "".join(tokens) + term
        offset = rng.randrange(-800, 801)
        start = offset-len(left)
        req = dict(q=1, head=offset, limit=steps, ones=ones(left+right+tail, start))
        want = dict(q=2, head=start, steps=steps, halted=False, ones=ones(out+residue+tail, start))
        yield f"blocks-{mode}-{term}", req, want, (start+1, offset+len(right)-1), True


def bridge_cases(rng):
    deposited = "010101010010"
    written = "111011010101010"
    for _ in range(80):
        l = "".join(rng.choices("01", k=rng.randrange(0, 40)))
        r = "".join(rng.choices("01", k=rng.randrange(0, 40)))
        head = rng.randrange(-800, 801)
        start = head+1-len(deposited)-len(l)
        source = l + deposited[::-1] + "111" + r
        req = dict(q=2, head=head, limit=34, ones=ones(source, start))
        want = dict(q=2, head=head-len(deposited), steps=34, halted=False,
                    ones=ones(l+written+r, start))
        yield "bridge-window", req, want, (head+1-len(deposited), head+3), False


def short_two_cases(rng):
    for j, _ in product((0, 1, 2, 3, 8, 16, 60, 200), range(10)):
        left = "".join(rng.choices("01", k=rng.randrange(0, 40)))
        right = "".join(rng.choices("01", k=rng.randrange(0, 40)))
        deposited = "010" + "10"*2 + "010" + "10"*j + "010" + "10" + "010"
        written = "11101" + "10"*(j+8)
        head = rng.randrange(-800, 801)
        start = head+1-len(deposited)-len(left)
        req = dict(q=2, head=head, limit=48+4*j,
                   ones=ones(left+deposited[::-1]+"111"+right, start))
        want = dict(q=2, head=head-len(deposited), steps=48+4*j, halted=False,
                    ones=ones(left+written+right, start))
        yield "short-two-window", req, want, (head+1-len(deposited), head+3), False


def two_wide_cases(rng):
    for outer, term, trial in product((1, 2), ("00", "100"), range(24)):
        u, v = (0, 0) if trial == 0 else (rng.randrange(24), rng.randrange(24))
        tail = "".join(rng.choices("01", k=rng.randrange(24))) + "1"
        first = "01"*outer + "101"
        second = "01"*6 + ("101" if term == "00" else "")
        right = MIXED + "100" + first + second + term
        seed_left = 3 if term == "00" else 1
        scanner = 2*(outer+6) + (26 if term == "00" else 13)
        block_clock = 45 + (43+2*outer)
        term_clock = 10 if term == "00" else 19
        if outer == 1:
            cut_clock, middle = 258, v+3
            strip = "01010101010101010111111010101010101010101010101010"
        else:
            cut_clock, middle = 292, v
            strip = "0101010101010111111111111111111010101010101010101010101010"
        out = "1"*(2*u+1) + K41_STRIP + "1"*(2*middle) + strip + "1"*seed_left + tail
        steps = 136 + scanner + term_clock + block_clock + cut_clock + 2*u + 2*v
        left = "10"*(6+u) + "0" + "10"*(7+v) + "0" + "10" + "01"*5
        offset = rng.randrange(-800, 801)
        start = offset-len(left)
        req = dict(q=1, head=offset, limit=steps, ones=ones(left+right+tail, start))
        want = dict(q=2, head=start, steps=steps, halted=False, ones=ones(out, start))
        yield f"blocks-width-five-two-wide-{outer}-{term}", req, want, (start+1, offset+len(right)-1), True


def one_pair_double_mixed_cases(rng):
    """The formerly uncovered three-block residue, both scanner stops.

    Check exact first blank-left C return, full tape, clock, read bounds,
    translated heads and variable exterior suffixes against raw Python/C++.
    """
    blocks = [return_block("double"), return_block("pair"), return_block("wide", 1)]
    all_tokens = [t for spec in reversed(blocks) for t in spec[0]]
    assert all_tokens[:5] == ["01"] * 5
    for term, trial in product(("00", "100"), range(80)):
        tokens = all_tokens[5:].copy()
        if term == "100":
            assert tokens.pop() == "101"
        u, v = ((0, 0), (1, 0), (0, 1), (7, 11))[trial % 4]
        if trial >= 4:
            u, v = rng.randrange(22), rng.randrange(22)
        tail = "".join(rng.choices("01", k=rng.randrange(0, 40))) + "1"
        residue = "".join(b[2] for b in reversed(blocks)) + "1" * (6 if term == "00" else 4)
        assert residue.startswith(ONE_PAIR_DOUBLE_GUARD)
        rest = residue[len(ONE_PAIR_DOUBLE_GUARD):]
        left = "10"*(u+6) + "0" + "10"*(v+7) + "0" + "10" + "01"*5
        right = MIXED + "100" + "".join(tokens) + term
        offset = rng.randrange(-800, 801)
        start = offset - len(left)
        steps = (136 + sum(CLOCK[t] for t in tokens) + (10 if term == "00" else 19)
                 + sum(b[1] for b in blocks) + 228 + 2*u + 2*v)
        out = ("1" + "11"*u + K41_STRIP + "1"*(2*(v+3)) +
               ONE_PAIR_DOUBLE_WRITTEN + rest + tail)
        req = dict(q=1, head=offset, limit=steps, ones=ones(left+right+tail, start))
        want = dict(q=2, head=start, steps=steps, halted=False, ones=ones(out, start))
        yield "mixed-one-pair-double-" + term, req, want, (start+1, offset+len(right)-1), True



def extra_widewide_cases(rng):
    """Full mixed returns for the two zero-headed inner wide-wide guards."""
    families = (
        (1, "1101010101010101101010101010100", "010101010101010101101010101010101111111111111111", 252, 3),
        (2, "111101010101010101101010101010100", "01010101010101111111111111101010101010101111111111111111", 286, 0),
    )
    for outer, guard, written, cut_clock, middle in families:
        for first_kind, j in (("double", 0), ("bridge", 0), ("wide", 0),
                              *(("short-two", k) for k in range(4))):
            first = return_block(first_kind, j)
            blocks = [first, return_block("wide", 1), return_block("wide", outer)]
            for term in ("00", "100"):
                tokens = [t for b in reversed(blocks) for t in b[0]]
                assert tokens[:5] == ["01"] * 5
                del tokens[:5]
                if term == "100":
                    assert tokens.pop() == "101"
                for trial in range(5):
                    u, v = ((0, 0), (1, 0), (0, 1), (5, 9), (11, 4))[trial]
                    tail = "".join(rng.choices("01", k=rng.randrange(0, 40))) + "1"
                    residue = "".join(b[2] for b in reversed(blocks)) + "1" * (6 if term == "00" else 4)
                    assert residue.startswith(guard), (outer, first_kind, j, term)
                    rest = residue[len(guard):]
                    left = "10"*(6+u) + "0" + "10"*(7+v) + "0" + "10" + "01"*5
                    right = MIXED + "100" + "".join(tokens) + term
                    offset = rng.randrange(-800, 801)
                    start = offset-len(left)
                    clock = (136 + sum(CLOCK[t] for t in tokens)
                             + (10 if term == "00" else 19)
                             + sum(b[1] for b in blocks) + cut_clock + 2*u + 2*v)
                    out = ("1"*(2*u+1) + K41_STRIP + "1"*(2*(v+middle))
                           + written + rest + tail)
                    req = dict(q=1, head=offset, limit=clock, ones=ones(left+right+tail, start))
                    want = dict(q=2, head=start, steps=clock, halted=False, ones=ones(out, start))
                    yield f"mixed-widewide-{outer}-{first_kind}{j}-{term}", req, want, (
                        start+1, offset+len(right)-1), True


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
    cases = [*scan_cases(rng), *witness_cases(rng), *mixed_00_cases(rng), *transport_cases(rng),
             *narrow_cases(rng), *block_cases(rng), *bridge_cases(rng), *short_two_cases(rng), *two_wide_cases(rng),
             *one_pair_double_mixed_cases(rng), *extra_widewide_cases(rng)]
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
