"""Compare scanner return formulas with the literal C++ and Python machines."""
from collections import Counter
from itertools import product
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile

BASE = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(BASE / "l17-b-dispatch"))
from claims import MACHINE
from raw import replay

SEED = 19112042


def ones(word, start):
    return [start + i for i, b in enumerate(word) if b == "1"]


def cases():
    rng = random.Random(SEED)
    groups = [*product(("B", "C2", "C5"), ("even-100", "odd-00")),
              *product(("B", "C2", "C5"), ("odd-100", "positive-even-00")),
              *product(("B", "C2", "C5"), ("prefixed-00", "prefixed-odd-100",
                       "prefixed-positive-even-00", "wide-even-100", "wide-odd-00"))]
    for entry, kind in groups:
        small = product((6, 7, 13), (7, 8, 16), range(6), range(4))
        large = ((rng.randrange(6, 270), rng.randrange(7, 270),
                  rng.randrange(40), rng.randrange(85)) for _ in range(84))
        for index, (p, c, h, j) in enumerate(list(small) + list(large)):
            offset = rng.randrange(-1000, 1001)
            r = "".join(rng.choice("01") for _ in range(rng.randrange(42)))
            tokens = index // 4 % 35 if kind.startswith(("prefixed-", "wide-")) else 0
            if kind.startswith("wide-"):
                tokens += 5
            family = kind.removeprefix("prefixed-").removeprefix("wide-")
            add, end = {
                "00": (0, "00"),
                "even-100": (0, "100"),
                "odd-00": (1, "00"),
                "odd-100": (1, "100"),
                "positive-even-00": (2, "00"),
            }[family]
            repeats = 0 if family == "00" else 2*h + add
            t = "1101" + "01"*tokens + "101"*repeats + end
            base = "10"*p + "0" + "10"*c + "0"
            if entry == "B":
                n, q, prefix, overhead, left = 5 + j, 1, "", 0, base + "10" + "01"*(5+j)
            else:
                width, cap, n0, cost = (2, 2, 5, 38) if entry == "C2" else (5, 3, 9, 62)
                n, q = n0+j, 2
                prefix, overhead = "0111" + "10"*j, cost + 2*j
                left = (base + "10"*cap + "0" + "10"*width)[:-1]
            start = offset - len(left)
            outer = "1"*(2*p-11) + "10"*7
            e = 9 if end == "00" else 7
            if kind in ("even-100", "odd-00"):
                phase = "1"*(2*c-3) + "1010" + "1"*(2*n-4) + "1010"
                clock = 2*p + 2*c + 2*n + 66 + 4*(end == "00")
            else:
                phase, clock0 = {
                    5: ("1"*(2*c-9) + "10"*10, 128),
                    6: ("1"*(2*c-13) + "10101010101010011010101010", 144),
                    7: ("1"*(2*c-3) + "10"*9, 124),
                }.get(n, (
                    "1"*(2*c-3) + "1010" + "1"*(2*n-14) + "10"*7,
                    2*(n-8) + 126,
                ))
                clock = 2*(p-6) + 2*(c-7) + clock0
            c6 = "111010"*h + "1"*e
            if family == "00":
                suffix = "1"*(2*tokens+6)
            elif kind.startswith("wide-"):
                shifted = "1"*(2*tokens-8) + "10"*7 + c6[3:]
                assert shifted.startswith("111")
                suffix = shifted[3:]
                clock += 42 if end == "100" else 46
            elif family in ("odd-100", "positive-even-00"):
                suffix = "1"*(2*tokens) + "010" + c6
                clock += 32 if end == "00" else 28
            else:
                suffix = c6
            target = outer + phase + suffix + r
            clock += overhead + 4*tokens + (0 if family == "00" else 32*h)
            req = dict(q=q, head=offset, limit=clock, ones=ones(left+prefix+t+r, start))
            want = dict(q=2, head=start, steps=clock, halted=False, ones=ones(target, start))
            yield (entry, kind), req, want, offset + len(prefix+t) - 1


def main():
    batch = list(cases())
    rows = []
    for i, (_, req, _, _) in enumerate(batch):
        n = req["limit"]
        fields = [i, MACHINE, req["q"], req["head"], n, int(n <= 1000), len(req["ones"]), *req["ones"]]
        rows.append(" ".join(map(str, fields)))
    with tempfile.TemporaryDirectory(prefix="l17-scanner-") as tmp:
        exe = Path(tmp) / "literal"
        subprocess.run(["c++", "-std=c++17", "-O2", str(BASE/"l17-hardening"/"raw_comparator.cpp"),
                        "-o", str(exe)], check=True)
        out = subprocess.run([str(exe)], input="\n".join(rows)+"\n", text=True,
                             capture_output=True, check=True).stdout.splitlines()
    counts, traces = Counter(), 0
    for i, (((entry, kind), req, want, right), row) in enumerate(zip(batch, out, strict=True)):
        cpp, py = json.loads(row), replay(req)
        assert cpp["id"] == i
        for got in (cpp, py):
            assert {k: got[k] for k in want} == want, (i, req, got, want)
            assert want["head"] <= got["read_min"] <= got["read_max"] <= right
        assert (cpp["read_min"], cpp["read_max"]) == (py["read_min"], py["read_max"])
        if "reads" in cpp:
            assert cpp["reads"] == py["reads"]
            traces += 1
        counts[f"{entry}:{kind}"] += 1
    print(json.dumps(dict(seed=SEED, cases=len(batch), traces=traces, by_kind=counts), sort_keys=True))


if __name__ == "__main__":
    main()
