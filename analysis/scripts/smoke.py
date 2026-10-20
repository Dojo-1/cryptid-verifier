"""Reproducible evidence run for CI (fast): every transcribed rule system runs 100k steps without
getting stuck, and the raw Turing machines agree with the macro rules over 300k raw steps."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from machines import MACHINES
import tmcheck as T
bad = 0
for name, (step, s0, _, _) in MACHINES.items():
    s = s0
    for n in range(100_000):
        t = step(s)
        if t == 'STUCK': print(f"{name}: STUCK at {n} from {s}"); bad += 1; break
        if t == 'HALT': print(f"{name}: HALT at {n}"); bad += 1; break
        s = t
        if max(s).bit_length() > 3000: break
def a4ref(s):
    return (0, 2 * s[0] + 4) if s[1] == 1 else T.a4(s)
for name, tm, m, step, s0 in (("Antihydra", "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA", T.m_antihydra, T.antihydra, (0, 4)),
                              ("A.4", "1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA", T.m_a4, a4ref, (0, 3)),
                              ("A.9", "1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD", T.m_a9, T.a9, (5, 2, 0))):
    seq = [x for _, x in T.run(tm, 300_000, m)]
    mac = T.macro(step, s0, len(seq))
    ok = seq == mac[:len(seq)]
    print(f"{name}: {len(seq)} macro configurations on the raw tape, agree with rules: {ok}")
    bad += not ok
print("smoke OK" if bad == 0 else f"smoke FAILED ({bad})")
sys.exit(1 if bad else 0)
