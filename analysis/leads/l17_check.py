"""Raw-TM checks for L17 = 1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---.
Section C(a,b) = 0^inf C> (01)^a 1^b 0^inf. Each check runs the raw machine from the full
configuration until the first exact return to the section and compares (target, steps, head shift)."""
import sys
from l17_sim import cfg, run_until_C

def branch(a, b):
    if b == 0: return (0, 2*a+4), 4*a+8, -2
    if a == 0: return (1, b), 2, -2
    if b == 2: return (a+4, 0), 6*a+21, -7
    if b >= 3: return (a+5, b-3), 6*a+21, -7
    if a % 3 == 0 and a >= 6:           # new: C(3k,1), k >= 2
        k = a // 3
        return (10*k-12, 3), 60*k*k-204*k+244, 24-14*k
    return None

def check(a, b):
    p = branch(a, b)
    if p is None: return None
    t, h, st = cfg(a, b)
    r = run_until_C(t, h, st, 10**8)
    return (r[0], r[1], r[2]) == p

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    res = [check(a, b) for a in range(N) for b in range(N)]
    res += [check(3*k, 1) for k in range(2, 4*N)]
    done = [r for r in res if r is not None]
    print(f"{len(done)} raw checks, {done.count(False)} failures")
    sys.exit(1 if False in done else 0)
