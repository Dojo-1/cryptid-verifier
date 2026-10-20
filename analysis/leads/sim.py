"""Lead triage: raw TM simulation, halting check, macro-shape discovery, exact affine rule fitting."""
import sys, collections, itertools, json
from fractions import Fraction

def parse(tm):
    rows = tm.split('_'); k = len(rows[0]) // 3
    T = {}
    for s, row in enumerate(rows):
        for sym in range(k):
            x = row[3*sym:3*sym+3]
            T[(s, sym)] = None if x[0] == '-' else (int(x[0]), 1 if x[1] == 'R' else -1, ord(x[2]) - 65)
    return T, len(rows), k

def simulate(tm, N, on_event):
    T, ns, k = parse(tm)
    size = 1 << 16; tape = bytearray(size); pos = size // 2; lo = hi = pos; st = 0
    for n in range(N):
        sym = tape[pos]; tr = T[(st, sym)]
        if tr is None: return ('HALT', n)
        w, d, st2 = tr; tape[pos] = w; pos += d; st = st2
        if pos < 2 or pos >= size - 2:
            new = bytearray(size * 2); off = size // 2; new[off:off+size] = tape
            tape = new; pos += off; lo += off; hi += off; size *= 2
        if pos < lo: lo = pos; on_event(n, st, 'L', tape, lo, hi, pos)
        elif pos > hi: hi = pos; on_event(n, st, 'R', tape, lo, hi, pos)
    return ('RUNNING', N)

def tokenize(cells):
    out = []; i = 0; n = len(cells)
    while i < n:
        best = (1, 1)  # (block length, repeats)
        for L in range(1, 5):
            if i + L > n: break
            blk = cells[i:i+L]; r = 1
            while cells[i+r*L:i+(r+1)*L] == blk: r += 1
            if r >= 2 and r * L > best[0] * best[1] and (best[1] == 1 or L <= best[0] or r*L > best[0]*best[1]):
                best = (L, r)
        L, r = best; out.append((bytes(cells[i:i+L]), r)); i += L * r
    return out

def shape_of(st, side, tape, lo, hi, pos):
    cells = tape[lo:hi+1]
    toks = tokenize(cells)
    shape = tuple((b, '*' if r >= 3 else r) for b, r in toks)
    expo = tuple(r for b, r in toks if r >= 3)
    return (st, side, shape), expo

def fit_rules(seq):
    """seq: consecutive exponent vectors of one shape (same length). Group transitions by the parity
    vector of the source; fit x' = A x + c exactly with rational coefficients (least squares, then check)."""
    import numpy as np
    groups = collections.defaultdict(list)
    for x, y in zip(seq, seq[1:]):
        if len(x) == len(y): groups[tuple(v % 2 for v in x)].append((x, y))
    rules = {}
    for par, pairs in groups.items():
        if len(pairs) < len(pairs[0][0]) + 3: continue
        X = np.array([list(x) + [1] for x, _ in pairs], dtype=float)
        Y = np.array([list(y) for _, y in pairs], dtype=float)
        sol, *_ = np.linalg.lstsq(X, Y, rcond=None)
        frac = [[Fraction(v).limit_denominator(12) for v in col] for col in sol.T]
        ok = all(sum(f * xi for f, xi in zip(row, list(x) + [1])) == yi
                 for x, y in pairs for row, yi in zip(frac, y))
        rules[par] = (ok, len(pairs), [[str(f) for f in row] for row in frac])
    return rules

def analyze(tm, N):
    shapes = collections.Counter(); seqs = collections.defaultdict(list)
    def ev(n, st, side, tape, lo, hi, pos):
        key, expo = shape_of(st, side, tape, lo, hi, pos)
        if expo:
            shapes[key] += 1; seqs[key].append(expo)
    status = simulate(tm, N, ev)
    top = shapes.most_common(3); res = []
    for key, cnt in top:
        seq = seqs[key]; growth = (max(seq[-1]) if seq else 0)
        res.append({'state': key[0], 'side': key[1], 'count': cnt, 'nexp': len(seq[0]),
                    'last_exponents': list(seq[-1])[:6], 'rules': fit_rules(seq)})
    return status, res

if __name__ == '__main__':
    N = int(sys.argv[1]); out = []
    for tm in open('leads.txt').read().split():
        status, res = analyze(tm, N)
        exact = [r for r in res if r['rules'] and all(v[0] for v in r['rules'].values())]
        print(f"{tm:42s} {status[0]:8s} {status[1]:>10d}  top shape count {res[0]['count'] if res else 0:6d}"
              f"  exponents {res[0]['nexp'] if res else '-'}  exact-fit shapes {len(exact)}", flush=True)
        out.append({'machine': tm, 'status': status, 'shapes': [
            {k: (v if k != 'rules' else {str(p): r for p, r in v.items()}) for k, v in r.items()} for r in res]})
    json.dump(out, open('triage.json', 'w'), indent=1, default=str)
