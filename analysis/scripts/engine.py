"""Invariant search for the Cryptid counter systems, certified with lambda-sat.

Abstract state of a concrete state x: each coordinate exact if < K, else ('B', x mod M); plus each pairwise
difference clipped to [-D, D] ('<', '>' beyond). Abstract edges are read off ALL concrete states in a box
[0, B]^d (box-sampled abstraction: a discovery tool, not a proof). An invariant is a set I of abstract states
with start in I, closed under edges, containing no state that can step to HALT. Those are binary/unit clauses,
i.e. 2-SAT, which lambda-sat's frame solver decides with a sound certificate (model replay for SAT)."""
import sys, itertools, time
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.environ.get('LAMBDA_SAT', '../../../lambda-sat-solver'))
from machines import MACHINES
from backend.cnf_utils import CNFFormula, verify_model
from backend.frame_solver import frame_solve, frame_solve_scouted, frame_solve_coupled

def absf(x, K, M, D):
    co = tuple(v if v < K else ('B', v % M) for v in x)
    rel = []
    for i, j in itertools.combinations(range(len(x)), 2):
        if x[i] >= K and x[j] >= K:
            df = x[i] - x[j]; rel.append(df if -D <= df <= D else ('<' if df < 0 else '>'))
        else: rel.append(None)
    return co + tuple(rel)

def search(name, K, M, D, B):
    step, s0, _, _ = MACHINES[name]
    d = len(s0); idx = {}; edges = set(); halting = set()
    def vid(a):
        if a not in idx: idx[a] = len(idx) + 1
        return idx[a]
    for x in itertools.product(range(B + 1), repeat=d):
        t = step(x)
        if t == 'STUCK': continue
        u = vid(absf(x, K, M, D))
        if t == 'HALT': halting.add(u); continue
        edges.add((u, vid(absf(t, K, M, D))))
    s = vid(absf(s0, K, M, D))
    sources = {u for u, _ in edges} | halting
    unknown = [u for u in range(1, len(idx) + 1) if u not in sources]   # never sampled: successors unknown
    clauses = [[s]] + [[-u, v] for u, v in edges] + [[-h] for h in halting] + [[-u] for u in unknown]
    f = CNFFormula(num_vars=len(idx), clauses=clauses)
    r = frame_solve_coupled(f, max_rounds=10**6)        # lambda-sat coupled frame: BCP + 2-SAT + parity, sound refutation
    if r.status == 'UNSAT':
        return 'UNSAT', r.resolved_by, True, len(idx), len(edges), len(halting), 0
    # consistent 2-SAT: the least fixed point (reachable closure) is the candidate; replay it
    adj = {}
    for u, v in edges: adj.setdefault(u, []).append(v)
    seen = {s}; todo = [s]
    while todo:
        u = todo.pop()
        for v in adj.get(u, []):
            if v not in seen: seen.add(v); todo.append(v)
    model = {v: (v in seen) for v in range(1, len(idx) + 1)}
    ok = verify_model(f, model)                          # lambda-sat model replay
    if not ok:
        why = 'halt' if seen & halting else 'unsampled'
        return 'NO-INV('+why+')', r.status, False, len(idx), len(edges), len(halting), len(seen)
    return ('SAT' if ok else 'BAD'), 'lfp+replay', ok, len(idx), len(edges), len(halting), len(seen)

if __name__ == '__main__':
    cfgs = [(4, 2, 2), (6, 4, 4), (6, 6, 6), (8, 12, 8), (8, 24, 12)]
    names = [n for n in MACHINES]
    for name in names:
        d = len(MACHINES[name][1]); B = {2: 120, 3: 40, 4: 18}[d]
        for K, M, D in cfgs:
            t0 = time.time()
            st, by, ok, nv, ne, nh, inv = search(name, K, M, D, B)
            print(f"{name:9s} K={K} M={M:2d} D={D}: {st:5s} via {by:10s} certified={ok} "
                  f"abstract={nv} edges={ne} halting={nh} invariant_size={inv} ({time.time()-t0:.1f}s)", flush=True)
