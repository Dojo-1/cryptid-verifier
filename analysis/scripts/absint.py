"""Over-approximate reachable states of a counter system: each coordinate is either an exact
small value (< K) or BIG with a residue mod M. Successors are computed from many concrete
representatives (big values K+r+M*j, j in 0..J-1) so all small differences/orderings occur.
Discovery tool only: a hit-free result suggests an invariant to prove exactly in Lean."""
import sys, itertools; sys.path.insert(0,'/tmp/zk/global')
from machines import *
def absv(x,K,M): return x if x<K else ('B',x%M)
def reps(v,K,M,J):
    if isinstance(v,int): return [v]
    return [K+((v[1]-K)%M)+M*j for j in range(J)]
def explore(step,s0,K,M,J,halting_abs,limit=200000):
    start=tuple(absv(x,K,M) for x in s0); seen={start}; todo=[start]; halt_hits=set()
    while todo:
        A=todo.pop()
        for conc in itertools.product(*[reps(v,K,M,J) for v in A]):
            t=step(conc)
            if t=='HALT': halt_hits.add(A); continue
            if t=='STUCK': continue
            B=tuple(absv(x,K,M) for x in t)
            if B not in seen:
                seen.add(B); todo.append(B)
                if len(seen)>limit: return seen,halt_hits,'limit'
    return seen,halt_hits,'closed'
if __name__=="__main__":
    for K,M,J in ((8,4,10),(8,8,10),(12,8,8),(16,16,6)):
        seen,hh,st=explore(a1,(0,0,0,0),K,M,J,None)
        print(f"A.1 K={K} M={M} J={J}: {len(seen)} abstract states ({st}); abstract states that can step to HALT: {len(hh)}")
        if hh: print("   e.g.",list(hh)[:3])
