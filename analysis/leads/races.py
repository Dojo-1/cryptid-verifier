import sys, collections, json
sys.argv=['x']; exec(open('sim.py').read().split("if __name__")[0])
import numpy as np
from fractions import Fraction
def fit(pairs, nin):
    X=np.array([list(x)+[1] for x,_ in pairs],float); Y=np.array([list(y) for _,y in pairs],float)
    sol,*_=np.linalg.lstsq(X,Y,rcond=None)
    fr=[[Fraction(v).limit_denominator(8) for v in col] for col in sol.T]
    ok=all(sum(f*xi for f,xi in zip(row,list(x)+[1]))==yi for x,y in pairs for row,yi in zip(fr,y))
    return ok,fr
def race_model(seq):
    # segment into maximal runs of constant delta
    runs=[]; i=0
    while i<len(seq)-1:
        d=tuple(b-a for a,b in zip(seq[i],seq[i+1])); j=i+1
        while j<len(seq)-1 and tuple(b-a for a,b in zip(seq[j],seq[j+1]))==d: j+=1
        runs.append((seq[i],seq[j],d,j-i)); i=j
    deltas=collections.Counter(r[2] for r in runs if r[3]>=3)
    # resets: from end of a long run to the start of the next run
    rd={r[2] for r in runs if r[3]>=3}
    resets=[(a,b) for a,b in zip(seq,seq[1:]) if tuple(y-x for x,y in zip(a,b)) not in rd]
    best=None
    for m in (1,2,3,4,6):
        groups=collections.defaultdict(list)
        for a,b in resets: groups[tuple(v%m for v in a)].append((a,b))
        res={}; allok=True; covered=0
        for key,pairs in groups.items():
            if len(pairs)<len(pairs[0][0])+2: allok=False; continue
            ok,fr=fit(pairs,len(pairs[0][0])); res[key]=(ok,len(pairs),fr); covered+=len(pairs)
            allok&=ok
        if res and all(v[0] for v in res.values()):
            best=(m,res,covered,len(resets)); break
    return deltas,best,len(resets)
for tm in open('leads.txt').read().split():
    shapes=collections.Counter(); seqs=collections.defaultdict(list)
    def ev(n, st, side, tape, lo, hi, pos):
        key, expo = shape_of(st, side, tape, lo, hi, pos)
        if expo: shapes[key]+=1; seqs[key].append(expo)
    simulate(tm, 3000000, ev)
    if not shapes: print(tm,'no shapes'); continue
    key,cnt=shapes.most_common(1)[0]
    seq=[s for s in seqs[key]]
    if len(seq)<20 or len(set(len(s) for s in seq))>1: print(f"{tm:42s} top shape too rare/irregular (count {cnt})"); continue
    deltas,best,nres=race_model(seq)
    if best:
        m,res,cov,tot=best
        rules='; '.join(f"{k}:{['('+','.join(str(f) for f in row)+')' for row in v[2]]}" for k,v in sorted(res.items()))
        print(f"{tm:42s} races {dict(deltas)}  resets {cov}/{tot} fit exactly mod {m}: {rules}")
    else:
        print(f"{tm:42s} races {dict(deltas)}  resets: no exact affine fit (n={nres})")
