"""Fuzz the start: perturb one coordinate of states on each orbit and record which perturbations halt."""
import sys, random; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from machines import MACHINES
from collections import Counter
random.seed(1)
def runs(step,s,N=40000,cap=600):
    for n in range(N):
        t=step(s)
        if t=='HALT': return n
        if t=='STUCK': return 'STUCK'
        s=t
        if max(s).bit_length()>cap: return None
    return None
print(f"{'machine':9s} {'tried':>6s} {'halted':>6s} {'frac':>6s} {'median steps':>12s}  delta mod 2 / mod 3 among halting (vs all)")
for name,(step,s0,_,_) in MACHINES.items():
    s=s0; pts=[]
    for n in range(200000):
        t=step(s)
        if t in('HALT','STUCK'): break
        s=t
        if n>2000 and n%8000==0: pts.append(s)
    tried=0; halts=[]; dmods=Counter(); allmods=Counter()
    for p in pts[:20]:
        for i in range(len(p)):
            for dlt in list(range(-12,0))+list(range(1,13)):
                q=list(p); q[i]+=dlt
                if q[i]<0: continue
                q=tuple(q); tried+=1; allmods[(dlt%2,dlt%3)]+=1
                r=runs(step,q)
                if r=='STUCK': continue
                if r is not None: halts.append(r); dmods[(dlt%2,dlt%3)]+=1
    fr=len(halts)/max(tried,1)
    med=sorted(halts)[len(halts)//2] if halts else '-'
    m2=sum(v for k,v in dmods.items() if k[0]==0)/max(len(halts),1)
    m3=[sum(v for k,v in dmods.items() if k[1]==r)/max(len(halts),1) for r in range(3)]
    print(f"{name:9s} {tried:6d} {len(halts):6d} {fr:6.3f} {str(med):>12s}  even δ {m2:.2f}; δ≡0,1,2 mod 3: {m3[0]:.2f} {m3[1]:.2f} {m3[2]:.2f}")
