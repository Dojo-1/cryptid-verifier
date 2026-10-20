import sys; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from machines import MACHINES
from collections import Counter
H=60000
print(f"{'machine':9s} {'tried':>6s} {'merge into real orbit':>22s} {'halt':>5s} {'distinct halting configs':>24s}")
for name,(step,s0,_,_) in MACHINES.items():
    s=s0; orbit=[]; 
    for n in range(H):
        t=step(s)
        if t in('HALT','STUCK'): break
        s=t; orbit.append(s)
        if max(s).bit_length()>600: break
    oset=set(orbit); pts=orbit[2000::max(1,len(orbit)//25)][:20]
    tried=merged=halted=0; hc=Counter()
    for p in pts:
        for i in range(len(p)):
            for d in list(range(-12,0))+list(range(1,13)):
                q=list(p); q[i]+=d
                if q[i]<0: continue
                x=tuple(q); tried+=1
                for n in range(40000):
                    if x in oset and n>0: merged+=1; break
                    y=step(x)
                    if y=='HALT': halted+=1; hc[x]+=1; break
                    if y=='STUCK' or max(y).bit_length()>600: break
                    x=y
    print(f"{name:9s} {tried:6d} {merged:22d} {halted:5d}   {dict(hc.most_common(3))}")
