import sys; sys.path.insert(0,'/tmp/zk/global')
from machines import *
from collections import Counter
def run(step,s0,N=3_000_000,maxbits=3000):
    s=s0; prevd=None
    for n in range(N):
        t=step(s)
        if t in('HALT','STUCK'): return
        d=tuple(y-x for x,y in zip(s,t))
        yield s,t,(d!=prevd)
        prevd=d; s=t
        if max(s).bit_length()>maxbits: return
# A.1
r1=[d-b-2 for (a,b,c,d),t,new in run(a1,(0,0,0,0)) if a==0 and c==0 and d>=2]
print("A.1 r = d-b-2 at A(0,b,0,d):",len(r1),"values:",r1[:40]); print("   mod 4:",Counter(x%4 for x in r1))
# A.6 race starts
r6=[(w-2*u+1) for (u,v,w),t,new in run(a6,(0,0,0)) if new and u>=1 and w>=2]
print("A.6 race starts:",len(r6),"mod 2:",Counter(x%2 for x in r6),"mod 4:",Counter(x%4 for x in r6))
print("   r>0 (u runs out first):",sum(x>0 for x in r6)," r<0:",sum(x<0 for x in r6)," smallest |r|:",sorted(set(abs(x) for x in r6))[:8])
# A.10 race starts E(a,b,c) b>=1,c>=3 entered fresh
r10=[(c-2*b-3) for (a,b,c),t,new in run(a10,(1,0,2)) if new and b>=1 and c>=3]
print("A.10 race starts:",len(r10),"mod 2:",Counter(x%2 for x in r10),"mod 4:",Counter(x%4 for x in r10),"mod 7:",sorted(Counter(x%7 for x in r10).items()))
print("   smallest |r|:",sorted(set(abs(x) for x in r10))[:8])
