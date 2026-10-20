import sys; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from machines import a6
from collections import Counter
def runs(s,N=40000):
    for n in range(N):
        t=a6(s)
        if t=='HALT': return n,s
        s=t
        if max(s).bit_length()>600: return None
    return None
s=(0,0,0); pts=[]
for n in range(200000):
    s=a6(s)
    if n>2000 and n%8000==0: pts.append(s)
hits=[]
for p in pts[:20]:
    for i in range(3):
        for d in list(range(-12,0))+list(range(1,13)):
            q=list(p); q[i]+=d
            if q[i]<0: continue
            r=runs(tuple(q))
            if r: hits.append((p,i,d,r[0],r[1]))
for h in hits: print(h)
# which features separate the real orbit from halting-perturbed starting states?
orbit=[]; s=(0,0,0)
for n in range(300000):
    s=a6(s); orbit.append(s)
def feats(x):
    u,v,w=x; F={}
    for m in (2,3,4,6,8):
        for name,val in (('u',u),('v',v),('w',w),('u+w',u+w),('v+w',v+w),('u+v',u+v),('2u-w',2*u-w),('u+v+w',u+v+w),('v-2u',v-2*u)):
            F[(name,m)]=val%m
    return F
orb={}
for x in orbit:
    for k,v in feats(x).items(): orb.setdefault(k,set()).add(v)
cands=[k for k,vals in orb.items() if len(vals)<k[1]]
print("features where the real orbit misses some residue:",[(k,sorted(orb[k])) for k in cands])
