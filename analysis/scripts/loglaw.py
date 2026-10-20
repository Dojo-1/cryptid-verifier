import math, sys; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from machines import a3, a8
PHI=(1+5**.5)/2
# Antihydra: maximal drawdown of the counter walk vs log_phi t
a,b=0,4; peak=0; dd=0; rec=[]
for t in range(1,1_000_001):
    odd=b&1; a+= -1 if odd else 2; b=3*(b>>1)+(3 if odd else 2)
    peak=max(peak,a); 
    if peak-a>dd: dd=peak-a; rec.append((t,dd))
print("Antihydra drawdown records (t, DD, DD/log_phi t):")
for t,d in rec[-8:]: print(f"   t={t:8d} DD={d:3d}  ratio={d/(math.log(t)/math.log(PHI)):.3f}")
print(f"   at t=1e6: DD={dd}, log_phi t={math.log(1e6)/math.log(PHI):.1f}, a_t={a}")
# window machines: depth of approach to the halting window vs log of decision index
def depth_records(step,s0,rf,W,N=3_000_000):
    s=s0; i=0; best=-1; recs=[]
    for n in range(N):
        t=step(s)
        x=rf(s)
        if x is not None:
            r,L=x; i+=1
            d=min(abs(r-w) for w in W)
            dep=math.log2(max(L,2)/max(d,1))
            if dep>best: best=dep; recs.append((i,dep,math.log2(max(L,2))))
        s=t
        if max(s).bit_length()>3000: break
    return i,recs
def r3(s):
    a,c,f=s; return (c//2-a//2,max(a,c)//2) if a>=4 and c>=4 else None
def r8(s):
    a,b=s
    if b%2==0:
        k=(b-6)//2; return (k-(a-1)-4,max(a,k)) if a>=1 else None
    k=(b-1)//2; return (a-k,max(a,k))
for name,step,s0,rf,W in (("A.3",a3,(6,2,2),r3,{0,1}),("A.8",a8,(0,9),r8,{0,1})):
    n,recs=depth_records(step,s0,rf,W)
    print(f"{name}: {n} decisions; record approach depth log2(L/dist) vs log2(i) and log2(L):")
    for i,dep,lL in recs[-5:]: print(f"   i={i:6d} depth={dep:6.2f} log2 i={math.log2(i):5.2f}  log2 L={lL:8.1f}")
