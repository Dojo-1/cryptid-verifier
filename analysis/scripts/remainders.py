"""At each decision point, the integer r that must land in a finite window W for the machine to halt.
Halting happens exactly when r ∈ W at some decision (derived from the paper's rules)."""
import sys, math; sys.path.insert(0,'/tmp/zk/global')
from machines import *
def a1_r(s,t):            # states A(0,b,0,d): halt iff d - b - 2 == 0
    a,b,c,d=s
    return (d-b-2, max(b,d)) if a==0 and c==0 and d>=2 else None
def a3_r(s,t):            # Euclid step C(2k,2m,f), k,m>=2: halt iff m-k in {0,1}
    a,c,f=s
    return (c//2-a//2, max(a,c)//2) if a>=4 and c>=4 else None
def a6_r(s,t):            # race start J(u,v,w), u>=1, w>=2: halt iff w == 2u-1
    u,v,w=s
    return (w-2*u+1, max(u,w)) if u>=1 and w>=2 and not (t[0]==u-1 and t[2]==w-2 and prev_race[0]) else None
def a8_r(s,t):
    a,b=s
    if b%2==0:
        k=(b-6)//2
        return ((k-(a-1)-4), max(a,k)) if a>=1 else None   # W = {0,1}
    k=(b-1)//2; return (a-k, max(a,k))                     # W = {0,1}
def a9_r(s,t):            # race start: first state with b,c>=1 after a reset; halt iff b-c in {0,1}
    a,b,c=s
    return (b-c, max(b,c)) if b>=1 and c>=1 and s[0] in (2,5) else None
def a10_r(s,t):           # race start E(a,b,c), b>=1, c>=3: halt iff c == 2b+3
    a,b,c=s
    return (c-2*b-3, max(b,c)) if b>=1 and c>=3 and a==1 else None
W={"A.1":{0},"A.3":{0,1},"A.6":{0},"A.8":{0,1},"A.9":{0,1},"A.10":{0}}
prev_race=[False]
SPEC={"A.1":(a1,(0,0,0,0),a1_r),"A.3":(a3,(6,2,2),a3_r),"A.6":(a6,(0,0,0),a6_r),
      "A.8":(a8,(0,9),a8_r),"A.9":(a9,(5,2,0),a9_r),"A.10":(a10,(1,0,2),a10_r)}
print(f"{'machine':8s} {'decisions':>9s} {'E[halts] if uniform':>20s} {'min |r| (r∉W)':>14s} {'obstruction moduli M<=200 (W never hit mod M)':>40s}")
for name,(step,s0,rf) in SPEC.items():
    s=s0; recs=[]
    for n in range(3_000_000):
        t=step(s)
        if t in('HALT','STUCK'): print(name,t,n); break
        x=rf(s,t)
        if x is not None: recs.append(x)
        s=t
        if max(s).bit_length()>3000: break
    exp=sum(len(W[name])/max(2*L,1) for r,L in recs)    # r roughly uniform on [-L, L]
    hit=[r for r,L in recs if r in W[name]]
    minr=min(abs(r) for r,L in recs if r not in W[name])
    obs=[M for M in range(2,201) if not any((r-w)%M==0 for r,L in recs for w in W[name])]
    print(f"{name:8s} {len(recs):9d} {exp:20.3f} {minr:14d}   {str(obs[:12]):40s} hits={len(hit)}")
