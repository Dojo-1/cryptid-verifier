import math, numpy as np
from collections import Counter
N=1_000_000
b=4; P=np.empty(N,dtype=np.int8); bs3=[]; J=6
for t in range(N):
    p=b&1; P[t]=p
    if t<20000: bs3.append(b%3**J)
    b=3*(b>>1)+2+p
# 1. identity check: b_t mod 3^J determines the previous J parities (pv_past3)
seen={}; ok=True
for t in range(J,20000):
    key=bs3[t]; past=tuple(P[t-J:t])
    if seen.setdefault(key,past)!=past: ok=False
print("b_t mod 3^6 determines last 6 parities:",ok)
# 2. past/future independence: joint (past j bits, future k bits) vs product
def pf(j,k):
    n=N-j-k; w=np.zeros(n,dtype=np.int64)
    for i in range(j): w=w*2+P[i:i+n]
    f=np.zeros(n,dtype=np.int64)
    for i in range(k): f=f*2+P[j+i:j+i+n]
    joint=np.zeros((2**j,2**k)); np.add.at(joint,(w,f),1)
    pr=joint.sum(1,keepdims=True); pc=joint.sum(0,keepdims=True); e=pr*pc/n
    chi=((joint-e)**2/np.where(e>0,e,1)).sum(); dof=(2**j-1)*(2**k-1)
    mi=np.nansum(joint/n*np.log2(np.where(joint>0,joint*n/(pr*pc),1)))
    return chi,dof,mi,dof/(2*n*math.log(2))
print(" j  k   chi2      dof   z=(chi2-dof)/sqrt(2dof)   MI(bits)  MI-bias(indep)")
for j,k in ((1,1),(3,3),(4,4),(6,6),(8,4),(4,8)):
    chi,dof,mi,bias=pf(j,k)
    print(f"{j:2d} {k:2d} {chi:9.1f} {dof:7d} {(chi-dof)/math.sqrt(2*dof):12.2f}           {mi:.2e}  {bias:.2e}")
# 3. does the past drift predict the future drift? (the quantity halting depends on)
d=np.where(P==0,2,-1).astype(np.int64)
for k in (5,20,100):
    c=np.convolve(d,np.ones(k,dtype=np.int64),'valid')
    past,fut=c[:-k],c[k:]
    r=np.corrcoef(past,fut)[0,1]
    print(f"corr(past {k}-step drift, next {k}-step drift) = {r:+.4f}  (±{2/math.sqrt(len(past)/k):.4f} noise)")
print("robustness of (3,3):")
full=P.copy()
for lo,hi in ((0,500000),(500000,1000000)):
    P=full[lo:hi]; N=hi-lo
    chi,dof,mi,bias=pf(3,3); print(f"  steps {lo}-{hi}: z={(chi-dof)/math.sqrt(2*dof):.2f}")
