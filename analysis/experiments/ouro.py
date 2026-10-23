import numpy as np
def T(b):  # Antihydra b-map
    return np.where(b%2==0, 3*(b//2)+2, 3*(b//2)+3)
# 1) Terras-type check: parity vector of length k  <->  b mod 2^k is a bijection
for k in range(1,17):
    b=np.arange(2**k,dtype=np.int64); code=np.zeros_like(b); x=b.copy()
    for i in range(k):
        code|=(x%2)<<i; x=T(x)
    assert len(np.unique(code))==2**k, k
print("parity-vector map b mod 2^k -> {0,1}^k is a bijection for k<=16")
# 2) survival sets S_k: residues whose first k steps keep bank account a>=0 (start a=0)
print(" k   |S_k|/2^k   exact-walk-DP")
dist={0:1.0}
for k in range(1,25):
    b=np.arange(2**k,dtype=np.int64) if k<=22 else None
    if b is not None:
        a=np.zeros_like(b); alive=np.ones(2**k,bool); x=b.copy()
        for i in range(k):
            ev=(x%2==0)
            alive&=~((~ev)&(a==0)); a=np.where(ev,a+2,a-1); x=T(x)
        frac=alive.mean()
    # pure random-walk DP (+2 / -1, absorb at -1)
    nd={}
    for v,p in dist.items():
        nd[v+2]=nd.get(v+2,0)+p/2
        if v>0: nd[v-1]=nd.get(v-1,0)+p/2
    dist=nd; w=sum(dist.values())
    if k in (1,2,3,4,6,8,12,16,20,22,24): print(f"{k:2d}  {frac if b is not None else float('nan'):.6f}   {w:.6f}")
print("limit 1/phi^2 =",(3-5**0.5)/2)
# 3) projection check: S_{k+1} maps into S_k (tower closes on itself)
