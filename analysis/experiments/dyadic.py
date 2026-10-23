import numpy as np
d=8; n=2**d
def lam(pe,po):
    # window graph, phase pe on even-step edges, po on odd-step edges (radians)
    L=np.zeros((n,n),complex)
    for w in range(n):
        for bit in (0,1):
            v=((w<<1)|bit)&(n-1); ph=np.exp(1j*(po if bit else pe))
            if w==v: L[w,w]+=2-2*ph.real; continue
            L[w,w]+=1; L[v,v]+=1; L[w,v]-=ph; L[v,w]-=np.conj(ph)
    return np.linalg.eigvalsh(L)[0]
cache={}
def lamuv(u,v,m):
    key=(u%m,v%m,m)
    if key not in cache: cache[key]=lam(2*np.pi*u/m,2*np.pi*v/m)
    return cache[key]
print("tower        m   window-only min_j   window x time: min_j   argmin j   j*3 mod m   ground mass near 1..1")
for fam,base in (("Z/2^k",2),("Z/4^k",4),("Z/8^k",8)):
    for k in (1,2,3):
        m=base**k
        if m>512: continue
        wo=min(lamuv(2*j,-j,m) for j in range(1,m))
        best=(9,None)
        js=range(1,m) if m<=64 else [pow(3,-1,m), m-pow(3,-1,m)]
        for j in js:
            ss=range(m) if m<=64 else [j%m,(-2*j)%m]
            l=min(lamuv(2*j+s,-j+s,m) for s in ss)
            if l<best[0]-1e-12: best=(l,j)
        print(f"{fam:6s} k={k}  {m:4d}   {wo:.5f}            {best[0]:.6f}            {best[1]:4d}      {3*best[1]%m}")
print("\n2-adic limit of argmin j = 3^-1 mod 2^n:", [pow(3,-1,2**e) for e in range(1,13)])
print("binary of 3^-1 mod 2^12:", bin(pow(3,-1,4096)))
