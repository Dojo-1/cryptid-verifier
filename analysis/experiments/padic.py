import numpy as np
d=7; n=2**d
def lam(pe,po):
    L=np.zeros((n,n),complex)
    for w in range(n):
        for bit in (0,1):
            v=((w<<1)|bit)&(n-1); ph=np.exp(1j*(po if bit else pe))
            if w==v: L[w,w]+=2-2*ph.real; continue
            L[w,w]+=1; L[v,v]+=1; L[w,v]-=ph; L[v,w]-=np.conj(ph)
    return np.linalg.eigvalsh(L)[0]
def row(m):
    wo=min(lam(2*np.pi*2*j/m,-2*np.pi*j/m) for j in range(1,m))
    # window x time: gauge s=j makes phases (3j, 0); best over s in {j,-2j} (exact for kernel)
    lt=[min(lam(2*np.pi*3*j/m,0), lam(0,-2*np.pi*3*j/m)) for j in range(1,m)]
    bal=[j for j,l in enumerate(lt,1) if l<1e-9]
    nonbal=[l for l in lt if l>=1e-9]
    return wo, bal, (min(nonbal) if nonbal else float('nan'))
print("tower      m    window-only min   balanced chars (with time)   min over non-balanced")
for p,ks in ((3,(1,2,3,4)),(5,(1,2,3)),(7,(1,2,3)),(11,(1,2)),(13,(1,2))):
    for k in ks:
        m=p**k; wo,bal,mn=row(m)
        print(f"Z/{p}^{k}  {m:5d}    {wo:.5f}          {str(bal):24s}     {mn:.5f}")
# 3-adic duality check: last j parities are a function of T^j(b) mod 3^j
T=lambda b: 3*(b//2)+2+(b&1)
ok=True
for j in range(1,8):
    seen={}
    for b in range(0,2*3**j*40):
        x=b; par=[]
        for _ in range(j): par.append(x&1); x=T(x)
        key=x%3**j
        if seen.setdefault(key,tuple(par))!=tuple(par): ok=False
print("3-adic past-parity determination (j<=7):",ok)
