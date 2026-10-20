import numpy as np, scipy.sparse as sp, scipy.sparse.linalg as sla
def signedL(k, twist, theta=None):
    n=2**k; rows=[];cols=[];vals=[]; deg=np.zeros(n)
    for w in range(n):
        for bit in (0,1):
            v=((w<<1)|bit)&(n-1)
            if theta is None: ph=-1.0 if twist(bit) else 1.0
            else: ph=np.exp(1j*theta*(2 if bit==0 else -1))
            if w==v: deg[w]+=2; rows+= [w]; cols+=[w]; vals+=[-2*np.real(ph)]; continue
            deg[w]+=1; deg[v]+=1
            rows+=[w,v]; cols+=[v,w]; vals+=[-ph, -np.conj(ph)]
    A=sp.coo_matrix((vals,(rows,cols)),shape=(n,n)).tocsr()
    return (sp.diags(deg)+A)
print(" k   lam_min(Mobius)  k*lam   mass of ground state on windows with >=k-2 ones")
for k in range(4,15):
    L=signedL(k, lambda b: b==1).astype(float)
    vals,vecs=sla.eigsh(L,k=1,sigma=-1e-3,which='LM')
    v=vecs[:,0]**2; ones=np.array([bin(w).count('1') for w in range(2**k)])
    print(f"{k:2d}  {vals[0]:.5f}        {k*vals[0]:.3f}   {v[ones>=k-2].sum():.3f}   (uniform would be {(ones>=k-2).mean():.4f})")
print("\nflux scan on k=10 window graph (U(1) phase theta per unit of counter):")
for th in np.linspace(0,2*np.pi,13):
    L=signedL(10,None,theta=th)
    lam=np.linalg.eigvalsh(L.toarray())[0]
    print(f"  theta={th/np.pi:.3f}pi  lam_min={lam:.5f}")
