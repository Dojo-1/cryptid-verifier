import numpy as np
def lam(k,pe,po):
    n=2**k; L=np.zeros((n,n),complex)
    for w in range(n):
        for bit in (0,1):
            v=((w<<1)|bit)&(n-1); ph=np.exp(1j*(po if bit else pe))
            if w==v: L[w,w]+=2-2*ph.real; continue
            L[w,w]+=1; L[v,v]+=1; L[w,v]-=ph; L[v,w]-=np.conj(ph)
    return np.linalg.eigvalsh(L)[0]
eps=1e-3
print(" k   window-only λ/ε²   pred 2(1/4+9/(4(k+1)))   with time λ/ε²   pred 2·9/(4(k+1))   k·(with time)")
for k in range(2,11):
    wo=lam(k,2*eps,-eps)/eps**2
    # with time: counter + c*t, c optimal = -1/2 (removes the mean drift): steps +1.5 / -1.5
    wt=min(lam(k,(2+c)*eps,(-1+c)*eps) for c in np.linspace(-1,0,41))/eps**2
    print(f"{k:2d}   {wo:.4f}             {2*(0.25+9/(4*(k+1))):.4f}                  {wt:.4f}          {2*9/(4*(k+1)):.4f}            {k*wt:.3f}")
# real (imaginary-flux) tilt: Perron root of transfer operator with weights e^{eps*da}/2
print("\nreal tilt  Λ(ε)=log ρ: exact at every depth? (row sums constant)")
for k in (3,6,9):
    n=2**k
    for e in (-np.log((1+5**.5)/2), 0.3):
        M=np.zeros((n,n))
        for w in range(n):
            M[w,((w<<1)|0)&(n-1)]+=np.exp(2*e)/2; M[w,((w<<1)|1)&(n-1)]+=np.exp(-e)/2
        rho=max(abs(np.linalg.eigvals(M)))
        print(f"  k={k} ε={e:+.4f}  ρ={rho:.6f}  closed form (e^2ε+e^-ε)/2={(np.exp(2*e)+np.exp(-e))/2:.6f}")
