import numpy as np, math
P=np.load('/tmp/zk/p1/parities.npy').astype(np.int64); N=len(P)
d=np.where(P==0,2,-1); a=np.cumsum(d)
print(f"N={N}: min counter a_t over t>=15: {a[14:].min()} (never negative: {a.min()>=0}); a_N={a[-1]}")
# P1 drawdown records
peak=np.maximum.accumulate(a); dd=peak-a; DD=np.maximum.accumulate(dd)
PHI=(1+5**.5)/2; t=np.arange(1,N+1)
rec=np.flatnonzero(np.diff(DD)>0)+1
ratios=[(int(t[i]),int(DD[i]),DD[i]/(math.log(t[i])/math.log(PHI))) for i in rec if t[i]>=10**6]
print("P1 records in [1e6,1e7] (t, DD, ratio):",ratios if ratios else "none (no new record)")
print(f"   DD(1e6)={DD[10**6-1]}, DD(N)={DD[-1]}, log_phi N={math.log(N)/math.log(PHI):.2f}, ratio at N={DD[-1]/(math.log(N)/math.log(PHI)):.3f}")
# P3 drift band
lo=10**6; tt=t[lo-1:]; dev=np.abs(a[lo-1:]/tt-0.5); band=3*np.sqrt(np.log(tt)/tt)
print(f"P3: max (|a_t/t-1/2| / band) on [1e6,1e7] = {np.max(dev/band):.3f}  (holds iff <= 1)")
# P4 chi^2 independence of past j / future k, j+k<=16
worst=(0,None); zs=[]
for L in range(2,17):
    code=np.zeros(N-L+1,dtype=np.int64)
    for i in range(L): code=code*2+P[i:N-L+1+i]
    cnt=np.bincount(code,minlength=2**L).astype(float); n=cnt.sum()
    for j in range(1,L):
        k=L-j; M=cnt.reshape(2**j,2**k)
        e=M.sum(1,keepdims=True)*M.sum(0,keepdims=True)/n
        chi=((M-e)**2/e).sum(); dof=(2**j-1)*(2**k-1); z=(chi-dof)/math.sqrt(2*dof)
        zs.append((z,j,k))
zs.sort()
print(f"P4: {len(zs)} (j,k) pairs; z range [{zs[0][0]:.2f}, {zs[-1][0]:.2f}]; largest:",[(round(z,2),j,k) for z,j,k in zs[-4:]])
print("   P4 holds (all |z|<=4):",all(abs(z)<=4 for z,_,_ in zs),"; refuted (any z>6):",any(z>6 for z,_,_ in zs))
