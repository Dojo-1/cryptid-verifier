"""P1/P3/P4 at t = 1e7 for Antihydra. Parities in chunks of K via b mod 2^K (pv_mod), exact b advanced
by one big multiplication per chunk via 2^K b' = 3^K b + S_K (real_bridge)."""
import sys, math, time, numpy as np
try:
    import gmpy2; MPZ=gmpy2.mpz
except ImportError:
    MPZ=int
N=int(sys.argv[1]); K=4096
b=MPZ(4); P=np.empty(N,dtype=np.int8); t=0; t0=time.time(); pow3=MPZ(3)**K
while t<N:
    k=min(K,N-t)
    x=int(b & ((1<<k+2)-1)) if True else 0
    x=int(b % (MPZ(1)<<(k+64)))      # enough low bits for k parities
    S=0; p_list=[]
    for i in range(k):
        p=x&1; p_list.append(p)
        S=3*S+(1<<i)*(4-p)
        x=3*(x>>1)+2+p
    P[t:t+k]=p_list
    b=((MPZ(3)**k if k!=K else pow3)*b+S)>>k
    t+=k
    if t%(1<<20)<K: print(f"t={t} bits={b.bit_length() if hasattr(b,'bit_length') else int(b).bit_length()} elapsed={time.time()-t0:.0f}s",flush=True)
np.save('/tmp/zk/p1/parities.npy',P)
print("done",time.time()-t0,flush=True)
