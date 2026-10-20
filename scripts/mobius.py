import numpy as np, itertools
X=np.array([[0,1],[1,0]]); I=np.eye(2)
def ker(k, twist):
    n=2**k; L=np.zeros((2*n,2*n))
    for w in range(n):
        for bit in (0,1):
            v=((w<<1)|bit)&(n-1)       # window shift: drop oldest, append new parity
            s=twist(w&1,bit)            # (last parity, next parity) -> twist?
            B=X if s else I
            if w==v:
                L[2*w:2*w+2,2*w:2*w+2]+=2*I-B-B.T; continue
            L[2*w:2*w+2,2*w:2*w+2]+=I; L[2*v:2*v+2,2*v:2*v+2]+=I
            L[2*w:2*w+2,2*v:2*v+2]-=B; L[2*v:2*v+2,2*w:2*w+2]-=B.T
    return int((np.abs(np.linalg.eigvalsh(L))<1e-8).sum())
rules={"Mobius  (twist on odd step)":lambda p,q:q==1,
       "anti    (twist on even step)":lambda p,q:q==0,
       "double  (twist every step)":lambda p,q:True,
       "flip    (twist when parity changes)":lambda p,q:p!=q,
       "anti-flip (twist when parity repeats)":lambda p,q:p==q}
for name,r in rules.items():
    print(f"{name:40s}", [ker(k,r) for k in range(1,9)])
