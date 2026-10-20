import numpy as np, itertools
from collections import defaultdict
def build(step, sample, vert, fib):
    V={}; E=defaultdict(set)
    def vid(x):
        if x not in V: V[x]=len(V)
        return V[x]
    for s in sample:
        t=step(s)
        if t is None: continue
        u=vid(vert(s))
        if t=='HALT': E[(u,vid('HALT'))].add(None); continue
        v=vid(vert(t)); E[(u,v)].add(tuple(y-x for x,y in zip(fib(s),fib(t))))
    return V,E
def charker(V,E,ks,chi,drop=None,ret=None):
    # magnetic Laplacian for character chi of Z/k1 x..x Z/kn ; None-labels (halt edges) get phase 1
    n=len(V); L=np.zeros((n,n),complex)
    edges=[(u,v,l) for (u,v),ls in E.items() for l in ls]
    if ret: edges.append(ret)
    for u,v,l in edges:
        if drop is not None and (u==drop or v==drop): continue
        ph=1 if l is None else np.exp(2j*np.pi*sum(c*d/k for c,d,k in zip(chi,l,ks)))
        if u==v:
            L[u,u]+=2-2*ph.real; continue
        L[u,u]+=1; L[v,v]+=1; L[u,v]-=ph; L[v,u]-=np.conj(ph)
    keep=[i for i in range(n) if i!=drop]
    L=L[np.ix_(keep,keep)]
    return int((np.abs(np.linalg.eigvalsh(L))<1e-7).sum())
def report(name,V,E,ks,start):
    h=V['HALT']; s=V[start]
    chis=list(itertools.product(*[range(k) for k in ks]))
    full=sum(charker(V,E,ks,c) for c in chis)
    punct=sum(charker(V,E,ks,c,drop=h) for c in chis)
    # closed system: return edge HALT->start with trivial label
    closed=sum(charker(V,E,ks,c,ret=(h,s,None)) for c in chis)
    G=int(np.prod(ks))
    # comp counts (chi=0)
    c_full=charker(V,E,ks,tuple(0 for _ in ks)); c_p=charker(V,E,ks,tuple(0 for _ in ks),drop=h)
    print(f"{name:42s} |G|={G:3d} comps={c_full} ker_full={full} (|G/H|={full/c_full:g})  "
          f"punctured: comps={c_p} ker={punct}  closed-loop ker={closed}")
# ---------- Antihydra
def anti(s):
    a,b=s
    if b%2==0: return (a+2,3*(b//2)+2)
    if a==0: return 'HALT'
    return (a-1,3*(b//2)+3)
S=[(a,b) for a in range(0,48) for b in range(0,256)]
for n in (2,4):
  for k in (2,3,4,5,6,8):
    V,E=build(anti,S,lambda s,n=n:(s[0]==0,s[1]%2**n),lambda s:(s[0],))
    report(f"Antihydra  base=(a==0,b mod 2^{n}) fib=a mod {k}",V,E,(k,),(True,4%2**n))
# ---------- A.9 with orthogonal tapes b,c (and a)
def a9(s):
    a,b,c=s
    if b==0 and c==0: return 'HALT'
    if b==0 and c==1: return (5,2,a//2+1) if a%2==0 else (2,0,a//2+3)
    if b==0: return (2,a//2+3,c-2) if a%2==0 else (5,a//2+3,c-2)
    if c==0: return (a+3,0,b-1)
    return (a+6,b-1,c-1)
S9=[(a,b,c) for a in range(0,40) for b in range(0,20) for c in range(0,20)]
vert=lambda s:(max(-3,min(3,s[1]-s[2])),s[0]%2,s[1]==0,s[2]==0)
st=vert((5,2,0))
for ks,fib in [((2,2),lambda s:(s[1],s[2])),((3,3),lambda s:(s[1],s[2])),((4,4),lambda s:(s[1],s[2])),
               ((2,2,2),lambda s:(s[0],s[1],s[2])),((3,3,3),lambda s:(s[0],s[1],s[2])),((6,),lambda s:(s[1]-s[2],))]:
    V,E=build(a9,S9,vert,fib)
    report(f"A.9 base=(clip b-c,a%2,flags) fib k={ks}",V,E,ks,st)
print("\n--- locate the punctured (2,2,2) invariant")
ks=(2,2,2); fib=lambda s:(s[0],s[1],s[2])
V,E=build(a9,S9,vert,fib); h=V['HALT']; inv={i:x for x,i in V.items()}
for chi in itertools.product(range(2),repeat=3):
    if charker(V,E,ks,chi,drop=h)>=1 and any(chi):
        print("character",chi)
        # solve potential phi on base: chi.label = phi(v)-phi(u) mod 2
        phi={V[st]:0}; stack=[V[st]]; ok=True
        adj=defaultdict(list)
        for (u,v),ls in E.items():
            for l in ls:
                if l is None: continue
                d=sum(c*x for c,x in zip(chi,l))%2
                adj[u].append((v,d)); adj[v].append((u,d))
        while stack:
            u=stack.pop()
            for v,d in adj[u]:
                if v not in phi: phi[v]=(phi[u]+d)%2; stack.append(v)
                elif phi[v]!=(phi[u]+d)%2: ok=False
        print("consistent:",ok)
        I=lambda s:(sum(c*x for c,x in zip(chi,fib(s)))-phi[V[vert(s)]])%2
        # check on real trajectory from start
        s=(5,2,0); vals=set(); n=0
        while n<20000:
            t=a9(s)
            if t=='HALT': print("halted"); break
            vals.add(I(s)); s=t; n+=1
        print("invariant values along trajectory:",vals)
        hv=[(x,I(x)) for x in S9 if a9(x)=='HALT'][:3]
        print("halting states (b=c=0) invariant values:",{I(x) for x in S9 if a9(x)=='HALT'}, hv)
        for u in sorted(phi, key=lambda i:str(inv[i])): print("  phi",inv[u],phi[u])
