"""Contextual-lemma stepper: every step is one Lean lemma that holds with arbitrary right context.

State: 𝒞(a; w) = 0^∞ C> (01)^a w 0^∞, where w is a run list over the units '1', '0' and '01'.
The steps (Lean name, file):
  Z    zT              (L17c)  𝒞(a; 00 w)                 → 𝒞(0; 1^(2a+4) w)
  EQ   stepEC          (L17c)  𝒞(0; 1^n X)                → 𝒞(1+5q; 1^r X),         n = 3q+r ≥ 1
  Q    countdownT      (L17b)  𝒞(a; 1^n X), a ≥ 1, n ≥ 3  → 𝒞(a+5q; 1^r X)
  P    branch_ge2T     (L17b)  𝒞(a; 11 X), a ≥ 1          → 𝒞(a+4; 0 X)
  F111 F111            (L17c)  𝒞(u+5; (10)^(d+1) 111 v)   → 𝒞(0; 1^(2u+2) (01)^(d+7) 0 v)
  F100 F100            (L17c)  𝒞(u+7; (10)^(c+1) 0 v)     → 𝒞(0; 1^(2u+2) (01)^7 1^(2c+3) v)
  F1100 F1100          (L17e)  𝒞(u+7; (10)^(d+7) 1100 v)  → 𝒞(0; 1^(2u+2) (01)^7 1^(2d+1) T v)
Leading 01 pairs of w are absorbed into a by tape equality. The stepper stops at the first state none of these covers.
Usage: python3 l17_ctx.py SECONDS
"""
import sys,time,json,gzip
sys.set_int_max_str_digits(0)

def canon(runs):
    out=[]
    for u,n in runs:
        if n==0: continue
        if out and out[-1][0]==u: out[-1]=(u,out[-1][1]+n); continue
        out.append((u,n))
        # a single 0 followed by ones is a 01 pair
        while len(out)>=2 and out[-2][0]=='0' and out[-1][0]=='1':
            (_,z),(_,o)=out[-2],out[-1]; out[-2:]=[('0',z-1),('01',1),('1',o-1)]
            out=[r for r in out if r[1]>0]
            # re-merge
            m=[]
            for r in out:
                if m and m[-1][0]==r[0]: m[-1]=(r[0],m[-1][1]+r[1])
                else: m.append(r)
            out=m
    while out and out[-1][0]=='0': out.pop()
    return out

def bits(w,k):
    s=''
    for u,n in w:
        if len(s)>=k: break
        s+=u*min(n,k)
    return (s+'0'*k)[:k]

def drop(w,k):
    w=list(w); i=0
    while k>0 and i<len(w):
        u,n=w[i]; L=len(u)
        full=min(n,k//L)
        if full: k-=full*L; n-=full
        if n and k:  # partial unit
            rest=u[k:]; k=0
            w[i:i+1]=[(rest,1),(u,n-1)] if n>1 else [(rest,1)]
            return canon(w[i:])
        if n==0: i+=1
        else: w[i]=(u,n); return canon(w[i:])
    return canon(w[i:])

T=[('01',7),('1',3)]

def step(a,w):
    """Return (rule, a', w') or (stop reason, a, w)."""
    if w and w[0][0]=='01': return 'absorb',a+w[0][1],w[1:]
    b=bits(w,2)
    if b=='00': return 'Z',0,canon([('1',2*a+4)]+drop(w,2))
    n=w[0][1]; X=w[1:]          # w = 1^n X, X starts with 0 or is blank
    if a==0:
        q,r=divmod(n,3); return 'EQ',1+5*q,canon([('1',r)]+X)
    if n>=3:
        q,r=divmod(n,3); return 'Q',a+5*q,canon([('1',r)]+X)
    if n==2: return 'P',a+4,canon([('0',1)]+X)
    # n == 1: 1 (01)^c Y = (10)^c 1 Y
    c=X[0][1] if X and X[0][0]=='01' else 0
    Y=X[1:] if c else X
    p='1'+bits(Y,3)
    if p[:3]=='111':
        if a<5 or c<1: return 'STOP-F111-guard',a,w
        return 'F111',0,canon([('1',2*a-8),('01',c+6),('0',1)]+drop(Y,2))
    if p[:3]=='100':
        if a<7: return 'STOP-F100-guard',a,w
        return 'F100',0,canon([('1',2*a-12),('01',7),('1',2*c+3)]+drop(Y,2))
    if p=='1100':
        if a<7 or c<7: return 'STOP-F1100-guard',a,w
        return 'F1100',0,canon([('1',2*a-12),('01',7),('1',2*c-13)]+T+drop(Y,3))
    return 'STOP-'+p,a,w

def depth(w): return sum(1 for u,_ in w if u=='01')

if __name__=='__main__':
    limit=float(sys.argv[1]); a,w=30066981019881,[('1',27)]
    from collections import Counter
    cnt=Counter(); n=0; maxd=0; ev=[]; t0=time.time()
    while time.time()-t0<limit:
        r,a2,w2=step(a,w)
        if r.startswith('STOP'): break
        if r=='F1100': ev.append((n,a.bit_length(),a%3,w[1][1] if len(w)>1 else 0))
        if r!='absorb': cnt[r]+=1; n+=1
        a,w=a2,w2; maxd=max(maxd,depth(w))
    print('rule steps',n,dict(cnt),'max pair blocks',maxd,'elapsed',round(time.time()-t0))
    print('F1100 events (step, a bits, a mod 3, c):',ev)
    print('final',r,'a bits',a.bit_length(),'a mod 3',a%3,'a mod 243',a%243,'w',[(u,m if m<10**6 else 'bits%d'%m.bit_length()) for u,m in w])
