import json,sys
def canon(a,b,k,s):
    if k==0 and s>0: b+=s; s=0
    return (a,b,k,s)
def step(st):
    a,b,k,s=st
    if a==0 and b>=1:
        q,r=divmod(b,3); return ('EC',dict(n=b,q=q,r=r,a2=1+5*q),canon(1+5*q,r,k,s))
    if a==0 and b==0:
        return ('N',dict(),canon(k,s,0,0))
    if b>=3:
        q,r=divmod(b,3); return ('CD',dict(q=q,r=r),canon(a+5*q,r,k,s))
    if b==2:
        if k==0: return ('B2',dict(),(0,2*a+12,0,0))
        return ('PZ',dict(),canon(0,2*a+13,k-1,s))
    if b==0:
        if k>0: return ('N',dict(),canon(a+k,s,0,0))
        return ('B0',dict(),(0,2*a+4,0,0))
    # b==1
    if k==0:
        assert a>=7; return ('R1',dict(),(0,2*a-12,7,3))
    if s==0:
        assert a>=7; return ('F100',dict(),canon(0,2*a-12,7,2*k+3))
    if s>=3:
        assert a>=5; return ('F111',dict(),canon(0,2*a-8,k+7,s-3))
    if s==2:
        assert a>=5; return ('F111r2',dict(),canon(0,2*a-8,k+6,0))
    return ('STOP-F1100',dict(),st)
if __name__=='__main__':
    st=(30066981019881,27,0,0); seq=[st]; rules=[]
    target=int(sys.argv[1]) if len(sys.argv)>1 else None
    for i in range(5000):
        r,info,nst=step(st); rules.append(r)
        if r.startswith('STOP'): print("stop",i,st); break
        st=nst; seq.append(st)
        if target and st[0]==target: print("hit GPT final at macro step",i+1,st[1:]); break
    from collections import Counter; print(Counter(rules))
    json.dump([list(map(str,x)) for x in seq],open('orbit2.json','w'))
