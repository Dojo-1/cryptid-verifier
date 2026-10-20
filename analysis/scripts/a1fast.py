import sys; sys.path.insert(0,'/tmp/zk/global')
from machines import a1
from collections import Counter
def fast(s):
    a,b,c,d=s
    if c>0: return (a,b+c,0,d)                      # c-drain
    if a==1 and b>0 and d>0: return (1,b+2*d,0,0)
    if d>0 and a>=3:
        t=min(a//3,d); return (a-3*t,b+2*t,0,d-t)    # a-drain
    return a1(s)
s=(0,0,0,0); res=Counter(); cyc=[]; n=0; dec=0
while dec<3000:
    t=fast(s); n+=1
    if t in('HALT','STUCK'): print(t,s); break
    if t[0]==0 and t[2]==0 and t[3]>=2:
        dec+=1; res[(t[3]-t[1]-2)%4]+=1
    if t[0]==2 and t[1]==0 and t[2]==0: cyc.append(t[3])
    s=t
    if max(s).bit_length()>2000: break
print("decision states (0,b,0,d):",dec," residues of d-b-2 mod 4:",dict(res))
print("cycle starts (2,0,0,D):",len(cyc)," D mod 4:",Counter(D%4 for D in cyc)," bits of last D:",cyc[-1].bit_length() if cyc else None)
print("first D:",cyc[:10])
