import sys; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from machines import antihydra, a4, a9
def parse(s):
    T={}
    for i,st in enumerate(s.split('_')):
        for r in (0,1):
            x=st[3*r:3*r+3]
            T[(chr(65+i),r)]=None if x[0]=='-' else (int(x[0]),x[1],x[2])
    return T
def run(tm,N,match):
    T=parse(tm); tape={}; pos=0; st='A'; out=[]
    for n in range(N):
        m=match(st,tape,pos)
        if m is not None: out.append((n,m))
        tr=T[(st,tape.get(pos,0))]
        if tr is None: out.append((n,'HALT')); break
        w,d,ns=tr; tape[pos]=w; pos+=1 if d=='R' else -1; st=ns
    return out
def cells(tape,lo,hi): return [tape.get(i,0) for i in range(lo,hi)]
def ext(tape):
    ks=[k for k,v in tape.items() if v]; return (min(ks),max(ks)) if ks else (0,-1)
def m_antihydra(st,tape,pos):          # 0^inf 1^a 0 1^b E> 0^inf
    if st!='E': return None
    lo,hi=ext(tape)
    if hi>=pos: return None
    i=pos-1; b=0
    while tape.get(i,0)==1: b+=1; i-=1
    i-=1; a=0
    while tape.get(i,0)==1: a+=1; i-=1
    if lo<=i: return None
    return (a,b)
def m_a4(st,tape,pos):                 # 0^inf E> (10)^a 1^b 0^inf, b>=1
    if st!='E': return None
    lo,hi=ext(tape)
    if lo<pos or hi<pos: return None
    seg=cells(tape,pos,hi+1); b=0
    while seg and seg[-1]==1: seg.pop(); b+=1
    if b==0 or len(seg)%2 or any(seg[2*i:2*i+2]!=[1,0] for i in range(len(seg)//2)): return None
    return (len(seg)//2,b)
def m_a9(st,tape,pos):                 # 0^inf 1^(a+2) E> 1^(2b+2) 0 1^(2c+2) 0^inf
    if st!='E': return None
    lo,hi=ext(tape)
    left=cells(tape,lo,pos); right=cells(tape,pos,hi+1)
    if not left or any(x!=1 for x in left) or len(left)<2: return None
    if 0 not in right: return None
    k=right.index(0); r1,r2=right[:k],right[k+1:]
    if not r1 or not r2 or any(x!=1 for x in r1+r2) or len(r1)%2 or len(r2)%2: return None
    return (len(left)-2,len(r1)//2-1,len(r2)//2-1)
def macro(step,s0,K):
    s=s0; out=[s0]
    for _ in range(K):
        s=step(s)
        if s in('HALT','STUCK'): break
        out.append(s)
    return out
if __name__=="__main__":
  for name,tm,m,step,s0,N in (("Antihydra","1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA",m_antihydra,antihydra,(0,4),300000),
                               ("A.4","1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA",m_a4,a4,(0,3),300000),
                               ("A.9","1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD",m_a9,a9,(5,2,0),300000)):
      tr=run(tm,N,m); seq=[x for _,x in tr]
      mac=macro(step,s0,len(seq)+5)
      k=0
      while k<len(seq) and k<len(mac) and seq[k]==mac[k]: k+=1
      print(f"{name}: TM pattern matches in {N} raw steps: {len(seq)}; first match at raw step {tr[0][0] if tr else None}; agree with macro run for first {k}")
      if k<len(seq): print("   first disagreement:",seq[k:k+3],"vs",mac[k:k+3])
