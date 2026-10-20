M='1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---'
T={}
for i,blk in enumerate(M.split('_')):
    for s in range(2):
        t=blk[3*s:3*s+3]
        T[(i,s)]=None if t[2]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
def cfg(a,b):  # C> (01)^a 1^b, head on first symbol of word, at position 0
    w=[0,1]*a+[1]*b
    return {i:v for i,v in enumerate(w) if v},0,2
def run_until_C(tape,h,st,limit):
    # run until next time state C is at a config of the form C(a,b) (exact), returning (a,b,steps,h)
    n=0
    while n<limit:
        tr=T[(st,tape.get(h,0))]
        if tr is None: return ('halt',n)
        w,d,ns=tr
        if w: tape[h]=1
        else: tape.pop(h,None)
        h+=d; st=ns; n+=1
        if st==2:
            r=decode(tape,h)
            if r: return (r,n,h)
    return ('timeout',n)
def decode(tape,h):
    if not tape: return (0,0)
    ks=sorted(tape); lo,hi=ks[0],ks[-1]
    if lo<h: return None
    w=[tape.get(i,0) for i in range(h,hi+1)]
    a=0;i=0
    while i+1<len(w) and w[i]==0 and w[i+1]==1: a+=1;i+=2
    rest=w[i:]
    if all(x==1 for x in rest): return (a,len(rest))
    return None
