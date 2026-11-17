"""Literal Python machine, with no counter acceleration."""
from paths import HERE
from reference import OPS
def replay(req):
    ones=set(req['ones']);q=req['q'];h=req['head'];reads=[]
    for t in range(req['limit']):
        b=int(h in ones);op=OPS[q][b]
        if op is None:break
        reads.append([q,h,b]);v,d,q=op
        if v:ones.add(h)
        else:ones.discard(h)
        h+=d
    else:t=req['limit']
    return dict(q=q,head=h,ones=sorted(ones),steps=t,halted=OPS[q][int(h in ones)] is None,reads=reads,read_min=min((x[1] for x in reads),default=None),read_max=max((x[1] for x in reads),default=None))
