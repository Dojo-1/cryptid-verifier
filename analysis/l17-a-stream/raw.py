"""Literal Python path and full-tape endpoint, no block acceleration."""
from paths import HERE
from reference import OPS
def replay(req):
    ones=set(req['ones']);q=req['q'];head=req['head'];reads=[]
    for done in range(req['limit']):
        b=int(head in ones);op=OPS[q][b]
        if op is None:break
        reads.append([q,head,b]);value,d,q=op
        if value:ones.add(head)
        else:ones.discard(head)
        head+=d
    else:done=req['limit']
    return dict(q=q,head=head,steps=done,halted=OPS[q][int(head in ones)] is None,ones=sorted(ones),reads=reads,read_min=min((x[1] for x in reads),default=None),read_max=max((x[1] for x in reads),default=None))
