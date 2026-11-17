"""Stop a deterministic local path before its first unknown read."""
import json
from paths import HERE
from reference import OPS
def trace(r,m=9):
    lo=-2*r-1;hi=m;src='00'+'10'*r+'1'*m
    tape={lo+i:int(b) for i,b in enumerate(src)};q=2;h=0;reads=[]
    for t in range(500):
        if h not in tape:reason='unknown-read';break
        b=tape[h];op=OPS[q][b]
        if op is None:reason='halt';break
        reads.append([q,h,b]);v,d,q=op;tape[h]=v;h+=d
    else:t=500;reason='cap'
    return dict(r=r,m=m,lo=lo,hi=hi,input=src,q=q,head=h,steps=t,reason=reason,output=''.join(str(tape[i]) for i in range(lo,hi+1)),reads=reads)
def main():
    rows=[trace(r,m) for r in range(1,6) for m in (3,9)]
    (HERE/'local-probes.json').write_text(json.dumps(rows,indent=2)+'\n')
    for x in rows:print({k:v for k,v in x.items() if k!='reads'})
if __name__=='__main__':main()
