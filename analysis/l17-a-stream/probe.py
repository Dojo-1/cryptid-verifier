"""Exploratory left-stack return probes, retaining complete read paths."""
import json,gzip,time
from paths import HERE
from reference import OPS

def run(left,right,cap=20000,deadline=None):
    ones={i-len(left) for i,b in enumerate(left+right) if b=='1'};q=0;h=0;reads=[]
    for t in range(cap):
        if deadline is not None and time.monotonic()>deadline:reason='wall-cap';break
        bit=int(h in ones);op=OPS[q][bit]
        if op is None:reason='halt';break
        reads.append([q,h,bit]);value,d,q=op
        if value:ones.add(h)
        else:ones.discard(h)
        h+=d
        if q==2 and not any(x<h for x in ones):t+=1;reason='C-section';break
    else:t=cap;reason='cap'
    origin=min(h,min(ones,default=h));word=''.join(str(int(i in ones)) for i in range(origin,max(ones,default=origin)+1))
    return dict(steps=t,q=q,head=h,word_start=origin,word=word,reason=reason,ones=sorted(ones),read_min=min((x[1] for x in reads),default=None),read_max=max((x[1] for x in reads),default=None),reads=reads)

def main():
    rows=[];deadline=time.monotonic()+30
    for terminal in ('00','100','11'):
      for j in range(7):
        for n in (3,4,8):
          p,c=8,8;left='10'*p+'0'+'10'*c+'0'+'10'*n
          right='101'*j+terminal+'001101'
          r=run(left,right,deadline=deadline);r.update(p=p,c=c,n=n,j=j,terminal=terminal);rows.append(r)
          if r['reason']=='wall-cap':raise TimeoutError('Prospective exploratory wall cap')
          if n==3:print({k:r[k] for k in ('j','terminal','steps','head','reason','word')})
    with open(HERE/'probe-results.json.gz','wb') as f:
      with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as z:z.write((json.dumps(rows,separators=(',',':'))+'\n').encode())
if __name__=='__main__':main()
