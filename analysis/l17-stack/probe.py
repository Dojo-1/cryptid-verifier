"""Literal sparse exploration of the currently unhandled 1101 prefix."""
from pathlib import Path
import sys,json
from paths import HERE,FRONTIER
sys.path.insert(0,str(FRONTIER))
from reference import OPS

CASES=[(8,8,d,r) for d in (1,2,7,8) for r in (0,1,2,3)]


def run(a,c,d,r):
    word='01'*a+'10'*c+'1101'+'01'*d+'1'*r
    ones={i for i,b in enumerate(word) if b=='1'};q=2;head=0
    common=2+2*(a+1)+11+2*c
    trace=[]
    for t in range(200000):
        if t>=common and q==2 and head<=0 and not any(i<head for i in ones):
            end=max(ones,default=head-1)
            out=''.join('1' if i in ones else '0' for i in range(head,end+1))
            return {'a':a,'c':c,'d':d,'r':r,'steps':t,'head':head,'word':out,'trace_window':trace}
        op=OPS[q][int(head in ones)]
        if op is None:return {'a':a,'c':c,'d':d,'r':r,'halted':True,'steps':t,'head':head}
        if common<=t<common+80:trace.append([t,'ABCDEF'[q],head,int(head in ones)])
        v,m,q=op
        if v:ones.add(head)
        else:ones.discard(head)
        head+=m
    return {'a':a,'c':c,'d':d,'r':r,'budget':200000,'head':head,'state':q}


if __name__=='__main__':
    report={'campaign':'Exploratory: 16 of 128 registered probes; cap 200000 each; no fitted rule assumed.',
            'cases':[run(*x) for x in CASES]}
    (HERE/'probe1101.json').write_text(json.dumps(report,indent=2)+'\n')
    for row in report['cases']:print({k:v for k,v in row.items() if k!='trace_window'})
