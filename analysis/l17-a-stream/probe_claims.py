"""First literal endpoint cross-check of the frozen candidate formulas."""
import json
from paths import HERE
from claims import RULES,KERNELS
from specification import integer,materialize,expand,agrees
from raw import replay
def main():
    results=[]
    for name,row in RULES.items():
        p={k:v[0] for k,v in row['guards'].items()}
        for h in range(7):
            if 'h' in p:p['h']=h
            source=expand(materialize(row['source'],p,'001101'));target=expand(materialize(row['target'],p,'001101'));start=integer(row['source_start'],p)
            req=dict(q=0,head=0,limit=integer(row['steps'],p),ones=[start+i for i,b in enumerate(source) if b=='1'])
            expected=dict(q=2,head=integer(row['shift'],p),steps=req['limit'],halted=False,ones=[start+i for i,b in enumerate(target) if b=='1'])
            got=replay(req);ok=agrees(got,expected);results.append(dict(rule=name,p=dict(p),passed=ok))
            if not ok:print(name,p,'got',got,'expected',expected);raise AssertionError(name)
    kernels={}
    for name,(q,t,qq,h,lo,src,dst) in KERNELS.items():
        req=dict(q=q,head=0,limit=t,ones=[lo+i for i,b in enumerate(src) if b=='1']);got=replay(req)
        want=dict(q=qq,head=h,steps=t,halted=False,ones=[lo+i for i,b in enumerate(dst) if b=='1'])
        assert agrees(got,want),(name,got,want)
        assert got['read_min']>=lo and got['read_max']<lo+len(src)
        kernels[name]=dict(q=q,steps=t,exit_q=qq,exit_head=h,lo=lo,hi=lo+len(src)-1,input=src,output=dst,reads=got['reads'],read_min=got['read_min'],read_max=got['read_max'])
    (HERE/'kernels.json').write_text(json.dumps(kernels,indent=2)+'\n')
    (HERE/'formula-probe-results.json').write_text(json.dumps(results,indent=2)+'\n');print('passed',len(results),'formula probes and',len(kernels),'fixed paths')
if __name__=='__main__':main()
