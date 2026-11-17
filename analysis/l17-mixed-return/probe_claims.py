import json,itertools
from paths import HERE
from claims import RULES,TRANSFERS,KERNELS
from specification import materialize,integer,agrees
from raw import replay
def main():
    outcomes=[]
    for name,row in {**RULES,**TRANSFERS}.items():
        base={k:v[0] for k,v in row['guards'].items()}
        for delta in itertools.product(range(2),repeat=len(base)):
            p={k:v+d for (k,v),d in zip(base.items(),delta)};v='001101';src=''.join(w*n for w,n in materialize(row['source'],p,v));dst=''.join(w*n for w,n in materialize(row['target'],p,v));start=integer(row['source_start'],p);steps=integer(row['steps'],p)
            req=dict(q=row['source_q'],head=0,limit=steps,ones=[start+i for i,b in enumerate(src) if b=='1']);expected=dict(q=row['target_q'],head=integer(row['shift'],p),steps=steps,halted=False,ones=[start+i for i,b in enumerate(dst) if b=='1']);got=replay(req);ok=agrees(got,expected);outcomes.append(dict(rule=name,p=p,passed=ok))
            if not ok:
                (HERE/'failed-formula.json').write_text(json.dumps(dict(name=name,p=p,actual=got,expected=expected),indent=2)+'\n');raise AssertionError((name,p))
    kernels={}
    for name,(q,t,qq,h,lo,src,dst) in KERNELS.items():
        got=replay(dict(q=q,head=0,limit=t,ones=[lo+i for i,b in enumerate(src) if b=='1']));expected=dict(q=qq,head=h,steps=t,halted=False,ones=[lo+i for i,b in enumerate(dst) if b=='1'])
        if not agrees(got,expected):
            (HERE/'failed-kernel.json').write_text(json.dumps(dict(name=name,actual=got,expected=expected),indent=2)+'\n');raise AssertionError(name)
        assert got['read_min']>=lo and got['read_max']<lo+len(src),(name,got)
        kernels[name]=dict(q=q,steps=t,exit_q=qq,exit_head=h,lo=lo,hi=lo+len(src)-1,input=src,output=dst,reads=got['reads'],read_min=got['read_min'],read_max=got['read_max'])
    (HERE/'kernels.json').write_text(json.dumps(kernels,indent=2)+'\n');(HERE/'formula-probes.json').write_text(json.dumps(outcomes,indent=2)+'\n');print('Passed',len(outcomes),'formula checks and',len(kernels),'framed paths')
if __name__=='__main__':main()
