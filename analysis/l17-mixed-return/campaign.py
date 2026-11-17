"""Matched bounded endpoint campaign for small-width returns and transfers."""
import json,random,itertools,subprocess,hashlib
from paths import HERE,BASE
from claims import MACHINE,RULES,TRANSFERS
from specification import materialize,integer,agrees
from raw import replay
import backend

def word(terms,p,v):return ''.join(w*n for w,n in materialize(terms,p,v))
def case(name,p,v,pad='',extra=''):
    row={**RULES,**TRANSFERS}[name];src=word(row['source'],p,v);dst=word(row['target'],p,v);start=integer(row['source_start'],p);target_start=integer(row['target_start'],p)
    return dict(label=name,q=row['source_q'],qq=row['target_q'],source=pad+src+extra,target=pad+dst+extra,steps=integer(row['steps'],p),head=integer(row['shift'],p),start=start-len(pad),target_start=target_start-len(pad),bounds=[integer(z,p) for z in row['read_bounds']],metadata=dict(rule=name,p=p,v=v,pad=pad,extra=extra))
def mixed_case(p,c,v,embedded=False):
    prefix='01'+'101'+'01'+'101'
    target='1'*(2*p-6)+'01'*(c+12)+'11'+v
    if embedded:
        a=p+1;source='01'*a+'10'*c+'1101'+prefix+'00'+v;steps=4*a+6*c+152;start=0;head=target_start=-2;q=2
        bounds=[-2,2*a+2*c+15]
    else:
        source='10'*p+'0'+'10'*c+'0'+'10'*3+prefix+'00'+v;steps=2*p+4*c+126;start=head=target_start=-2*p-2*c-8;q=0;bounds=[start,11]
    return dict(label='mixed-original-C' if embedded else 'mixed-A',q=q,qq=2,source=source,target=target,steps=steps,head=head,start=start,target_start=target_start,bounds=bounds,metadata=dict(p=p,c=c,v=v,embedded=embedded))
def request(c,i):
    return dict(id=i,machine=MACHINE,q=c['q'],head=0,limit=c['steps'],trace=c['steps']<=1000,ones=[c['start']+j for j,b in enumerate(c['source']) if b=='1'])
def want(c):
    return dict(q=c['qq'],head=c['head'],steps=c['steps'],halted=False,ones=[c['target_start']+j for j,b in enumerate(c['target']) if b=='1'])
def generate():
    rng=random.Random(17112027);out=[]
    for name,row in {**RULES,**TRANSFERS}.items():
        base={k:v[0] for k,v in row['guards'].items()}
        def add(p,v):
            pad=extra=''
            if row.get('framed'):
                pad=''.join(rng.choice('01') for _ in range(13));extra=''.join(rng.choice('01') for _ in range(13))
            out.append(case(name,p,v,pad,extra))
        for delta in itertools.product(range(2),repeat=len(base)):
            p={k:v+d for (k,v),d in zip(base.items(),delta)}
            for v in ('','1','001101'):add(p,v)
        for _ in range(8):
            p={k:v+rng.randrange(180) for k,v in base.items()};v=''.join(rng.choice('01') for _ in range(31));add(p,v)
    kernels=json.loads((HERE/'kernels.json').read_text())
    for name,row in kernels.items():
        for _ in range(8):
            pad=''.join(rng.choice('01') for _ in range(13));extra=''.join(rng.choice('01') for _ in range(13))
            out.append(dict(label='kernel:'+name,q=row['q'],qq=row['exit_q'],source=pad+row['input']+extra,target=pad+row['output']+extra,steps=row['steps'],head=row['exit_head'],start=row['lo']-13,target_start=row['lo']-13,bounds=[row['read_min'],row['read_max']],metadata=dict(kernel=name)))
    for embedded in (False,True):
        for p,c in itertools.product((6,7),repeat=2):
            for v in ('','1','001101'):out.append(mixed_case(p,c,v,embedded))
        for _ in range(8):out.append(mixed_case(6+rng.randrange(80),7+rng.randrange(80),''.join(rng.choice('01') for _ in range(19)),embedded))
    assert len(out)<=1200
    return out
def budget():
    ledger=HERE/'raw-budget.jsonl';spent=sum(json.loads(x)['executed_defined_transitions'] for x in ledger.read_text().splitlines()) if ledger.exists() else 0
    backend.set_budget(20000000-spent,ledger)
def main():
    (HERE/'claims.json').write_text(json.dumps(dict(machine=MACHINE,status='Conditional mathematical compositions,not Lean theorems',rules={**RULES,**TRANSFERS}),indent=2)+'\n')
    (HERE/'build').mkdir(exist_ok=True);binary=HERE/'build/raw-o2';subprocess.run(['g++','-std=c++17','-O2',str(BASE/'l17-hardening/raw_comparator.cpp'),'-o',str(binary)],check=True)
    cases=generate();requests=[request(c,i) for i,c in enumerate(cases)];assert max(r['limit'] for r in requests)<=200000;budget()
    actual,meta=backend.execute(binary,requests,HERE/'raw-results.jsonl.gz');counts={};traces=0
    for c,req,r in zip(cases,requests,actual):
        w=want(c);py=replay(req)
        if not (agrees(r,w) and agrees(py,w) and r['read_min']>=c['bounds'][0] and r['read_max']<=c['bounds'][1]):
            (HERE/'failed-case.json').write_text(json.dumps(dict(case=c,actual=r,expected=w),indent=2)+'\n');raise AssertionError(c['label'])
        if req['trace']:assert r['reads']==py['reads'];traces+=1
        counts[c['label']]=counts.get(c['label'],0)+1
    (HERE/'cases.json').write_text(json.dumps(cases,separators=(',',':'))+'\n')
    out=dict(passed=True,cases=len(cases),by_kind=counts,all_python_endpoints=len(cases),full_trace_comparisons=traces,maximum_steps=max(c['steps'] for c in cases),raw_metadata=meta,claims_sha256=hashlib.sha256((HERE/'claims.json').read_bytes()).hexdigest())
    (HERE/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
