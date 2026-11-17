"""Seeded matched comparisons against the frozen C++ literal machine."""
import itertools,json,random,subprocess,hashlib
from paths import HERE,BASE
from claims import MACHINE,RULES
from scanner import compile_stack,left_word
from specification import integer,materialize,agrees
from raw import replay
import backend

def word(terms,p,v):return ''.join(w*n for w,n in materialize(terms,p,v))
def record(label,source,target,steps,head,q=0,qq=2,start=0,target_start=None,bounds=None,metadata=None):
    return dict(label=label,source=source,target=target,steps=steps,head=head,q=q,qq=qq,start=start,target_start=head if target_start is None else target_start,bounds=bounds,metadata=metadata or {})
def return_case(name,p,v,embedded=False):
    row=RULES[name];src=word(row['source'],p,v);dst=word(row['target'],p,v);steps=integer(row['steps'],p);head=start=integer(row['shift'],p)
    if embedded:
        a=p['p']+1;c=p['c'];j=integer(row['j'],p)
        src='01'*a+'10'*c+'1101'+'101'*j+row['terminal']+v
        steps+=2*a+2*c+28;start=0;head=-2;target_start=-2;q=2
        bounds=[-2,2*a+2*c+4+3*j+len(row['terminal'])-1]
    else:target_start=start;q=0;bounds=[integer(x,p) for x in row['read_bounds']]
    return record(name+('-embedded' if embedded else ''),src,dst,steps,head,q=q,start=start,target_start=target_start,bounds=bounds,metadata=dict(rule=name,p=p,v=v,embedded=embedded))

def generate():
    rng=random.Random(17112026);out=[]
    for name,row in RULES.items():
        base={k:v[0] for k,v in row['guards'].items()}
        for delta in itertools.product(range(3),repeat=len(base)):
            p={k:v+d for (k,v),d in zip(base.items(),delta)}
            for v in ('','1','001101'):out.append(return_case(name,p,v))
        for _ in range(16):
            p={k:v+rng.randrange(240 if k!='h' else 96) for k,v in base.items()};v=''.join(rng.choice('01') for _ in range(31));out.append(return_case(name,p,v))
        for _ in range(8):
            p={k:v+rng.randrange(16) for k,v in base.items()};v=''.join(rng.choice('01') for _ in range(17));out.append(return_case(name,p,v,True))
    tokensets=[list(t) for n in range(4) for t in itertools.product(('01','101'),repeat=n)]
    tokensets += [[rng.choice(('01','101')) for _ in range(rng.randrange(97))] for _ in range(128)]
    for i,tokens in enumerate(tokensets):
        runs=[rng.randrange(12),rng.randrange(1,16),rng.randrange(3,16)];v=rng.choice(('00','100','11'))+''.join(rng.choice('01') for _ in range(21))
        left=left_word(runs);new,t,d=compile_stack(runs,tokens);source=left+''.join(tokens)+v;target=left_word(new)+v
        out.append(record('scanner',source,target,t,d,q=0,qq=0,start=-len(left),target_start=-len(left),bounds=[-len(left),d-1] if t else None,metadata=dict(runs=runs,tokens=tokens,v=v)))
    kernels=json.loads((HERE/'kernels.json').read_text())
    for name,row in kernels.items():
        for _ in range(12):
            lo=row['lo'];pad=''.join(rng.choice('01') for _ in range(13));v=''.join(rng.choice('01') for _ in range(13))
            src=pad+row['input']+v;dst=pad+row['output']+v
            out.append(record('kernel:'+name,src,dst,row['steps'],row['exit_head'],q=row['q'],qq=row['exit_q'],start=lo-13,target_start=lo-13,bounds=[row['read_min'],row['read_max']],metadata=dict(kernel=name)))
    assert len(out)<=1200
    return out

def request(case,i):
    return dict(id=i,machine=MACHINE,q=case['q'],head=0,limit=case['steps'],trace=case['steps']<=1000,ones=[case['start']+j for j,b in enumerate(case['source']) if b=='1'])
def want(case):
    return dict(q=case['qq'],head=case['head'],steps=case['steps'],halted=False,ones=[case['target_start']+j for j,b in enumerate(case['target']) if b=='1'])

def main():
    (HERE/'claims.json').write_text(json.dumps(dict(machine=MACHINE,status='Analytic compositions, not Lean theorems',rules=RULES),indent=2)+'\n')
    (HERE/'build').mkdir(exist_ok=True);binary=HERE/'build/raw-o2'
    subprocess.run(['g++','-std=c++17','-O2',str(BASE/'l17-hardening/raw_comparator.cpp'),'-o',str(binary)],check=True)
    cases=generate();reqs=[request(c,i) for i,c in enumerate(cases)]
    assert max(x['limit'] for x in reqs)<=200000
    ledger=HERE/'raw-budget.jsonl';spent=sum(json.loads(s)['executed_defined_transitions'] for s in ledger.read_text().splitlines()) if ledger.exists() else 0
    backend.set_budget(20000000-spent,ledger)
    actual,meta=backend.execute(binary,reqs,HERE/'raw-results.jsonl.gz')
    counts={};traces=0;total=0
    for c,req,r in zip(cases,reqs,actual):
        expected=want(c);py=replay(req);total+=py['steps']
        assert agrees(r,expected) and agrees(py,expected),(c,r,expected)
        if c['bounds'] is not None:assert r['read_min']>=c['bounds'][0] and r['read_max']<=c['bounds'][1],(c,r)
        if req['trace']:assert r['reads']==py['reads'];traces+=1
        counts[c['label']]=counts.get(c['label'],0)+1
    (HERE/'cases.json').write_text(json.dumps(cases,separators=(',',':'))+'\n')
    out=dict(passed=True,cases=len(cases),by_kind=counts,all_python_endpoints=len(cases),full_cpp_python_traces=traces,python_defined_transitions=total,maximum_steps=max(c['steps'] for c in cases),raw_metadata=meta,claims_sha256=hashlib.sha256((HERE/'claims.json').read_bytes()).hexdigest())
    (HERE/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
