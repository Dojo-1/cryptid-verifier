"""Frozen-grid endpoint, window, compiler and mutation checks."""
import hashlib,json,random,subprocess,itertools
from gd_paths import HERE
from gd_critic import Claims,single
from specification import request,want,agrees,equal_words
from gd_actor import row,Word
from backend import execute,set_budget

def compare(out,case):
    assert equal_words(out.word().parts,case['target']),(case['rule'],case['parameters'],'endpoint')
    assert (out.steps,out.shift)==(case['steps'],case['shift']),(case['rule'],case['parameters'],'time/head')

def campaign():
    rng=random.Random(21102026);claims=Claims(HERE/'claims.json');cases=[]
    def push(name,p):
        suffix=''.join(rng.choice('01') for _ in range(rng.randrange(0,16)))
        case=single(claims,name,p,suffix);compare(row(name,p,Word.literal(suffix)),case)
        assert case['steps']<=200000
        case['id']=len(cases);cases.append(case)
    qs=(1,2,3,5,12,25)
    for q,k,m in itertools.product(qs,(1,2,7),(0,1,2,3,5)):push('D0',dict(q=q,k=k,m=m,l=7,s=3))
    for q,k,m in itertools.product(qs,(1,2,5,9),(3,4,5,6,12)):push('D1',dict(q=q,k=k,m=m,l=7,s=3))
    for name in ('D12','D11'):
        for q,k in itertools.product(qs,(1,2,5,7,14,21)):push(name,dict(q=q,k=k,l=7,s=3))
    for q,k,m in itertools.product((0,1,2,3,5,12,25),(1,2,3,7,14),(0,1,2,3,8)):
        push('D2',dict(q=q,k=k,m=m,l=rng.choice((1,6,7,14)),s=rng.randrange(0,8)))
    for name in ('G0','G1','G2','G2k'):
        Q=(2,3,5,12,25) if name=='G1' else ((1,2,3,12,25) if name=='G0' else (0,1,2,12,25))
        for q in Q:
            for k in ((None,) if name=='G2k' else ((0,1,5,14) if name in ('G0','G1') else (1,2,7))):
                p=dict(q=q,l=rng.choice((1,2,7,14)),s=rng.randrange(0,8))
                if k is not None:p['k']=k
                push(name,p)
    for a,c,l in itertools.product((7,8,11,30),(5,6,7,14),(1,7,14)):push('JOIN',dict(a=a,c=c,l=l))
    for q,k,l in itertools.product((2,3,6,12),(5,6,14),(1,7)):push('D11join',dict(q=q,k=k,l=l,s=rng.choice((3,4,5,8))))
    for N,k in itertools.product((2,4,50),(1,7)):push('M0',dict(N=N,k=k,l=7,s=3))
    for N,m in itertools.product((2,4,50),(0,1)):push('K0',dict(N=N,m=m,l=7,s=3))
    return claims,cases

def main():
    claims,cases=campaign();set_budget(40000000,HERE/'raw-budget.jsonl');rng=random.Random(21102027)
    builds=[];metadata=[];runs=[];allactual=[]
    source=HERE.parent/'l17-hardening/raw_comparator.cpp'
    for label,options in (('O2',['-O2']),('O0',['-O0']),('UBSan',['-O1','-fsanitize=undefined','-fno-sanitize-recover=undefined'])):
        binary=HERE/('comparator-'+label)
        build=subprocess.run(['g++','-std=c++17',*options,str(source),'-o',str(binary)],check=True,capture_output=True,text=True)
        builds.append(dict(label=label,options=options,stderr=build.stderr,binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest()))
        selected=cases if label=='O2' else cases[::12]
        req=[request(c,c['id']) for c in selected];actual,meta=execute(binary,req,HERE/('raw-'+label+'.jsonl.gz'))
        for c,a in zip(selected,actual):
            assert agrees(a,want(c)),(label,c['id'],'literal mismatch')
            if c['read_bound'] is None:assert a['read_min'] is None
            else:
                lo,hi=c['read_bound'];assert lo<=a['read_min']<=a['read_max']<=hi,(label,c['id'],'read window',c['read_bound'],a['read_min'],a['read_max'])
        metadata.append(dict(label=label,**meta));runs.append(dict(label=label,cases=len(selected),all_passed=True))
        if label=='O2':allactual=actual
    # Random tape outside complete read bounds, independently of word encoding.
    requests=[];expected=[];kernel_specs=[('K7',-4,'1010101',0,0,0,-3,'0010101',7,(-4,1)),('K22',-12,'1010101001010',3,-4,2,-12,'1101010101010',22,(-11,-2))]
    for name,left,bits,inq,inh,outq,outh,outbits,steps,bound in kernel_specs:
        for seed in range(12):
            ins={left+i for i,b in enumerate(bits) if b=='1'};outs={left+i for i,b in enumerate(outbits) if b=='1'}
            for x in list(range(bound[0]-10,bound[0]))+list(range(bound[1]+1,bound[1]+11)):
                b=rng.randrange(2)
                if b:ins.add(x);outs.add(x)
                else:ins.discard(x);outs.discard(x)
            requests.append(dict(id=10000+len(requests),machine=claims.machine,q=inq,head=inh,limit=steps,ones=sorted(ins),trace=True))
            expected.append(dict(q=outq,head=outh,steps=steps,halted=False,ones=sorted(outs),read_bound=bound,name=name))
    # Whole-row exterior-noise checks; retain written words and every interior zero.
    selected=cases[::12]
    for c in selected:
        if c['read_bound'] is None:continue
        req=request(c,10000+len(requests));exp=want(c);ins=set(req['ones']);outs=set(exp['ones']);lo,hi=c['read_bound']
        assert all(lo<=x<=hi for x in ins.symmetric_difference(outs))
        for x in (lo-11,lo-1,hi+1,hi+9):
            b=rng.randrange(2)
            if b:ins.add(x);outs.add(x)
            else:ins.discard(x);outs.discard(x)
        req['ones']=sorted(ins);exp['ones']=sorted(outs);exp['read_bound']=(lo,hi);exp['name']=c['rule'];requests.append(req);expected.append(exp)
    win_actual,win_meta=execute(HERE/'comparator-O2',requests,HERE/'windows.jsonl.gz')
    for req,exp,act in zip(requests,expected,win_actual):
        assert agrees(act,exp),(req['id'],exp['name'],'exterior tape mismatch')
        lo,hi=exp['read_bound'];assert lo<=act['read_min']<=act['read_max']<=hi
    mutations=[]
    for key in ('time-minus-one','head-plus-one','wrong-state','missing-first-one','missing-context','drop-interior-zero'):
        killed=None
        for c,actual in zip(cases,allactual):
            pred=want(c)
            if key=='time-minus-one':pred['steps']-=1
            elif key=='head-plus-one':pred['head']+=1
            elif key=='wrong-state':pred['q']=1
            elif key=='missing-first-one':pred['ones']=pred['ones'][1:]
            elif key=='missing-context':
                if not c['suffix'] or '1' not in c['suffix']:continue
                pred['ones']=pred['ones'][:-1]
            else:
                if c['rule']!='D12':continue
                p=c['parameters'];pos=10*p['q']-6+2*(p['k']+6)
                # Remove the explicit gap: move every cell after it one place left.
                h=pred['head'];pred['ones']=[x-1 if x>h+pos else x for x in pred['ones']]
            if not agrees(actual,pred):killed=c['id'];break
        assert killed is not None,key
        mutations.append(dict(mutant=key,killed=True,witness_id=killed))
    (HERE/'cases.json').write_text(json.dumps(cases,indent=2)+'\n')
    (HERE/'window-cases.json').write_text(json.dumps(dict(requests=requests,expected=expected),indent=2)+'\n')
    report=dict(status='Bounded checks, not new Lean proof',claims_sha256=hashlib.sha256((HERE/'claims.json').read_bytes()).hexdigest(),comparator_source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),builds=builds,runs=runs,raw_metadata=metadata,window_checks=len(requests),window_metadata=win_meta,mutations=mutations,RET39='Arithmetic compositions only; minimum time exceeds200k; no raw run')
    (HERE/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(endpoint_cases=len(cases),compiler_runs=runs,window_checks=len(requests),mutants=len(mutations),total_fresh_transitions=sum(x['executed_defined_transitions'] for x in metadata)+win_meta['executed_defined_transitions']),indent=2))
if __name__=='__main__':main()
