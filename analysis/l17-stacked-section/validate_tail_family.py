"""Separate, bounded validation of the one-tail formulas and stack-producing rule."""
from __future__ import annotations
from collections import Counter
from datetime import datetime, timezone
import json
from pathlib import Path
import random
from reference import OPS
from rules import Endpoint, core100, core111, core1100
from validate import check
from words import Word

ROOT=Path(__file__).resolve().parent


def one_tail(a,b,c,r):
    """Endpoint for C(a,b) . (01)^c 1^r; explicitly leaves small r=1 unsupported."""
    if min(a,b,c,r)<0:raise ValueError('nonnegative parameters required')
    if b==0:
        return Endpoint(a+c,Word((('1',r),)),0,0,'merge-tail')
    if b==2 and a>=1 and c>=1:
        return Endpoint(0,Word((('1',2*a+13),('01',c-1),('1',r))),10*a+45,-9,'two-ones-tail')
    if b==1 and c>=1:
        if r==0 and a>=7:return core100(a,c)
        if r==1 and a>=7 and c>=7:return core1100(a,c)
        if r==2 and a>=5:return core111(a,c)
        if r>=3 and a>=5:
            return Endpoint(0,Word((('1',2*a-8),('01',c+7),('1',r-3))),4*a+6*c+38,-2,'three-or-more-tail-ones')
    return None


def kernel60():
    k={'name':'segment60','origin':-16,'input':'10'*8+'100','q':0,'head':0,
       'steps':60,'output':'11'+'01'*7+'111','target_q':2,'target_head':-16,'read_bounds':[-15,2]}
    tape={k['origin']+i:1 for i,b in enumerate(k['input']) if b=='1'}
    q,h=k['q'],k['head'];reads=[]
    for _ in range(60):
        reads.append([chr(q+65),h,tape.get(h,0)])
        assert -15<=h<=2
        v,m,q=OPS[q][tape.get(h,0)]
        if v:tape[h]=1
        else:tape.pop(h,None)
        h+=m
    expected={k['origin']+i:1 for i,b in enumerate(k['output']) if b=='1'}
    assert (q,h,tape)==(2,-16,expected)
    return dict(k,reads=reads)


def tail_shape(a,parts):
    """Recognize one tail or its P-to-Z bridge by exact prefix operations."""
    w=Word(tuple(map(tuple,parts)))
    p=w.periodic_prefix_length('01')//2;a+=p;w=w.drop(2*p)
    bridge=False
    if w.size() and w.prefix(1)=='0':bridge=True;w=w.drop(1)
    b=w.periodic_prefix_length('1');w=w.drop(b)
    c=w.periodic_prefix_length('01')//2;w=w.drop(2*c)
    r=w.periodic_prefix_length('1');w=w.drop(r)
    return {'a':a,'b':b,'c':c,'r':r,'bridge':bridge,'unparsed':w.to_json()}


def main():
    rows=[];unsupported=[];counts=Counter();max_steps=0
    for a in range(7,15):
        for c in range(1,9):
            for r in range(9):
                for b in (0,1,2):
                    target=one_tail(a,b,c,r)
                    if target is None:
                        unsupported.append({'a':a,'b':b,'c':c,'r':r});continue
                    source=Word((('01',a),('1',b),('01',c),('1',r)))
                    check(source,target);counts[target.rule]+=1
                    rows.append({'a':a,'b':b,'c':c,'r':r,'rule':target.rule,'steps':target.steps,'shift':target.shift})
                    max_steps=max(max_steps,target.steps)
    rng=random.Random(20261021);contexts=[];larger=[]
    for size,n,amin,amax,cmin,cmax in (('context',256,7,64,7,32),('larger',64,1000,20000,100,2000)):
        for _ in range(n):
            a=rng.randint(amin,amax);c=rng.randint(cmin,cmax)
            suffix=''.join(rng.choice('01') for _ in range(rng.randrange(41)))
            v=Word.literal(suffix);source=Word((('01',a),('10',c),('1100',1))+v.parts)
            target=core1100(a,c,v);info=check(source,target)
            row={'a':a,'c':c,'suffix':suffix,'steps':target.steps,'block_checks':info}
            (contexts if size=='context' else larger).append(row);max_steps=max(max_steps,target.steps)
    witness=one_tail(7,1,8,1)
    trace=json.loads((ROOT/'symbolic-extension.json').read_text())['trace']
    observed=Counter();bad=[]
    for i,row in enumerate(trace['records']):
        shape=tail_shape(row['a_before'],row['tail_before'])
        if shape['unparsed']:bad.append({'index':i,'shape':shape})
        observed['bridge' if shape['bridge'] else 'one-tail']+=1
    output={'recorded_at_utc':datetime.now(timezone.utc).isoformat(),
            'status':'Finite full-tape checks. The universal interpretation is derived in DERIVATION.md, not Lean verified here.',
            'grid':rows,'explicit_unsupported_grid_cases':unsupported,'rule_counts':dict(counts),
            'new_core_arbitrary_suffix_checks':contexts,'new_core_larger_checks':larger,
            'maximum_reference_transitions':max_steps,'reference_limit':200000,
            'kernel_witness':kernel60(),
            'one_tail_nonclosure_witness':{'source':'C(7,1) . (01)^8 1','target':witness.tail.to_json(),'steps':witness.steps,'shift':witness.shift},
            'bounded_2000_trace_shape_check':{'counts':dict(observed),'unparsed':bad,
                'interpretation':'All frozen trace inputs fit the one-tail shape or its single-zero P-to-Z bridge. This is a finite observation, not reachable closure.'},
            'new_halting_or_nonhalting_theorems':0}
    (ROOT/'tail-family-checks.json').write_text(json.dumps(output,indent=2)+'\n')
    print('One-tail endpoint grid:',len(rows),'explicit unsupported:',len(unsupported),dict(counts))
    print('New stack-producing core:',len(contexts),'arbitrary suffixes,',len(larger),'larger checks')
    print('Maximum reference transitions:',max_steps,'limit 200000')
    print('Frozen 2000-rewrite trace shapes:',dict(observed),'unparsed:',len(bad))
    print('K60 complete path and two-tail witness checked with exact full tape endpoints.')


if __name__=='__main__':main()
