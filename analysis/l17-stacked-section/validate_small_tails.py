"""Fixed-window proofs and bounded independent checks for six short-tail cases."""
from __future__ import annotations
from datetime import datetime,timezone
import json
from pathlib import Path
import random
from reference import OPS
from rules import core1100_small
from validate import check
from words import Word

ROOT=Path(__file__).resolve().parent
KERNELS=[
    {'c':1,'m':3,'steps':36,'output':'11'+'01'*2+'1'*6,'read_bounds':[-5,5]},
    {'c':2,'m':7,'steps':118,'output':'11'+'01'*10,'read_bounds':[-13,7]},
    {'c':4,'m':3,'steps':70,'output':'11'+'01'+'1'+'01'*5+'111','read_bounds':[-5,11]},
    {'c':5,'m':8,'steps':164,'output':'11'+'01'*14,'read_bounds':[-15,13]},
    {'c':6,'m':8,'steps':126,'output':'11'+'01'*6+'0'+'01'*7+'111','read_bounds':[-15,15]},
]


def witness(k):
    tape={k['origin']+i:1 for i,b in enumerate(k['input']) if b=='1'}
    q,h=k['q'],k['head'];reads=[]
    for _ in range(k['steps']):
        reads.append([chr(q+65),h,tape.get(h,0)])
        assert k['read_bounds'][0]<=h<=k['read_bounds'][1]
        v,m,q=OPS[q][tape.get(h,0)]
        if v:tape[h]=1
        else:tape.pop(h,None)
        h+=m
    want={k['origin']+i:1 for i,b in enumerate(k['output']) if b=='1'}
    assert (q,h,tape)==(k['target_q'],k['target_head'],want)
    return dict(k,reads=reads)


def kernels():
    records=[]
    for k in KERNELS:
        m,c=k['m'],k['c']
        records.append(witness(dict(k,origin=-2*m,input='10'*m+'10'*c+'1100',
                                    q=0,head=0,target_q=2,target_head=-2*m)))
    records.append(witness({'name':'c3-right','origin':-4,'input':'10'*5+'1100',
        'q':0,'head':0,'steps':65,'output':'10'*5+'1111','target_q':3,'target_head':-5,'read_bounds':[-4,9]}))
    records.append(witness({'name':'D-left-finish','origin':-4,'input':'0000010',
        'q':3,'head':0,'steps':10,'output':'0101010','target_q':2,'target_head':-4,'read_bounds':[-3,2]}))
    return records


def main():
    rows=[];larger=[];max_steps=0
    for a in range(7,121):
        for c in range(1,7):
            out=core1100_small(a,c)
            check(Word((('01',a),('10',c),('11',1))),out)
            rows.append({'a':a,'c':c,'steps':out.steps,'shift':out.shift})
            max_steps=max(max_steps,out.steps)
    rng=random.Random(20261022)
    for _ in range(64):
        a=rng.randint(1000,10000);c=rng.randint(1,6)
        suffix=''.join(rng.choice('01') for _ in range(rng.randrange(41)))
        v=Word.literal(suffix);out=core1100_small(a,c,v)
        check(Word((('01',a),('10',c),('1100',1))+v.parts),out)
        larger.append({'a':a,'c':c,'suffix':suffix,'steps':out.steps,'shift':out.shift})
        max_steps=max(max_steps,out.steps)
    output={'recorded_at_utc':datetime.now(timezone.utc).isoformat(),
            'status':'Finite raw checks and fixed-window witnesses; universal sweep derivation is in DERIVATION.md. No Lean build.',
            'grid':rows,'larger_arbitrary_suffix_checks':larger,'kernel_witnesses':kernels(),
            'maximum_reference_transitions':max_steps,'reference_limit':200000,
            'historical_grid_gaps_now_covered':'The 48 c<7,r=1 cases left explicit in tail-family-checks.json are covered by these additional lemmas.'}
    (ROOT/'small-tail-checks.json').write_text(json.dumps(output,indent=2)+'\n')
    print('Short-tail grid:',len(rows),'larger suffix checks:',len(larger),'fixed kernels:',len(output['kernel_witnesses']))
    print('Maximum reference transitions:',max_steps,'limit 200000')


if __name__=='__main__':main()
